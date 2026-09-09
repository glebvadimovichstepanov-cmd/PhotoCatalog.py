"""Qt desktop interface; all filesystem work runs outside the GUI thread."""

from __future__ import annotations

import os
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path
from threading import Event

from PySide6.QtCore import QObject, Qt, QThread, QUrl, Signal, Slot
from PySide6.QtGui import (
    QCloseEvent,
    QColor,
    QDesktopServices,
    QFont,
    QIcon,
    QPainter,
    QPixmap,
)
from PySide6.QtWidgets import (
    QApplication,
    QCheckBox,
    QFileDialog,
    QFrame,
    QGridLayout,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QLineEdit,
    QMainWindow,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QScrollArea,
    QSpinBox,
    QTableWidget,
    QTableWidgetItem,
    QVBoxLayout,
    QWidget,
)

from . import __version__
from .catalog import Config, Record, Summary, run
from .storage import validate_roots, write_report

STATUS = {
    "copied": "Скопирован",
    "duplicate": "Уже в каталоге",
    "planned": "В плане",
    "skipped": "Пропущен",
    "error": "Ошибка",
}
COLORS = {
    "copied": "#107c68",
    "duplicate": "#66758a",
    "planned": "#366aca",
    "skipped": "#99721e",
    "error": "#c84747",
}
STYLE = """
QMainWindow, QWidget#workspace { background: #f4f6fa; color: #192940; }
QWidget { font-family: 'Segoe UI'; font-size: 13px; color: #192940; }
QFrame#sidebar { background: #122339; border: none; }
QFrame#sidebar QLabel { color: #aabbd0; background: transparent; }
QFrame#sidebar QLabel#brand { color: white; font-size: 23px; font-weight: 700; }
QLabel#eyebrow { color: #55857a; font-size: 11px; font-weight: 700; }
QLabel#title { color: #14263f; font-size: 29px; font-weight: 700; }
QLabel#subtitle { color: #6f7d8f; font-size: 13px; }
QFrame#card { background: white; border: 1px solid #e1e7ef; border-radius: 12px; }
QFrame#card QLabel { background: transparent; border: none; }
QLabel#section { font-size: 15px; font-weight: 600; }
QLabel#metric { font-size: 26px; font-weight: 700; color: #152c44; }
QLabel#badge { background: #e0f4ed; color: #167c62; border-radius: 12px; padding: 6px 12px; }
QLineEdit { background: #f8fafc; border: 1px solid #dce4ed; border-radius: 7px; padding: 11px; }
QLineEdit:focus { border: 1px solid #268974; background: white; }
QPushButton { background: white; border: 1px solid #d9e2ec; border-radius: 7px;
              padding: 10px 17px; font-weight: 600; }
QPushButton:hover { background: #edf4f7; border-color: #b6c8d8; }
QPushButton#primary { background: #16846d; color: white; border: 1px solid #16846d; }
QPushButton#primary:hover { background: #106e5b; }
QPushButton#stop { color: #bc4949; background: #fff3f3; border-color: #f0caca; }
QPushButton:disabled { color: #9aa7b6; background: #eef1f5; border-color: #e1e5eb; }
QSpinBox { background: #f8fafc; border: 1px solid #dce4ed; border-radius: 5px; padding: 6px; }
QCheckBox { spacing: 8px; }
QCheckBox::indicator { width: 17px; height: 17px; border: 1px solid #b9c8d7;
                      border-radius: 4px; background: white; }
QCheckBox::indicator:checked { background: #16846d; border-color: #16846d; image: none; }
QProgressBar { border: none; background: #e8eef3; border-radius: 4px; height: 7px; }
QProgressBar::chunk { background: #16846d; border-radius: 4px; }
QTableWidget { border: none; background: white; gridline-color: #eef2f7;
               selection-background-color: #e4f3ed; selection-color: #182c43; }
QHeaderView::section { background: #f7f9fc; border: none; border-bottom: 1px solid #e5eaf1;
                      padding: 9px; color: #728198; font-weight: 600; }
QScrollBar:vertical { background: #f7f9fc; width: 9px; border: none; }
QScrollBar::handle:vertical { background: #c7d3df; border-radius: 4px; min-height: 24px; }
QToolTip { background: #122339; color: white; padding: 8px; border: none; }
"""


def application_icon() -> QIcon:
    pixmap = QPixmap(64, 64)
    pixmap.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    painter.setPen(Qt.PenStyle.NoPen)
    painter.setBrush(QColor("#16846d"))
    painter.drawRoundedRect(0, 0, 64, 64, 15, 15)
    painter.setBrush(QColor("#ffffff"))
    painter.drawRoundedRect(13, 19, 38, 29, 5, 5)
    painter.drawRoundedRect(21, 14, 15, 10, 3, 3)
    painter.setBrush(QColor("#16846d"))
    painter.drawEllipse(24, 24, 17, 17)
    painter.setBrush(QColor("#ffffff"))
    painter.drawEllipse(28, 28, 9, 9)
    painter.end()
    return QIcon(pixmap)


def bundled_library() -> str | None:
    if getattr(sys, "frozen", False):
        library = Path(sys._MEIPASS) / "pymediainfo" / "MediaInfo.dll"
        if not library.is_file():
            raise FileNotFoundError("Встроенная MediaInfo.dll не найдена")
        return str(library)
    return os.environ.get("PHOTOCATALOG_MEDIAINFO_LIB")


class Worker(QObject):
    record = Signal(object)
    completed = Signal(object)
    failed = Signal(str)

    def __init__(self, config: Config, cancellation: Event) -> None:
        super().__init__()
        self.config = config
        self.cancellation = cancellation

    @Slot()
    def execute(self) -> None:
        try:
            summary = run(
                self.config, progress=self.record.emit, cancel=self.cancellation
            )
            self.completed.emit(summary)
        except Exception as exc:
            self.failed.emit(str(exc))


class Window(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("PhotoCatalog — порядок в воспоминаниях")
        self.setWindowIcon(application_icon())
        self.resize(1220, 960)
        self.setMinimumSize(1060, 740)
        self.setStyleSheet(STYLE)
        self.thread: QThread | None = None
        self.worker: Worker | None = None
        self.cancel_event = Event()
        self.summary: Summary | None = None
        self.counts: Counter[str] = Counter()
        self.closing = False
        self.dry_run = False
        self.last_destination: Path | None = None

        widget = QWidget()
        widget.setObjectName("workspace")
        self.setCentralWidget(widget)
        layout = QHBoxLayout(widget)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.addWidget(self.sidebar())

        content = QWidget()
        content.setObjectName("workspace")
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setWidget(content)
        layout.addWidget(scroll, 1)
        column = QVBoxLayout(content)
        column.setContentsMargins(30, 24, 30, 20)
        column.setSpacing(16)
        header = QHBoxLayout()
        titles = QVBoxLayout()
        titles.setSpacing(5)
        titles.addWidget(self.label("ЛИЧНАЯ МЕДИАТЕКА", "eyebrow"))
        titles.addWidget(self.label("Ваши воспоминания. В порядке.", "title"))
        titles.addWidget(
            self.label(
                "Соберите фото и видео в понятный архив — по годам и дням.", "subtitle"
            )
        )
        header.addLayout(titles, 1)
        header.addWidget(
            self.label("●  Только на вашем ПК", "badge"),
            alignment=Qt.AlignmentFlag.AlignTop,
        )
        column.addLayout(header)

        card, grid = self.card_grid()
        grid.addWidget(self.label("01   Откуда и куда", "section"), 0, 0, 1, 3)
        self.source = QLineEdit(os.environ.get("PHOTOCATALOG_SOURCE", ""))
        self.destination = QLineEdit(os.environ.get("PHOTOCATALOG_DESTINATION", ""))
        self.source.setPlaceholderText("Папка с фотографиями, видео и ZIP-архивами")
        self.destination.setPlaceholderText("Отдельная папка для готовой медиатеки")
        self.source.setAccessibleName("Папка-источник")
        self.destination.setAccessibleName("Папка назначения")
        self.browse_source = QPushButton("Выбрать…")
        self.browse_dest = QPushButton("Выбрать…")
        self.browse_source.clicked.connect(lambda: self.choose(self.source))
        self.browse_dest.clicked.connect(lambda: self.choose(self.destination))
        grid.addWidget(QLabel("Источник"), 1, 0)
        grid.addWidget(self.source, 1, 1)
        grid.addWidget(self.browse_source, 1, 2)
        grid.addWidget(QLabel("Назначение"), 2, 0)
        grid.addWidget(self.destination, 2, 1)
        grid.addWidget(self.browse_dest, 2, 2)
        hint = self.label(
            "Оригиналы остаются на месте. Существующие файлы не перезаписываются.",
            "subtitle",
        )
        grid.addWidget(hint, 3, 0, 1, 3)
        grid.setColumnStretch(1, 1)
        column.addWidget(card)

        card, grid = self.card_grid()
        grid.addWidget(self.label("02   Как обрабатывать", "section"), 0, 0, 1, 4)
        self.zips = QCheckBox("Включить ZIP-архивы")
        self.zips.setChecked(True)
        self.video = QCheckBox("Читать даты видео")
        self.video.setChecked(True)
        self.video.setToolTip("В EXE библиотека MediaInfo уже встроена.")
        self.workers = QSpinBox()
        self.workers.setRange(1, 64)
        self.workers.setValue(4)
        self.workers.setAccessibleName("Количество параллельных задач")
        grid.addWidget(self.zips, 1, 0)
        grid.addWidget(self.video, 1, 1)
        grid.addWidget(QLabel("Параллельных задач"), 1, 2)
        grid.addWidget(self.workers, 1, 3)
        column.addWidget(card)

        actions = QHBoxLayout()
        self.preview = QPushButton("Предпросмотр")
        self.start_button = QPushButton("Начать копирование  →")
        self.start_button.setObjectName("primary")
        self.stop_button = QPushButton("Остановить")
        self.stop_button.setObjectName("stop")
        self.stop_button.setEnabled(False)
        self.preview.clicked.connect(lambda: self.start(True))
        self.start_button.clicked.connect(lambda: self.start(False))
        self.stop_button.clicked.connect(self.stop)
        actions.addWidget(self.preview)
        actions.addWidget(self.start_button)
        actions.addStretch()
        actions.addWidget(self.stop_button)
        column.addLayout(actions)

        metrics = QHBoxLayout()
        self.metric_labels: dict[str, QLabel] = {}
        for key, title in [
            ("processed", "ОБРАБОТАНО"),
            ("copied", "НОВЫХ КОПИЙ"),
            ("duplicate", "УЖЕ В КАТАЛОГЕ"),
            ("error", "ОШИБОК"),
        ]:
            frame, metric_grid = self.card_grid(margins=14)
            value = self.label("0", "metric")
            metric_grid.addWidget(value, 0, 0)
            metric_grid.addWidget(self.label(title, "subtitle"), 1, 0)
            self.metric_labels[key] = value
            metrics.addWidget(frame)
        column.addLayout(metrics)

        results, results_layout = self.card_grid()
        title_row = QHBoxLayout()
        title_row.addWidget(self.label("Результаты", "section"))
        title_row.addStretch()
        self.open_button = QPushButton("Открыть папку")
        self.export_button = QPushButton("Сохранить отчёт")
        self.open_button.setEnabled(False)
        self.export_button.setEnabled(False)
        self.open_button.clicked.connect(self.open_destination)
        self.export_button.clicked.connect(self.export)
        title_row.addWidget(self.open_button)
        title_row.addWidget(self.export_button)
        results_layout.addLayout(title_row, 0, 0)
        self.table = QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(
            ["Файл", "Результат", "Дата", "Источник даты"]
        )
        self.table.verticalHeader().hide()
        self.table.setShowGrid(False)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.horizontalHeader().setSectionResizeMode(
            0, QHeaderView.ResizeMode.Stretch
        )
        for index, width in [(1, 135), (2, 125), (3, 125)]:
            self.table.setColumnWidth(index, width)
        self.table.setMinimumHeight(150)
        self.table.cellDoubleClicked.connect(self.details)
        results_layout.addWidget(self.table, 1, 0)
        results_layout.setRowStretch(1, 1)
        self.empty_hint = self.label(
            "Выберите папки и начните с предпросмотра. Файлы не будут записаны.",
            "subtitle",
        )
        self.empty_hint.setWordWrap(True)
        results_layout.addWidget(self.empty_hint, 2, 0)
        column.addWidget(results, 1)

        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setValue(0)
        self.progress.setTextVisible(False)
        column.addWidget(self.progress)
        self.status = self.label("Готово к работе", "subtitle")
        self.status.setWordWrap(True)
        column.addWidget(self.status)

    @staticmethod
    def label(text: str, name: str = "") -> QLabel:
        result = QLabel(text)
        result.setObjectName(name)
        return result

    def card_grid(self, margins: int = 18) -> tuple[QFrame, QGridLayout]:
        card = QFrame()
        card.setObjectName("card")
        grid = QGridLayout(card)
        grid.setContentsMargins(margins, margins, margins, margins)
        grid.setVerticalSpacing(12)
        grid.setHorizontalSpacing(14)
        return card, grid

    def sidebar(self) -> QFrame:
        sidebar = QFrame()
        sidebar.setObjectName("sidebar")
        sidebar.setFixedWidth(210)
        column = QVBoxLayout(sidebar)
        column.setContentsMargins(23, 28, 20, 24)
        icon = QLabel()
        icon.setPixmap(application_icon().pixmap(50, 50))
        column.addWidget(icon)
        column.addSpacing(10)
        column.addWidget(self.label("PhotoCatalog", "brand"))
        column.addWidget(QLabel("DESKTOP  /  " + __version__))
        column.addSpacing(42)
        active = QLabel("  ●   Каталогизация")
        active.setStyleSheet(
            "background: #234139; color: #b4efdc; border-radius: 7px; padding: 12px;"
        )
        column.addWidget(active)
        column.addSpacing(30)
        for heading, detail in [
            ("01  Выберите папки", "Укажите источник\nи место для архива."),
            ("02  Проверьте план", "Посмотрите результат\nдо копирования."),
            ("03  Сохраните порядок", "Новые копии проверяются\nпо содержимому."),
        ]:
            label = QLabel(heading)
            label.setStyleSheet("color: #e0e8f3; font-weight: 600;")
            column.addWidget(label)
            detail_label = QLabel(detail)
            detail_label.setStyleSheet("color: #91a4bd; font-size: 12px;")
            column.addWidget(detail_label)
            column.addSpacing(15)
        column.addStretch()
        note = QLabel(
            "БЕЗ ОБЛАКА\n\nВаши файлы остаются\nна вашем компьютере.\n\nSHA-256 · безопасные копии"
        )
        note.setStyleSheet("color: #92a7c0; font-size: 11px;")
        column.addWidget(note)
        return sidebar

    def choose(self, field: QLineEdit) -> None:
        selected = QFileDialog.getExistingDirectory(
            self, "Выберите папку", field.text()
        )
        if selected:
            field.setText(selected)

    def set_busy(self, busy: bool) -> None:
        for widget in [
            self.source,
            self.destination,
            self.browse_source,
            self.browse_dest,
            self.zips,
            self.video,
            self.workers,
            self.preview,
            self.start_button,
        ]:
            widget.setEnabled(not busy)
        self.stop_button.setEnabled(busy)
        self.export_button.setEnabled(not busy and self.summary is not None)
        self.open_button.setEnabled(
            not busy
            and self.last_destination is not None
            and self.last_destination.is_dir()
        )

    def start(self, dry_run: bool) -> None:
        if self.thread is not None and self.thread.isRunning():
            return
        try:
            if not self.source.text().strip() or not self.destination.text().strip():
                raise ValueError("Выберите папку-источник и папку назначения.")
            source, destination = validate_roots(
                Path(self.source.text().strip()), Path(self.destination.text().strip())
            )
            config = Config(
                source,
                destination,
                workers=self.workers.value(),
                batch_size=16,
                dry_run=dry_run,
                extract_zips=self.zips.isChecked(),
                fast_video=not self.video.isChecked(),
                library=bundled_library(),
            )
        except Exception as exc:
            QMessageBox.warning(self, "Проверьте настройки", str(exc))
            return
        self.dry_run = dry_run
        self.last_destination = destination
        self.summary = None
        self.counts.clear()
        self.table.setRowCount(0)
        for label in self.metric_labels.values():
            label.setText("0")
        self.empty_hint.setText(
            "Предпросмотр: без записи. Для ZIP даты предварительные."
            if dry_run
            else "Двойной щелчок по строке — пути и подробности."
        )
        self.cancel_event = Event()
        self.progress.setRange(0, 0)
        self.status.setText("Сканирование и подготовка…")
        self.set_busy(True)
        self.export_button.setEnabled(False)
        self.open_button.setEnabled(False)
        self.thread = QThread(self)
        self.worker = Worker(config, self.cancel_event)
        self.worker.moveToThread(self.thread)
        self.thread.started.connect(self.worker.execute)
        self.worker.record.connect(self.add_record)
        self.worker.completed.connect(self.complete)
        self.worker.failed.connect(self.failure)
        self.worker.completed.connect(self.thread.quit)
        self.worker.failed.connect(self.thread.quit)
        self.worker.completed.connect(self.worker.deleteLater)
        self.worker.failed.connect(self.worker.deleteLater)
        self.thread.finished.connect(self.thread_finished)
        self.thread.start()

    @Slot(object)
    def add_record(self, record: Record) -> None:
        self.counts["processed"] += 1
        self.counts[record.status] += 1
        for key, label in self.metric_labels.items():
            label.setText(str(self.counts[key]))
        # Full records remain in Summary; keep the visual table responsive.
        if self.table.rowCount() >= 2000:
            self.table.removeRow(0)
        row = self.table.rowCount()
        self.table.insertRow(row)
        path = record.source.split("!")[-1]
        values = [
            Path(path).name,
            STATUS.get(record.status, record.status),
            record.date[:10] or "—",
            {
                "exif": "EXIF",
                "video": "Видео",
                "mtime": "Дата файла",
                "zip_mtime": "ZIP · предварительно",
            }.get(record.date_source, "—"),
        ]
        detail = (
            f"Источник: {record.source}\nНазначение: {record.target or '—'}"
            f"\nДата: {record.date or '—'}\n{record.message}"
        )
        for col, text in enumerate(values):
            item = QTableWidgetItem(text)
            item.setToolTip(detail)
            item.setData(Qt.ItemDataRole.UserRole, detail)
            if col == 1:
                item.setForeground(QColor(COLORS.get(record.status, "#66758a")))
            self.table.setItem(row, col, item)
        if not self.cancel_event.is_set():
            self.status.setText(
                f"Обработано: {self.counts['processed']}  ·  {Path(path).name}"
            )

    @Slot(object)
    def complete(self, summary: Summary) -> None:
        self.summary = summary
        self.progress.setRange(0, 100)
        self.progress.setValue(0 if summary.cancelled else 100)
        if summary.cancelled:
            message = "Остановлено. Готовые копии сохранены; можно продолжить повторным запуском."
        elif summary.counts["error"]:
            message = (
                "Завершено с ошибками. Откройте подробности строк или сохраните отчёт."
            )
        elif not summary.records:
            message = "Подходящих фото, видео и архивов не найдено."
        elif self.dry_run:
            message = f"План готов: {summary.counts['planned']} файлов. Запись не выполнялась."
        else:
            message = (
                f"Готово: новых копий — {summary.counts['copied']}, "
                f"уже в каталоге — {summary.counts['duplicate']}."
            )
        self.status.setText(message)

    @Slot(str)
    def failure(self, message: str) -> None:
        self.progress.setRange(0, 100)
        self.progress.setValue(0)
        self.status.setText("Не удалось завершить: " + message)

    @Slot()
    def thread_finished(self) -> None:
        if self.thread is not None:
            self.thread.deleteLater()
        self.thread = None
        self.worker = None
        self.set_busy(False)
        if self.closing:
            self.close()

    def stop(self) -> None:
        self.cancel_event.set()
        self.stop_button.setEnabled(False)
        self.status.setText(
            "Останавливаемся после текущих операций. Готовые копии будут сохранены…"
        )

    def details(self, row: int, column: int) -> None:
        item = self.table.item(row, column)
        if item is not None:
            QMessageBox.information(
                self, "Подробности файла", item.data(Qt.ItemDataRole.UserRole)
            )

    def open_destination(self) -> None:
        if self.last_destination is not None:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.last_destination)))

    def export(self) -> None:
        if self.summary is None:
            return
        filename, _ = QFileDialog.getSaveFileName(
            self,
            "Сохранить новый отчёт",
            f"PhotoCatalog-{datetime.now():%Y%m%d-%H%M%S}.json",
            "JSON (*.json)",
            options=QFileDialog.Option.DontConfirmOverwrite,
        )
        if filename:
            try:
                path = Path(filename).resolve()
                source = Path(self.source.text()).resolve()
                if path.is_relative_to(source):
                    raise ValueError("Сохраните отчёт вне папки-источника.")
                write_report(path, self.summary.json())
                self.status.setText("Отчёт сохранён: " + str(path))
            except Exception as exc:
                QMessageBox.warning(self, "Отчёт не сохранён", str(exc))

    def closeEvent(self, event: QCloseEvent) -> None:
        if self.thread is not None and self.thread.isRunning():
            answer = QMessageBox.question(
                self,
                "Обработка ещё идёт",
                "Остановить обработку и закрыть приложение после текущих операций?",
            )
            if answer == QMessageBox.StandardButton.Yes:
                self.closing = True
                self.stop()
            event.ignore()
        else:
            event.accept()


def main() -> int:
    app = QApplication(sys.argv)
    app.setApplicationName("PhotoCatalog")
    app.setApplicationVersion(__version__)
    app.setFont(QFont("Segoe UI", 10))
    window = Window()
    window.show()
    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
