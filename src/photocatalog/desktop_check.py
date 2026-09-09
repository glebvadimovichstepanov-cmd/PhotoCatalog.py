"""Packaged EXE integration check. Uses only generated media in a temp folder."""

import json
import os
import tempfile
import time
import traceback
from pathlib import Path


def self_test(output: str) -> int:
    output_dir = Path(output).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    os.environ["QT_QPA_PLATFORM"] = "offscreen"
    try:
        from PIL import Image
        from PySide6.QtGui import QFont, QFontDatabase
        from PySide6.QtWidgets import QApplication

        from .catalog import Record
        from .gui import Window, bundled_library
        from .metadata import mediainfo_status

        app = QApplication.instance() or QApplication(["PhotoCatalog self-test"])
        # Qt's offscreen Windows plugin does not enumerate system fonts.
        # Load installed fonts for this check only; do not redistribute them.
        fonts = Path(os.environ.get("WINDIR", "C:/Windows")) / "Fonts"
        for name in ("segoeui.ttf", "segoeuib.ttf"):
            if QFontDatabase.addApplicationFont(str(fonts / name)) < 0:
                raise RuntimeError(f"Could not load system font: {name}")
        app.setFont(QFont("Segoe UI", 10))
        window = Window()
        window.show()
        app.processEvents()
        library = bundled_library()
        available, message = mediainfo_status(library)
        if not available:
            raise RuntimeError(message)
        with tempfile.TemporaryDirectory(prefix="photocatalog-selftest-") as folder:
            source, destination = Path(folder) / "source", Path(folder) / "catalog"
            source.mkdir()
            photo = source / "family.jpg"
            exif = Image.Exif()
            exif[36867] = "2024:06:15 14:32:10"
            Image.new("RGB", (24, 24), "#16846d").save(photo, exif=exif)
            original = photo.read_bytes()
            window.source.setText(str(source))
            window.destination.setText(str(destination))

            def wait() -> None:
                deadline = time.monotonic() + 45
                while window.thread is not None:
                    app.processEvents()
                    if time.monotonic() > deadline:
                        window.cancel_event.set()
                        raise TimeoutError("Desktop worker did not finish")
                    time.sleep(0.01)
                if window.summary is None:
                    raise RuntimeError(window.status.text())

            window.start(True)
            wait()
            if destination.exists() or window.summary.counts["planned"] != 1:
                raise AssertionError("GUI preview wrote files or did not plan media")
            window.start(False)
            wait()
            if window.summary.counts["copied"] != 1:
                raise AssertionError(window.summary.json())
            target = Path(window.summary.records[0].target)
            if target.read_bytes() != original or photo.read_bytes() != original:
                raise AssertionError("Media bytes changed")
            window.start(False)
            wait()
            if window.summary.counts["duplicate"] != 1:
                raise AssertionError("Repeated GUI run did not detect duplicate")

        # Demonstration data is explicitly labelled, not presented as user results.
        window.source.setText("C:/Медиа/Семейный архив")
        window.destination.setText("D:/Фото/Медиатека")
        window.table.setRowCount(0)
        window.counts.clear()
        for name, state, date, source in [
            ("Летний день.jpg", "planned", "2024-06-15", "exif"),
            ("Первый снег.jpg", "planned", "2023-12-08", "exif"),
            ("Путешествие.mp4", "planned", "2024-08-21", "video"),
            ("Семейный альбом.zip!Пикник.jpg", "planned", "2022-05-14", "zip_mtime"),
        ]:
            window.add_record(Record(name, state, date=date, date_source=source))
        window.status.setText("Демонстрация интерфейса · предпросмотр без записи")
        window.empty_hint.setText(
            "Пример плана. Для файлов внутри ZIP даты предварительные."
        )
        window.resize(1280, 1040)
        app.processEvents()
        if not window.grab().save(str(output_dir / "desktop-preview.png")):
            raise RuntimeError("Could not render desktop screenshot")
        window.close()
        result = {
            "ok": True,
            "gui_preview": True,
            "gui_copy": True,
            "gui_repeat": True,
            "original_preserved": True,
            "mediainfo_available": available,
            "explicit_library": bool(library),
        }
        (output_dir / "self-test.json").write_text(
            json.dumps(result, indent=2), encoding="utf-8"
        )
        return 0
    except Exception:
        (output_dir / "self-test.json").write_text(
            json.dumps({"ok": False, "error": traceback.format_exc()}, indent=2),
            encoding="utf-8",
        )
        return 1
