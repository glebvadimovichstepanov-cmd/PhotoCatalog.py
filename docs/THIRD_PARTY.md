# Сторонние компоненты PhotoCatalog Desktop

EXE содержит Python, Qt/PySide6, shiboken6, Pillow, pymediainfo и нативную MediaInfo.dll. Python для запуска отдельно не требуется. Приложение работает локально и не отправляет медиа на серверы.

- Qt / PySide6 / shiboken6 6.8.2: LGPL-3.0 / GPL-совместимые условия согласно метаданным официальных пакетов. Исходники соответствующей версии: https://code.qt.io/cgit/pyside/pyside-setup.git/tag/?h=v6.8.2 и https://download.qt.io/archive/qt/6.8/6.8.2/submodules/ .
- MediaInfo: лицензия поставляемой библиотеки включена из pymediainfo/License.html. Исходники: https://github.com/MediaArea/MediaInfoLib .
- pymediainfo 7.0.1: MIT; исходники https://github.com/sbraz/pymediainfo .
- Pillow 12.3.0: лицензии включены из официального Python-пакета; https://github.com/python-pillow/Pillow .
- PyInstaller: bootloader exception; https://pyinstaller.org/en/stable/license.html .
- Python: PSF; https://docs.python.org/3/license.html .

Полные доступные тексты лицензий включены в EXE в папку licenses. При запуске one-file сборка распаковывает библиотеки во временный каталог. Для замены библиотек можно пересобрать EXE по инструкции в README из опубликованных исходников, используя изменённую совместимую сборку Qt/PySide6; не требуется закрытый SDK приложения. Ограничения на отладку изменений LGPL-компонентов приложением не вводятся.

Системный шрифт Segoe UI не включается в дистрибутив: используется установленный в Windows. Превью README построено автоматически на демонстрационных данных.
