# Build with: python tools/build_windows.py
from importlib.metadata import distribution
from pathlib import Path

from PyInstaller.utils.hooks import collect_dynamic_libs
from importlib.util import find_spec

root = Path(SPECPATH)
qt_dir = Path(find_spec("PySide6").submodule_search_locations[0])
qt_core_binaries = [
    (str(qt_dir / name), name) for name in ("Qt6Core.dll", "Qt6Gui.dll", "Qt6Widgets.dll")
]
license_files = [(str(root / "docs" / "THIRD_PARTY.md"), "licenses")]
for name in ("PySide6-Essentials", "shiboken6", "pymediainfo", "Pillow", "PyInstaller"):
    dist = distribution(name)
    for relative in dist.files or ():
        if "license" in str(relative).lower() or relative.name in ("COPYING.txt",):
            path = Path(dist.locate_file(relative))
            if path.is_file():
                license_files.append((str(path), "licenses/" + name))

a = Analysis(
    [str(root / "desktop_launcher.py")],
    pathex=[str(root / "src")],
    binaries=collect_dynamic_libs("pymediainfo") + qt_core_binaries,
    datas=license_files,
    hiddenimports=["pymediainfo"],
    hookspath=[],
    runtime_hooks=[str(root / "tools" / "runtime_hook.py")],
    excludes=["tkinter", "pytest", "PySide6.QtQml", "PySide6.QtQuick"],
    noarchive=False,
)
pyz = PYZ(a.pure)
exe = EXE(
    pyz, a.scripts, a.binaries, a.datas, [],
    name="PhotoCatalog",
    debug=False,
    strip=False,
    upx=False,
    console=True,
    icon=str(root / "build" / "branding" / "PhotoCatalog.ico"),
    version=str(root / "windows-version.txt"),
)
