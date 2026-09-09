"""Prefer bundled Qt and MediaInfo DLLs over machine-wide copies."""
import os
import sys

if getattr(sys, "frozen", False):
    root = sys._MEIPASS
    for folder in (os.path.join(root, "PySide6"),
                   os.path.join(root, "pymediainfo"), root):
        if os.path.isdir(folder):
            try:
                os.add_dll_directory(folder)
            except (AttributeError, OSError):
                pass
            os.environ["PATH"] = folder + os.pathsep + os.environ.get("PATH", "")
