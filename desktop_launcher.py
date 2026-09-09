"""PyInstaller entry point, including a reproducible offscreen smoke test."""

import multiprocessing
import sys

if __name__ == "__main__":
    multiprocessing.freeze_support()
    if len(sys.argv) == 3 and sys.argv[1] == "--self-test":
        from photocatalog.desktop_check import self_test

        raise SystemExit(self_test(sys.argv[2]))
    if sys.platform == "win32":
        import ctypes

        console = ctypes.windll.kernel32.GetConsoleWindow()
        if console:
            ctypes.windll.user32.ShowWindow(console, 0)
    from photocatalog.gui import main

    raise SystemExit(main())
