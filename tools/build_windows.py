"""Build the Windows GUI, including Qt, Python, MediaInfo and licenses."""

import argparse
import hashlib
import os
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageDraw


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if sys.platform != "win32":
        parser.error("Build the Windows EXE on Windows")
    root = Path(__file__).resolve().parents[1]
    output = args.output.resolve() if args.output else root / "dist"
    branding = root / "build" / "branding"
    branding.mkdir(parents=True, exist_ok=True)
    icon = Image.new("RGBA", (256, 256))
    draw = ImageDraw.Draw(icon)
    draw.rounded_rectangle((0, 0, 255, 255), 58, fill="#16846d")
    draw.rounded_rectangle((52, 76, 204, 192), 20, fill="white")
    draw.rounded_rectangle((84, 56, 144, 96), 12, fill="white")
    draw.ellipse((96, 96, 164, 164), fill="#16846d")
    draw.ellipse((112, 112, 148, 148), fill="white")
    icon.save(
        branding / "PhotoCatalog.ico",
        sizes=[(16, 16), (32, 32), (48, 48), (64, 64), (128, 128), (256, 256)],
    )
    env = os.environ.copy()
    env["PYINSTALLER_CONFIG_DIR"] = str(root / "build" / "pyinstaller-cache")
    subprocess.run(
        [
            sys.executable,
            "-m",
            "PyInstaller",
            "--noconfirm",
            "--distpath",
            str(output),
            "--workpath",
            str(root / "build" / "pyinstaller"),
            str(root / "PhotoCatalog.spec"),
        ],
        cwd=root,
        env=env,
        check=True,
    )
    binary = output / "PhotoCatalog.exe"
    checksum = hashlib.sha256(binary.read_bytes()).hexdigest()
    (output / "PhotoCatalog.exe.sha256").write_text(
        f"{checksum}  PhotoCatalog.exe\n", encoding="ascii"
    )
    print(f"Built {binary} ({binary.stat().st_size:,} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
