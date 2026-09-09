from pathlib import Path

import pytest
from PIL import Image


@pytest.fixture
def photo(tmp_path: Path) -> Path:
    path = tmp_path / "source" / "снимок.jpg"
    path.parent.mkdir()
    exif = Image.Exif()
    exif[36867] = "2020:02:03 04:05:06"
    Image.new("RGB", (8, 8), "red").save(path, exif=exif)
    return path
