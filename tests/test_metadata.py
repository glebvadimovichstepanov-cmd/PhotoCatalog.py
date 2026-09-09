import sys
from datetime import datetime, timedelta
from types import SimpleNamespace

import pytest
from PIL import Image

from photocatalog import metadata


@pytest.mark.parametrize("text", ["", "bad", "2026-99-99 12:00:00", None, 123])
def test_invalid_dates(text):
    assert metadata.parse_date(text) is None


def test_fraction_and_offset():
    date = metadata.parse_date("2024-01-02T03:04:05.123456+03:00")
    assert date.microsecond == 123456
    assert date.utcoffset() == timedelta(hours=3)
    assert metadata.parse_date("UTC 2024-01-02 03:04:05").utcoffset() == timedelta(0)


def test_real_exif_priority(photo):
    with Image.open(photo) as source:
        exif = source.getexif()
        exif[306] = "2026:01:01 00:00:00"
        source.save(photo.parent / "edited.jpg", exif=exif)
    date = metadata.read_date(photo.parent / "edited.jpg")
    assert date.value == datetime(2020, 2, 3, 4, 5, 6)
    assert date.source == "exif"


def test_invalid_original_falls_back_to_valid_exif(photo):
    with Image.open(photo) as source:
        exif = source.getexif()
        exif[36867] = "invalid"
        exif[306] = "2021:01:01 00:00:00"
        source.save(photo.parent / "edited.jpg", exif=exif)
    assert metadata.read_date(photo.parent / "edited.jpg").value.year == 2021


def test_dll_failure_is_false(monkeypatch):
    def unavailable(**kwargs):
        raise OSError("DLL failure")

    monkeypatch.setitem(
        sys.modules,
        "pymediainfo",
        SimpleNamespace(MediaInfo=SimpleNamespace(can_parse=unavailable)),
    )
    ok, message = metadata.mediainfo_status()
    assert not ok and "DLL failure" in message


def test_missing_package_and_video_fallback(tmp_path, monkeypatch):
    monkeypatch.setitem(sys.modules, "pymediainfo", None)
    assert not metadata.mediainfo_status()[0]
    video = tmp_path / "video.mp4"
    video.write_bytes(b"generated")
    date = metadata.read_date(video)
    assert date.source == "mtime" and "unavailable" in date.warning


def test_video_recorded_first_and_library_passed(tmp_path, monkeypatch):
    calls = []

    def parse(path, **kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            tracks=[
                SimpleNamespace(
                    track_type="General",
                    recorded_date="2020-01-01 00:00:00",
                    encoded_date="2026-01-01 00:00:00",
                )
            ]
        )

    monkeypatch.setitem(
        sys.modules,
        "pymediainfo",
        SimpleNamespace(MediaInfo=SimpleNamespace(parse=parse)),
    )
    assert metadata.video_date(tmp_path / "video.mp4", "custom.dll").year == 2020
    assert calls == [{"library_file": "custom.dll"}]


def test_missing_source_not_current_time(tmp_path):
    with pytest.raises(FileNotFoundError):
        metadata.read_date(tmp_path / "missing.jpg")


def test_corrupt_image_warning(tmp_path):
    path = tmp_path / "bad.jpg"
    path.write_bytes(b"not a picture")
    date = metadata.read_date(path)
    assert date.source == "mtime"
    assert "unavailable" in date.warning
