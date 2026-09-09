import zipfile
from pathlib import Path
from threading import Event

import pytest

from photocatalog.archives import Limits, extract
from photocatalog.catalog import Config, run


def test_progress_delivers_all_records(photo, tmp_path):
    seen = []
    summary = run(Config(photo.parent, tmp_path / "out"), progress=seen.append)
    assert seen == summary.records
    assert seen[0].status == "copied"


def test_cancel_before_run_writes_nothing(photo, tmp_path):
    stop = Event()
    stop.set()
    result = run(Config(photo.parent, tmp_path / "out"), cancel=stop)
    assert result.cancelled
    assert not (tmp_path / "out").exists()


def test_cancel_after_completed_copy_retains_it(photo, tmp_path):
    second = photo.parent / "second.jpg"
    second.write_bytes(photo.read_bytes())
    stop = Event()
    config = Config(photo.parent, tmp_path / "out", workers=1, batch_size=1)
    result = run(config, progress=lambda _: stop.set(), cancel=stop)
    assert result.cancelled
    assert result.counts["copied"] == 1
    assert Path(result.records[0].target).read_bytes() == photo.read_bytes()
    resumed = run(config)
    assert resumed.counts["duplicate"] == 1
    assert resumed.counts["copied"] == 1


def test_cancel_archive_before_extract(tmp_path):
    path = tmp_path / "photos.zip"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("one.jpg", b"generated")
    with zipfile.ZipFile(path) as archive:
        with pytest.raises(InterruptedError):
            extract(archive, tmp_path / "out", Limits(), should_stop=lambda: True)
    assert not (tmp_path / "out").exists()
