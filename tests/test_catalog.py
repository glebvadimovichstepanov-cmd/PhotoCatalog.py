import json
import zipfile
from dataclasses import replace
from pathlib import Path

from photocatalog.catalog import Config, run


def test_real_photo_roundtrip_repeat_and_report(photo, tmp_path):
    before = photo.read_bytes(), photo.stat().st_mtime_ns
    config = Config(photo.parent, tmp_path / "catalog", workers=2)
    summary = run(config)
    assert summary.counts["copied"] == 1
    result = summary.records[0]
    assert result.date_source == "exif"
    assert Path(result.target).read_bytes() == before[0]
    assert (photo.read_bytes(), photo.stat().st_mtime_ns) == before
    assert run(config).counts["duplicate"] == 1
    assert json.loads(summary.json())["records"][0]["sha256"]


def test_dry_run_no_destination_or_extraction(photo, tmp_path, monkeypatch):
    with zipfile.ZipFile(photo.parent / "fixture.zip", "w") as archive:
        archive.write(photo, "archived.jpg")

    def forbidden(*args, **kwargs):
        raise AssertionError("Dry-run attempted to create temporary directory")

    monkeypatch.setattr("photocatalog.catalog.tempfile.TemporaryDirectory", forbidden)
    result = run(Config(photo.parent, tmp_path / "out", dry_run=True))
    assert result.counts["planned"] == 2
    assert result.counts["error"] == 0
    assert not (tmp_path / "out").exists()
    assert any(r.date_source == "zip_mtime" for r in result.records)


def test_zip_cleanup_and_label(photo, tmp_path, monkeypatch):
    source = tmp_path / "zip_source"
    source.mkdir()
    with zipfile.ZipFile(source / "fixture.zip", "w") as archive:
        archive.write(photo, "nested/archived.jpg")
    import photocatalog.catalog as catalog

    original = catalog.tempfile.TemporaryDirectory
    folders = []

    def tracked(*args, **kwargs):
        temporary = original(*args, **kwargs)
        folders.append(Path(temporary.name))
        return temporary

    monkeypatch.setattr(catalog.tempfile, "TemporaryDirectory", tracked)
    summary = run(Config(source, tmp_path / "out"))
    assert summary.counts["copied"] == 1
    assert "!nested/archived.jpg" in summary.records[0].source
    assert all(not folder.exists() for folder in folders)


def test_bad_zip_continues_other_files(photo, tmp_path):
    (photo.parent / "broken.zip").write_bytes(b"bad")
    summary = run(Config(photo.parent, tmp_path / "out"))
    assert summary.counts["error"] == 1
    assert summary.counts["copied"] == 1


def test_empty_source(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    result = run(Config(source, tmp_path / "out"))
    assert all(n == 0 for n in result.counts.values())
    assert not (tmp_path / "out").exists()


def test_walk_error_visible(photo, tmp_path, monkeypatch):
    import photocatalog.catalog as catalog

    def inaccessible(path, onerror):
        onerror(PermissionError(13, "access denied", str(path)))
        return iter(())

    monkeypatch.setattr(catalog.os, "walk", inaccessible)
    summary = run(Config(photo.parent, tmp_path / "out"))
    assert summary.counts["error"] == 1


def test_crc_failure_publishes_no_partial_archive(photo, tmp_path):
    source = tmp_path / "zip_source"
    source.mkdir()
    path = source / "fixture.zip"
    payload = b"unique-corruption-fixture"
    with zipfile.ZipFile(path, "w") as archive:
        archive.write(photo, "valid.jpg")
        archive.writestr("bad.jpg", payload)
    content = path.read_bytes()
    path.write_bytes(content.replace(payload, b"X" * len(payload)))
    summary = run(Config(source, tmp_path / "out"))
    assert summary.counts["error"] == 1
    assert summary.counts["copied"] == 0
    assert not (tmp_path / "out").exists()


def test_dry_run_reports_existing_conflict(photo, tmp_path):
    config = Config(photo.parent, tmp_path / "out")
    run(config)
    planned = run(replace(config, dry_run=True))
    assert "Target collision" in planned.records[0].message
