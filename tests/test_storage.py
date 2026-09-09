import os
import stat
from concurrent.futures import ThreadPoolExecutor

import pytest

from photocatalog import storage


def test_collision_preserves_both_and_rerun(tmp_path):
    a, b = tmp_path / "a", tmp_path / "b"
    a.write_bytes(b"first")
    b.write_bytes(b"second")
    target = tmp_path / "out" / "same.jpg"
    first = storage.copy_verified(a, target)
    second = storage.copy_verified(b, target)
    assert first.target.read_bytes() == b"first"
    assert second.target.read_bytes() == b"second"
    assert first.target != second.target
    assert storage.copy_verified(b, target).status == "duplicate"
    assert len(list(target.parent.iterdir())) == 2


def test_concurrent_publication(tmp_path):
    paths = []
    for index in range(12):
        path = tmp_path / str(index)
        path.write_bytes(bytes([index]) * 20000)
        paths.append(path)
    target = tmp_path / "out" / "same.jpg"
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(lambda p: storage.copy_verified(p, target), paths))
    assert len({r.target for r in results}) == 12
    assert {r.target.read_bytes() for r in results} == {p.read_bytes() for p in paths}
    for path in paths:
        assert storage.copy_verified(path, target).status == "duplicate"


def test_competing_create_then_rerun(tmp_path, monkeypatch):
    source = tmp_path / "source"
    source.write_bytes(b"mine")
    target = tmp_path / "out" / "same.jpg"
    original = storage.publish
    attempts = []

    def competing(temp, candidate):
        if not attempts:
            attempts.append(True)
            candidate.write_bytes(b"competitor")
            raise FileExistsError(str(candidate))
        original(temp, candidate)

    monkeypatch.setattr(storage, "publish", competing)
    saved = storage.copy_verified(source, target)
    assert target.read_bytes() == b"competitor"
    assert saved.target.read_bytes() == b"mine"
    assert storage.copy_verified(source, target).target == saved.target
    assert len(list(target.parent.iterdir())) == 2


def test_partial_copy_failure_keeps_existing(tmp_path, monkeypatch):
    source, target = tmp_path / "source", tmp_path / "out" / "same.jpg"
    source.write_bytes(b"new")
    target.parent.mkdir()
    target.write_bytes(b"old")

    def broken(source, temporary):
        temporary.write_bytes(b"partial")
        raise OSError("disk full")

    monkeypatch.setattr(storage.shutil, "copyfile", broken)
    with pytest.raises(OSError, match="disk full"):
        storage.copy_verified(source, target)
    assert target.read_bytes() == b"old" and source.read_bytes() == b"new"
    assert list(target.parent.iterdir()) == [target]


def test_source_change_rejects_publication(tmp_path, monkeypatch):
    source, target = tmp_path / "source", tmp_path / "out" / "same.jpg"
    source.write_bytes(b"before")
    original = storage.shutil.copyfile

    def changed(src, dst):
        original(src, dst)
        src.write_bytes(b"after!")

    monkeypatch.setattr(storage.shutil, "copyfile", changed)
    with pytest.raises(OSError, match="Source changed"):
        storage.copy_verified(source, target)
    assert not target.exists()
    assert not list(target.parent.iterdir())


def test_readonly_source_and_timestamps(tmp_path):
    source = tmp_path / "source"
    source.write_bytes(b"readonly")
    os.utime(source, (1700000000, 1700000000))
    source.chmod(stat.S_IREAD)
    try:
        saved = storage.copy_verified(source, tmp_path / "out" / "same.jpg")
        assert saved.target.stat().st_mtime_ns == source.stat().st_mtime_ns
        assert storage.copy_verified(source, saved.target).status == "duplicate"
    finally:
        source.chmod(stat.S_IREAD | stat.S_IWRITE)


@pytest.mark.parametrize("which", ["same", "child", "parent"])
def test_overlapping_roots(tmp_path, which):
    source = tmp_path / "source"
    source.mkdir()
    target = {"same": source, "child": source / "out", "parent": tmp_path}[which]
    with pytest.raises(ValueError, match="overlap"):
        storage.validate_roots(source, target)


def test_report_never_overwrites(tmp_path):
    target = tmp_path / "report.json"
    storage.write_report(target, "original")
    with pytest.raises(FileExistsError):
        storage.write_report(target, "replacement")
    assert target.read_text() == "original"
    assert list(tmp_path.iterdir()) == [target]


def test_processes_cannot_replace_each_other(tmp_path):
    from concurrent.futures import ProcessPoolExecutor

    sources = []
    for index in range(6):
        source = tmp_path / str(index)
        source.write_bytes(bytes([index]) * 10000)
        sources.append(source)
    desired = tmp_path / "out" / "same.jpg"
    with ProcessPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(storage.copy_verified, p, desired) for p in sources]
        results = [future.result() for future in futures]
    assert len({r.target for r in results}) == 6
    assert {r.target.read_bytes() for r in results} == {p.read_bytes() for p in sources}


@pytest.mark.skipif(os.name != "nt", reason="Windows junction behavior")
def test_real_windows_junction_rejected(tmp_path):
    import subprocess

    real = tmp_path / "real"
    real.mkdir()
    junction = tmp_path / "junction"
    created = subprocess.run(
        ["cmd", "/c", "mklink", "/J", str(junction), str(real)],
        capture_output=True,
    )
    assert created.returncode == 0
    try:
        with pytest.raises(ValueError, match="junctions"):
            storage.validate_roots(junction, tmp_path / "out")
    finally:
        os.rmdir(junction)
    assert real.is_dir()
