import stat
import zipfile

import pytest

from photocatalog.archives import Limits, extract, members


@pytest.mark.parametrize(
    "name",
    [
        "../../victim.jpg",
        "/absolute.jpg",
        "C:/absolute.jpg",
        "dir\\evil.jpg",
        "NUL.jpg",
        "a/../b.jpg",
        "photo.jpg:stream",
        "trailing ./a.jpg",
    ],
)
def test_unsafe_member_rejected_without_changes(tmp_path, name):
    victim = tmp_path / "victim.jpg"
    victim.write_bytes(b"original")
    before = victim.stat().st_mtime_ns
    archive_path = tmp_path / "fixture.zip"
    with zipfile.ZipFile(archive_path, "w") as archive:
        info = zipfile.ZipInfo("fixture.jpg")
        # Preserve the raw ZIP name: ZipInfo's Windows constructor otherwise
        # normalizes backslashes, which would not exercise malicious input.
        info.filename = name
        archive.writestr(info, b"generated")
    output = tmp_path / "extracted"
    output.mkdir()
    with zipfile.ZipFile(archive_path) as archive:
        with pytest.raises(ValueError):
            extract(archive, output, Limits())
    assert victim.read_bytes() == b"original"
    assert victim.stat().st_mtime_ns == before
    assert not list(output.iterdir())


def test_valid_zip_bytes_and_time(tmp_path):
    path = tmp_path / "fixture.zip"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr(
            zipfile.ZipInfo("nested/photo.jpg", (2020, 2, 3, 4, 5, 6)), b"photo"
        )
    with zipfile.ZipFile(path) as archive:
        files = extract(archive, tmp_path / "out", Limits())
    assert files[0].read_bytes() == b"photo"
    from datetime import datetime

    assert datetime.fromtimestamp(files[0].stat().st_mtime).year == 2020


@pytest.mark.parametrize("limits", [Limits(files=1), Limits(bytes=3), Limits(ratio=1)])
def test_limits(tmp_path, limits):
    path = tmp_path / "fixture.zip"
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("a.jpg", b"x" * 500)
        archive.writestr("b.jpg", b"x" * 500)
    with zipfile.ZipFile(path) as archive:
        with pytest.raises(ValueError):
            members(archive, limits)


def test_link_member_rejected(tmp_path):
    path = tmp_path / "fixture.zip"
    link = zipfile.ZipInfo("link.jpg")
    link.create_system = 3
    link.external_attr = (stat.S_IFLNK | 0o777) << 16
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr(link, "outside")
    with zipfile.ZipFile(path) as archive:
        with pytest.raises(ValueError, match="Non-regular"):
            members(archive, Limits())


def test_case_colliding_members_rejected(tmp_path):
    path = tmp_path / "fixture.zip"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("A.jpg", b"a")
        archive.writestr("a.jpg", b"b")
    with zipfile.ZipFile(path) as archive:
        with pytest.raises(ValueError, match="Duplicate"):
            members(archive, Limits())


def test_encrypted_flag_rejected(tmp_path):
    path = tmp_path / "fixture.zip"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("photo.jpg", b"photo")
    with zipfile.ZipFile(path) as archive:
        archive.infolist()[0].flag_bits |= 1
        with pytest.raises(ValueError, match="Encrypted"):
            members(archive, Limits())
