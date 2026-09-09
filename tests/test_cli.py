import json
import subprocess
import sys

import pytest

from photocatalog import cli


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["a", "b", "-w", "0"],
        ["a", "b", "-b", "-1"],
        ["a", "b", "-w", "65"],
        ["a", "b", "--zip-max-files", "0"],
        ["a", "b", "--dry-run", "--report", "report.json"],
    ],
)
def test_invalid_arguments(args):
    with pytest.raises(SystemExit) as exc:
        cli.main(args)
    assert exc.value.code == 2


def test_missing_source_exit(tmp_path):
    assert cli.main([str(tmp_path / "missing"), str(tmp_path / "out")]) == 2


def test_subprocess_install_entrypoint_and_report(photo, tmp_path):
    report = tmp_path / "report.json"
    command = [
        sys.executable,
        "-m",
        "photocatalog",
        str(photo.parent),
        str(tmp_path / "out"),
        "--report",
        str(report),
    ]
    result = subprocess.run(command, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    assert json.loads(report.read_text(encoding="utf-8"))["counts"]["copied"] == 1
    repeated = subprocess.run(command, capture_output=True, text=True)
    assert repeated.returncode == 2


def test_help_without_video_or_tqdm(monkeypatch):
    monkeypatch.setitem(sys.modules, "pymediainfo", None)
    monkeypatch.setitem(sys.modules, "tqdm", None)
    with pytest.raises(SystemExit) as exc:
        cli.main(["--help"])
    assert exc.value.code == 0
    assert cli.main(["--check-mediainfo"]) == 1


def test_diagnostic_honors_library(monkeypatch):
    calls = []
    monkeypatch.setattr(
        cli, "mediainfo_status", lambda path: (calls.append(path) or False, "not found")
    )
    assert cli.main(["--check-mediainfo", "--mediainfo-lib", "custom.dll"]) == 1
    assert calls == ["custom.dll"]


def test_environment_and_override(photo, tmp_path, monkeypatch):
    monkeypatch.setenv("PHOTOCATALOG_SOURCE", str(photo.parent))
    monkeypatch.setenv("PHOTOCATALOG_DESTINATION", str(tmp_path / "out"))
    monkeypatch.setenv("PHOTOCATALOG_WORKERS", "not-a-number")
    assert cli.main(["-w", "1", "--dry-run"]) == 0
    assert not (tmp_path / "out").exists()


def test_error_exit_for_bad_zip(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "broken.zip").write_bytes(b"bad")
    assert cli.main([str(source), str(tmp_path / "out")]) == 1


def test_interruption_exit(monkeypatch):
    def interrupted(config):
        raise KeyboardInterrupt

    monkeypatch.setattr(cli, "run", interrupted)
    assert cli.main(["source", "out"]) == 130
