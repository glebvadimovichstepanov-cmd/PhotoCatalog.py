"""Run the GUI through the same self-test used on the packaged executable."""

import json

import pytest


def test_gui_preview_copy_and_repeat(tmp_path):
    pytest.importorskip("PySide6")
    from photocatalog.desktop_check import self_test

    assert self_test(str(tmp_path / "gui-check")) == 0
    result = json.loads((tmp_path / "gui-check" / "self-test.json").read_text())
    assert result["gui_preview"] and result["gui_copy"] and result["gui_repeat"]
    assert (tmp_path / "gui-check" / "desktop-preview.png").is_file()
