"""Strict ZIP member validation and bounded, private extraction."""

import os
import re
import stat
import zipfile
from collections.abc import Callable
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath


@dataclass(frozen=True)
class Limits:
    files: int = 10000
    bytes: int = 10 * 1024**3
    ratio: int = 1000

    def validate(self) -> None:
        if min(self.files, self.bytes, self.ratio) <= 0:
            raise ValueError("ZIP limits must be positive")


def members(
    archive: zipfile.ZipFile, limits: Limits
) -> list[tuple[zipfile.ZipInfo, Path]]:
    limits.validate()
    infos = archive.infolist()
    if len(infos) > limits.files:
        raise ValueError("ZIP member count exceeds limit")
    result = []
    seen: set[str] = set()
    total = 0
    for info in infos:
        # filename may already be normalized by zipfile on Windows (and
        # truncated at NUL). Validate the original archive spelling.
        raw = info.orig_filename
        name = PurePosixPath(raw)
        parts = raw.rstrip("/").split("/")
        if (
            not raw
            or "\\" in raw
            or name.is_absolute()
            or any(p in {"", ".", ".."} for p in parts)
        ):
            raise ValueError(f"Unsafe ZIP path: {raw!r}")
        for part in parts:
            if (
                re.search(r'[<>:"|?*\x00-\x1f]', part)
                or part.endswith((" ", "."))
                or re.fullmatch(
                    r"(?i)(CON|PRN|AUX|NUL|COM[1-9¹²³]|LPT[1-9¹²³])", part.split(".")[0]
                )
            ):
                raise ValueError(f"Unsafe Windows ZIP name: {raw!r}")
        mode = info.external_attr >> 16
        if stat.S_IFMT(mode) not in (0, stat.S_IFREG, stat.S_IFDIR):
            raise ValueError(f"Non-regular ZIP member: {raw!r}")
        if info.flag_bits & 1:
            raise ValueError(f"Encrypted ZIP member is unsupported: {raw!r}")
        key = "/".join(parts).casefold()
        if key in seen:
            raise ValueError(f"Duplicate ZIP member: {raw!r}")
        seen.add(key)
        total += info.file_size
        if total > limits.bytes:
            raise ValueError("ZIP expanded size exceeds limit")
        if info.file_size > max(info.compress_size, 1) * limits.ratio:
            raise ValueError("ZIP compression ratio exceeds limit")
        result.append((info, Path(*parts)))
    return result


def extract(
    archive: zipfile.ZipFile,
    destination: Path,
    limits: Limits,
    *,
    should_stop: Callable[[], bool] | None = None,
) -> list[Path]:
    # Caller owns a fresh TemporaryDirectory and discards the entire archive
    # after any failure. Never scan partially extracted content.
    entries = members(archive, limits)
    total = 0
    paths = []
    for info, relative in entries:
        if should_stop is not None and should_stop():
            raise InterruptedError("Archive extraction cancelled")
        target = destination / relative
        if info.is_dir():
            target.mkdir(parents=True, exist_ok=True)
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        size = 0
        with archive.open(info) as source, target.open("xb") as output:
            while chunk := source.read(1024 * 1024):
                if should_stop is not None and should_stop():
                    raise InterruptedError("Archive extraction cancelled")
                size += len(chunk)
                total += len(chunk)
                if size > info.file_size or total > limits.bytes:
                    raise ValueError("ZIP expanded data exceeds declared size or limit")
                output.write(chunk)
        if size != info.file_size:
            raise ValueError(f"ZIP size mismatch: {info.filename}")
        timestamp = datetime(*info.date_time).timestamp()
        os.utime(target, (timestamp, timestamp))
        paths.append(target)
    return paths
