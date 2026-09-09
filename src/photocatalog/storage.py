"""Filesystem boundaries, hashes and publication without replacement."""

import hashlib
import os
import re
import shutil
import tempfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path


def is_link(path: Path) -> bool:
    return path.is_symlink() or path.is_junction()


def reject_links(path: Path) -> None:
    for part in (path, *path.parents):
        if is_link(part):
            raise ValueError(f"Symbolic links/junctions are not allowed: {part}")


def validate_roots(source: Path, destination: Path) -> tuple[Path, Path]:
    reject_links(source.absolute())
    reject_links(destination.absolute())
    source, destination = source.resolve(), destination.resolve()
    if not source.is_dir():
        raise ValueError(f"Source directory does not exist: {source}")
    if destination.exists() and not destination.is_dir():
        raise ValueError(f"Destination is not a directory: {destination}")
    if source.is_relative_to(destination) or destination.is_relative_to(source):
        raise ValueError("Source and destination must not overlap")
    return source, destination


def digest(path: Path) -> str:
    reject_links(path)
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def signature(path: Path) -> tuple[int, int, int, int, int]:
    info = path.stat()
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def target_path(root: Path, name: str, date: datetime) -> Path:
    # Bound the component length and retain a deterministic identity if truncated.
    safe = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", Path(name).stem).rstrip(" .")
    if len(safe) > 64:
        safe = safe[:48] + "_" + hashlib.sha256(name.encode()).hexdigest()[:12]
    safe = safe or "media"
    stamp = date.strftime("%Y-%m-%d_%H-%M-%S")
    if date.microsecond:
        stamp += f"_{date.microsecond:06d}"
    return (
        root
        / date.strftime("%Y")
        / date.strftime("%Y-%m-%d")
        / (stamp + "_" + safe + Path(name).suffix.lower())
    )


def publish(temp: Path, target: Path) -> None:
    reject_links(target.parent)
    if os.name == "nt":
        # Windows rename fails if the destination already exists.
        os.rename(temp, target)
    else:
        # POSIX rename would replace; link instead reserves atomically.
        os.link(temp, target)
        temp.unlink()


@dataclass(frozen=True)
class CopyResult:
    target: Path
    status: str
    sha256: str


def copy_verified(source: Path, desired: Path) -> CopyResult:
    reject_links(source)
    reject_links(desired)
    if not source.is_file():
        raise ValueError(f"Source is not a regular file: {source}")
    before = signature(source)
    source_hash = digest(source)
    if signature(source) != before:
        raise OSError(f"Source changed while hashing: {source}")
    desired.parent.mkdir(parents=True, exist_ok=True)
    reject_links(desired.parent)
    fd, filename = tempfile.mkstemp(
        prefix=".photocatalog-", suffix=".tmp", dir=desired.parent
    )
    temp = Path(filename)
    os.close(fd)
    try:
        shutil.copyfile(source, temp)
        with temp.open("rb+") as stream:
            stream.flush()
            os.fsync(stream.fileno())
        if digest(temp) != source_hash:
            raise OSError(f"Copy verification failed: {source}")
        if signature(source) != before or digest(source) != source_hash:
            raise OSError(f"Source changed while copying: {source}")
        source_stat = source.stat()
        os.utime(temp, ns=(source_stat.st_atime_ns, before[3]))
        candidate = desired
        conflicts = 0
        for _ in range(10000):
            reject_links(candidate)
            if candidate.exists():
                prior = signature(candidate)
                if candidate.is_file() and digest(candidate) == source_hash:
                    if signature(candidate) == prior:
                        return CopyResult(candidate, "duplicate", source_hash)
                suffix = "_" + source_hash[:16]
                if conflicts:
                    suffix += f"_{conflicts}"
                candidate = desired.with_name(desired.stem + suffix + desired.suffix)
                conflicts += 1
                continue
            try:
                publish(temp, candidate)
                return CopyResult(candidate, "copied", source_hash)
            except FileExistsError:
                # A competing process won; inspect the same candidate again.
                continue
        raise OSError(f"Too many filename conflicts: {desired}")
    finally:
        temp.unlink(missing_ok=True)


def write_report(path: Path, content: str) -> None:
    reject_links(path.absolute())
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, filename = tempfile.mkstemp(prefix=".photocatalog-report-", dir=path.parent)
    temp = Path(filename)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        publish(temp, path)
    finally:
        temp.unlink(missing_ok=True)
