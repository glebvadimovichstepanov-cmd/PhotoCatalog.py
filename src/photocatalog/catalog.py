"""Catalog orchestration with bounded batches and structured outcomes."""

import json
import logging
import os
import tempfile
import zipfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path

from .archives import Limits, extract, members
from .metadata import MEDIA_EXTENSIONS, read_date
from .storage import copy_verified, is_link, target_path, validate_roots

LOG = logging.getLogger(__name__)


@dataclass(frozen=True)
class Config:
    source: Path
    destination: Path
    workers: int = 4
    batch_size: int = 50
    dry_run: bool = False
    extract_zips: bool = True
    fast_video: bool = False
    library: str | None = None
    limits: Limits = field(default_factory=Limits)


@dataclass
class Record:
    source: str
    status: str
    target: str = ""
    date: str = ""
    date_source: str = ""
    sha256: str = ""
    message: str = ""


@dataclass
class Summary:
    records: list[Record] = field(default_factory=list)

    @property
    def counts(self) -> dict[str, int]:
        return {
            name: sum(r.status == name for r in self.records)
            for name in ("copied", "duplicate", "planned", "skipped", "error")
        }

    def json(self) -> str:
        return (
            json.dumps(
                {"counts": self.counts, "records": [asdict(r) for r in self.records]},
                ensure_ascii=False,
                indent=2,
            )
            + "\n"
        )


def run(config: Config) -> Summary:
    if not 1 <= config.workers <= 64 or config.batch_size < 1:
        raise ValueError("workers must be 1..64 and batch-size must be positive")
    config.limits.validate()
    source, destination = validate_roots(config.source, config.destination)
    if config.library and not Path(config.library).is_file():
        raise ValueError(f"MediaInfo library does not exist: {config.library}")
    summary = Summary()

    def error(path: str, exc: Exception) -> None:
        LOG.error("%s: %s", path, exc)
        summary.records.append(Record(path, "error", message=str(exc)))

    def process(item: tuple[Path, str]) -> Record:
        path, label = item
        try:
            date = read_date(path, config.fast_video, config.library)
            target = target_path(destination, path.name, date.value)
            if config.dry_run:
                return Record(
                    label,
                    "planned",
                    str(target),
                    date.value.isoformat(),
                    date.source,
                    message=date.warning,
                )
            copied = copy_verified(path, target)
            return Record(
                label,
                copied.status,
                str(copied.target),
                date.value.isoformat(),
                date.source,
                copied.sha256,
                date.warning,
            )
        except Exception as exc:
            return Record(label, "error", message=str(exc))

    with ThreadPoolExecutor(max_workers=config.workers) as pool:
        batch: list[tuple[Path, str]] = []

        def flush() -> None:
            for record in pool.map(process, batch):
                if config.dry_run and record.target:
                    collision = Path(record.target).exists() or any(
                        prior.target == record.target for prior in summary.records
                    )
                    if collision:
                        record.message += (
                            "; Target collision: actual run will verify content "
                            "and skip a duplicate or choose a free name"
                        )
                summary.records.append(record)
                if record.status == "error":
                    LOG.error("%s: %s", record.source, record.message)
                elif record.message:
                    LOG.warning("%s: %s", record.source, record.message)
            batch.clear()

        def enqueue(path: Path, label: str) -> None:
            batch.append((path, label))
            if len(batch) >= config.batch_size:
                flush()

        def archive_job(path: Path) -> None:
            try:
                with zipfile.ZipFile(path) as archive:
                    if config.dry_run:
                        for info, relative in members(archive, config.limits):
                            if (
                                not info.is_dir()
                                and relative.suffix.lower() in MEDIA_EXTENSIONS
                            ):
                                date = datetime(*info.date_time)
                                summary.records.append(
                                    Record(
                                        f"{path}!{info.filename}",
                                        "planned",
                                        str(
                                            target_path(
                                                destination, relative.name, date
                                            )
                                        ),
                                        date.isoformat(),
                                        "zip_mtime",
                                        message=(
                                            "Provisional ZIP date; media metadata "
                                            "and CRC not read in dry-run"
                                        ),
                                    )
                                )
                    else:
                        # Flush before cleanup, including futures using extracted files.
                        with tempfile.TemporaryDirectory(
                            prefix="photocatalog-"
                        ) as folder:
                            paths = extract(archive, Path(folder), config.limits)
                            for extracted in paths:
                                if extracted.suffix.lower() in MEDIA_EXTENSIONS:
                                    relative = extracted.relative_to(folder).as_posix()
                                    label = f"{path}!{relative}"
                                    enqueue(extracted, label)
                            flush()
            except Exception as exc:
                error(str(path), exc)

        def walk_error(exc: OSError) -> None:
            error(str(exc.filename or source), exc)

        for root, directories, filenames in os.walk(source, onerror=walk_error):
            root_path = Path(root)
            for name in list(directories):
                if is_link(root_path / name):
                    directories.remove(name)
                    summary.records.append(
                        Record(
                            str(root_path / name),
                            "skipped",
                            message="Directory link/junction not followed",
                        )
                    )
            for name in sorted(filenames):
                path = root_path / name
                if is_link(path):
                    summary.records.append(
                        Record(str(path), "skipped", message="File link not followed")
                    )
                elif path.suffix.lower() in MEDIA_EXTENSIONS:
                    enqueue(path, str(path))
                elif config.extract_zips and path.suffix.lower() == ".zip":
                    flush()
                    archive_job(path)
        flush()
    return summary
