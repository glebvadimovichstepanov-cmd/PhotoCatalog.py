"""Metadata adapters. Optional video support never blocks CLI startup."""

import logging
import re
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from threading import Lock

from PIL import Image

LOG = logging.getLogger(__name__)
VIDEO_LOCK = Lock()
IMAGE_EXTENSIONS = frozenset(
    {
        ".jpg",
        ".jpeg",
        ".png",
        ".tif",
        ".tiff",
        ".bmp",
        ".gif",
        ".webp",
        ".heic",
        ".heif",
        ".dng",
        ".cr2",
        ".nef",
        ".arw",
    }
)
VIDEO_EXTENSIONS = frozenset(
    {
        ".mp4",
        ".mov",
        ".avi",
        ".mkv",
        ".m4v",
        ".3gp",
        ".mts",
        ".m2ts",
        ".wmv",
        ".flv",
    }
)
MEDIA_EXTENSIONS = IMAGE_EXTENSIONS | VIDEO_EXTENSIONS


@dataclass(frozen=True)
class DateInfo:
    value: datetime
    source: str
    warning: str = ""


def parse_date(value: object) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip().rstrip("\x00")
    text = re.sub(r"^(UTC|GMT)\s+", "", text, flags=re.I)
    # MediaInfo UTC prefix means an explicit UTC offset.
    if value.strip().upper().startswith(("UTC ", "GMT ")):
        if not re.search(r"(Z|[+-]\d\d:?\d\d)$", text):
            text += "+00:00"
    text = re.sub(r"\s+(UTC|GMT)$", "+00:00", text, flags=re.I)
    text = re.sub(r"^(\d{4})[:/](\d{2})[:/](\d{2})", r"\1-\2-\3", text)
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        return None


def mediainfo_status(library: str | None = None) -> tuple[bool, str]:
    try:
        from pymediainfo import MediaInfo

        if MediaInfo.can_parse(library_file=library):
            return True, "MediaInfo is available"
        return False, "MediaInfo library could not be loaded"
    except Exception as exc:
        return False, f"MediaInfo unavailable: {exc}"


def image_date(path: Path) -> datetime | None:
    with Image.open(path) as image:
        exif = image.getexif()
        original = exif.get_ifd(34665) if 34665 in exif else {}
        for tag, subsecond, offset in (
            (36867, 37521, 36881),
            (36868, 37522, 36882),
            (306, 37520, 36880),
        ):
            value = original.get(tag, exif.get(tag))
            result = parse_date(value)
            if result is None:
                continue
            fraction = str(original.get(subsecond, exif.get(subsecond, ""))).strip()
            if fraction.isdigit():
                result = result.replace(microsecond=int((fraction + "000000")[:6]))
            zone = original.get(offset, exif.get(offset))
            if isinstance(zone, str) and re.fullmatch(r"[+-]\d{2}:\d{2}", zone):
                zoned = parse_date(result.isoformat() + zone)
                if zoned is not None:
                    result = zoned
            return result
    return None


def video_date(path: Path, library: str | None) -> datetime | None:
    from pymediainfo import MediaInfo

    # libmediainfo options may be shared across threads: serialize this adapter.
    with VIDEO_LOCK:
        media = MediaInfo.parse(str(path), library_file=library)
    for field in ("recorded_date", "encoded_date", "tagged_date", "file_created_date"):
        for track in media.tracks:
            if track.track_type == "General":
                result = parse_date(getattr(track, field, None))
                if result is not None:
                    return result
    return None


def read_date(
    path: Path, fast_video: bool = False, library: str | None = None
) -> DateInfo:
    warning = ""
    try:
        if path.suffix.lower() in IMAGE_EXTENSIONS:
            result = image_date(path)
            source = "exif"
        elif fast_video:
            result, source = None, "mtime"
            warning = "Video metadata analysis disabled"
        else:
            result = video_date(path, library)
            source = "video"
        if result is not None:
            return DateInfo(result, source)
        warning = warning or "No usable recording date; using modification time"
    except Exception as exc:
        warning = f"Metadata unavailable ({exc}); using modification time"
    # Missing/unreadable source is an error, never a fabricated current date.
    return DateInfo(datetime.fromtimestamp(path.stat().st_mtime), "mtime", warning)
