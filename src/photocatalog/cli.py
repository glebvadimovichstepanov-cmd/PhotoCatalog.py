"""CLI: arguments override environment; validation precedes catalog IO."""

import argparse
import logging
import os
import sys
from pathlib import Path

from .archives import Limits
from .catalog import Config, run
from .metadata import mediainfo_status
from .storage import reject_links, write_report


def positive(value: str) -> int:
    try:
        result = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("Expected a positive integer") from exc
    if result < 1:
        raise argparse.ArgumentTypeError("Expected a positive integer")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="PhotoCatalog: verified media copies")
    env = os.environ
    parser.add_argument("source", nargs="?", default=env.get("PHOTOCATALOG_SOURCE"))
    parser.add_argument(
        "destination", nargs="?", default=env.get("PHOTOCATALOG_DESTINATION")
    )
    parser.add_argument("-i", "--interactive", action="store_true")
    parser.add_argument(
        "-w", "--workers", type=positive, default=env.get("PHOTOCATALOG_WORKERS", "4")
    )
    parser.add_argument(
        "-b",
        "--batch-size",
        type=positive,
        default=env.get("PHOTOCATALOG_BATCH_SIZE", "50"),
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--fast-video", action="store_true")
    parser.add_argument("--no-fast-video", action="store_true")
    parser.add_argument("--no-extract-zips", action="store_true")
    parser.add_argument(
        "--mediainfo-lib", default=env.get("PHOTOCATALOG_MEDIAINFO_LIB")
    )
    parser.add_argument("--check-mediainfo", action="store_true")
    parser.add_argument(
        "--zip-max-files",
        type=positive,
        default=env.get("PHOTOCATALOG_ZIP_MAX_FILES", "10000"),
    )
    parser.add_argument(
        "--zip-max-bytes",
        type=positive,
        default=env.get("PHOTOCATALOG_ZIP_MAX_BYTES", str(10 * 1024**3)),
    )
    parser.add_argument(
        "--zip-max-ratio",
        type=positive,
        default=env.get("PHOTOCATALOG_ZIP_MAX_RATIO", "1000"),
    )
    parser.add_argument(
        "--report", type=Path, help="New JSON report file; never replaces existing"
    )
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.WARNING,
        format="%(levelname)s: %(message)s",
    )
    try:
        if args.check_mediainfo:
            ok, message = mediainfo_status(args.mediainfo_lib)
            print(message)
            return 0 if ok else 1
        if args.interactive:
            args.source = input("Source directory: ").strip()
            args.destination = input("Destination directory: ").strip()
            args.dry_run = input("Dry run? [Y/n]: ").strip().lower() not in {"n", "no"}
        if not args.source or not args.destination:
            parser.error("source and destination are required (or use --interactive)")
        if args.workers > 64:
            parser.error("--workers must be between 1 and 64")
        if args.dry_run and args.report:
            parser.error("--report writes a file and cannot be used with --dry-run")
        if args.report:
            reject_links(args.report.absolute())
            if args.report.exists():
                parser.error(f"Report already exists: {args.report}")
            resolved_report = args.report.resolve()
            if resolved_report.is_relative_to(Path(args.source).resolve()):
                parser.error("Report must be outside the source tree")
        config = Config(
            Path(args.source),
            Path(args.destination),
            args.workers,
            args.batch_size,
            args.dry_run,
            not args.no_extract_zips,
            args.fast_video and not args.no_fast_video,
            args.mediainfo_lib,
            Limits(args.zip_max_files, args.zip_max_bytes, args.zip_max_ratio),
        )
        summary = run(config)
        if args.dry_run:
            print(summary.json(), end="")
        else:
            print(" ".join(f"{key}={value}" for key, value in summary.counts.items()))
        if args.report:
            write_report(args.report, summary.json())
        if summary.cancelled:
            return 130
        return 1 if summary.counts["error"] else 0
    except KeyboardInterrupt:
        print(
            "Interrupted; completed copies retained. Re-run to resume.", file=sys.stderr
        )
        return 130
    except EOFError:
        print("Interactive input ended unexpectedly.", file=sys.stderr)
        return 2
    except ValueError as exc:
        print(f"Invalid configuration: {exc}", file=sys.stderr)
        return 2
    except Exception as exc:
        logging.error("Catalog failed: %s", exc, exc_info=args.verbose)
        return 1
