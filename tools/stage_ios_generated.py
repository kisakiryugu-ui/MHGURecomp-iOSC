#!/usr/bin/env python3
"""Stage `make gen` output for the iOS build workflow."""

import argparse
import hashlib
from pathlib import Path
import re
import shutil
import stat
import tempfile
from zipfile import BadZipFile, ZipFile


# Same input and newline normalization as GEN_SRCS and GEN_ID in the Makefile.
GEN_SOURCES = (
    "tools/gen.py",
    "tools/lifter.py",
    "tools/neon.py",
    "tools/nso.py",
    "runtime/hle/hle_symbols.txt",
)
MEMBER = re.compile(r"generated/(?:(main|sdk)/(?:\1_[0-9]+\.c|\1_table\.c|undetected_tables\.txt)|gen\.id)")
DIRECTORIES = {"generated/", "generated/main/", "generated/sdk/"}


def verify_generated(repo, generated):
    digest = hashlib.sha256()
    for path in GEN_SOURCES:
        digest.update((repo / path).read_bytes().replace(b"\r", b""))
    expected = digest.hexdigest()[:16]
    stamp = generated / "gen.id"
    if not stamp.is_file():
        raise ValueError("Missing generated/gen.id. Run make gen or supply the private release tag.")
    if stamp.read_text(encoding="ascii").strip() != expected:
        raise ValueError("Generated code is from a different recompiler revision. Rerun make gen on this branch.")
    for part in ("main", "sdk"):
        for name in (f"{part}_000.c", f"{part}_table.c"):
            source = generated / part / name
            if not source.is_file() or not source.stat().st_size:
                raise ValueError(f"Missing or empty generated source: generated/{part}/{name}")


def stage_archive(repo, archive):
    if (repo / "generated").exists():
        raise ValueError("A generated/ directory already exists. Build with it or move it before staging a ZIP.")
    with tempfile.TemporaryDirectory(dir=repo, prefix=".ios-generated-") as temporary:
        staging = Path(temporary)
        entries = set()
        with ZipFile(archive) as source:
            for entry in source.infolist():
                name = entry.filename
                if stat.S_ISLNK(entry.external_attr >> 16) or name in entries:
                    raise ValueError(f"Invalid archive entry: {name!r}")
                entries.add(name)
                if entry.is_dir() and name in DIRECTORIES:
                    continue
                if not MEMBER.fullmatch(name):
                    raise ValueError(f"Unexpected archive entry: {name!r}. Zip the generated/ folder itself.")
                dest = staging / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                with source.open(entry) as reader, dest.open("xb") as writer:
                    shutil.copyfileobj(reader, writer)
        verify_generated(repo, staging / "generated")
        (staging / "generated").rename(repo / "generated")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path, help="Optional private mhgu-generated.zip")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    try:
        if args.archive:
            stage_archive(repo, args.archive)
        else:
            verify_generated(repo, repo / "generated")
    except (OSError, ValueError, BadZipFile) as error:
        parser.exit(1, f"Build inputs: {error}\n")
    print("Verified generated/ against this checkout's recompiler revision.")


if __name__ == "__main__":
    main()
