#!/usr/bin/env python3
"""
Lint Idris source files for common issues.

This script scans the current directory and its subdirectories for Idris (.idr)
files and checks them for trailing whitespace and missing trailing newlines.
"""

import os
import sys


def _lint_file(path: str) -> bool:
    """
    Check a single Idris file.
    """
    ok = True
    with open(path, encoding="utf-8") as f:
        for line_no, line in enumerate(f.readlines()):
            line_without_newline = line.rstrip("\r\n")
            if line_without_newline == line:
                print(f"No trailing newline in {path}")
                ok = False
                continue
            if line_without_newline.endswith(" "):
                print(f"Trailing whitespace in {path}:{line_no}")
                ok = False
                continue
    return ok


def main() -> None:
    """Scan the directory tree and lint all found Idris files."""
    ok = True
    count = 0

    for dirpath, _, filenames in os.walk("."):
        for filename in filenames:
            if not filename.endswith(".idr"):
                continue
            count += 1
            assert dirpath.startswith("./")
            full = f"{dirpath[2:]}/{filename}"
            if not _lint_file(full):
                ok = False

    # Sanity check
    assert count

    if ok:
        print(f"{count} *.idr files are OK")

    sys.exit(int(not ok))


if __name__ == "__main__":
    main()
