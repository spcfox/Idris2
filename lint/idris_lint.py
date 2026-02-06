#!/usr/bin/env python3
"""
Lint Idris source files for common issues.

This script scans the current directory and its subdirectories for Idris (.idr)
files and checks them for:
1. Trailing whitespace within lines.
2. Missing trailing newline at the end of file.
3. Too many trailing newlines at the end of file.
4. Invalid UTF-8 encoding in the file.
"""

import os
import sys


def _lint_file(path: str) -> bool:
    """
    Check a single Idris file.
    """
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.readlines()
    except UnicodeDecodeError:
        print(f"Error reading {path}: Not UTF-8")
        return False

    file_ok = True
    trailing_empty_lines = 1

    for line_no, line in enumerate(lines, start=1):
        line_without_newline = line.rstrip("\r\n")
        has_new_line = line_without_newline != line

        if line.isspace():
            trailing_empty_lines += has_new_line
        else:
            trailing_empty_lines = has_new_line

        if line_without_newline.endswith(" "):
            print(f"{path}:{line_no}: Trailing whitespace")
            file_ok = False

    if trailing_empty_lines == 0:
        print(f"{path}: Missing trailing newline")
        return False

    if trailing_empty_lines > 1:
        print(f"{path}: Too many trailing newlines")
        return False

    return file_ok


def main() -> None:
    """Scan the directory tree and lint all found Idris files."""
    checked = 0
    failed = 0

    for dirpath, _, filenames in os.walk("."):
        for filename in filenames:
            if not filename.endswith(".idr"):
                continue

            checked += 1

            if dirpath == ".":
                full = filename
            else:
                full = os.path.join(dirpath, filename)
                if full.startswith("./"):
                    full = full[2:]

            if not _lint_file(full):
                failed += 1

    # Sanity check
    if checked == 0:
        print("Error: No .idr files found", file=sys.stderr)
        sys.exit(2)

    if failed == 0:
        print(f"\n✓ {checked} *.idr files are OK")
        sys.exit(0)
    else:
        print(f"\n✗ Issues found in {failed} files")
        sys.exit(1)


if __name__ == "__main__":
    main()
