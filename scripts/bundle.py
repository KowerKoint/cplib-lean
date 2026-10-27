#!/usr/bin/env python3
"""Expand Cplib imports in a Lean source into one AtCoder submission file."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


IMPORT_RE = re.compile(r"import[ \t]+(\S+)")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
DEFAULT_SOURCE_URL = "https://github.com/KowerKoint/cplib-lean"


class BundleError(Exception):
    pass


def skip_comment(source: str, start: int, path: Path) -> int:
    """Return the offset just past the comment beginning at `start`."""
    if source.startswith("--", start):
        end = source.find("\n", start)
        return len(source) if end < 0 else end + 1
    depth = 0
    index = start
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif source.startswith("-/", index):
            depth -= 1
            index += 2
            if depth == 0:
                return index
        else:
            index += 1
    line_number = source.count("\n", 0, start) + 1
    raise BundleError(f"unterminated block comment at {path}:{line_number}")


def split_imports(source: str, path: Path) -> tuple[list[str], str]:
    """Return imported modules and source with import commands removed.

    Lean accepts `import` only in the header, ahead of the first real command,
    so the scan stops once one is reached.  Comments are skipped as comments
    rather than matched line by line, which keeps a docstring whose text
    happens to begin with the word `import` from being read as one.
    """
    modules: list[str] = []
    body: list[str] = []
    index = 0
    while index < len(source):
        if source[index].isspace():
            body.append(source[index])
            index += 1
        elif source.startswith("--", index) or source.startswith("/-", index):
            end = skip_comment(source, index, path)
            body.append(source[index:end])
            index = end
        elif (match := IMPORT_RE.match(source, index)) is not None:
            name = match.group(1)
            if MODULE_RE.fullmatch(name) is None:
                line_number = source.count("\n", 0, index) + 1
                raise BundleError(f"unsupported import syntax at {path}:{line_number}: {name}")
            modules.append(name)
            index = match.end()
        else:
            break
    body.append(source[index:])
    return modules, "".join(body)


def module_path(cplib_root: Path, module: str) -> Path:
    return cplib_root.joinpath(*module.split(".")).with_suffix(".lean")


def comment_block(source_url: str, license_text: str | None) -> str:
    contents = [
        "This file is generated. Edit the original sources, not this file.",
        "",
        f"Cplib source: {source_url}",
    ]
    if license_text is not None:
        contents.extend(["", license_text.rstrip()])
    body = "\n".join(contents)
    if "-/" in body:
        raise BundleError("generated header contains the Lean comment terminator '-/'")
    return f"/-\n{body}\n-/\n\n"


def bundle(
    entry: Path,
    cplib_root: Path,
    source_url: str = DEFAULT_SOURCE_URL,
    license_text: str | None = None,
) -> str:
    entry = entry.resolve()
    cplib_root = cplib_root.resolve()
    if not entry.is_file():
        raise BundleError(f"entry file does not exist: {entry}")
    if not (cplib_root / "Cplib.lean").is_file():
        raise BundleError(f"not a Cplib package root: {cplib_root}")

    visited: set[str] = set()
    visiting: list[str] = []
    external_imports: list[str] = []
    external_seen: set[str] = set()
    modules: list[tuple[str, Path, str]] = []

    def remember_external(name: str) -> None:
        if name not in external_seen:
            external_seen.add(name)
            external_imports.append(name)

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in visiting:
            cycle = " -> ".join([*visiting, name])
            raise BundleError(f"cyclic Cplib imports: {cycle}")

        path = module_path(cplib_root, name)
        if not path.is_file():
            raise BundleError(f"cannot find module {name}: expected {path}")

        visiting.append(name)
        imports, body = split_imports(path.read_text(encoding="utf-8"), path)
        for dependency in imports:
            if dependency == "Cplib" or dependency.startswith("Cplib."):
                visit(dependency)
            else:
                remember_external(dependency)
        visiting.pop()
        visited.add(name)
        modules.append((name, path, body))

    entry_imports, entry_body = split_imports(entry.read_text(encoding="utf-8"), entry)
    for name in entry_imports:
        if name == "Cplib" or name.startswith("Cplib."):
            visit(name)
        else:
            remember_external(name)

    output: list[str] = [comment_block(source_url, license_text)]
    if external_imports:
        output.extend(f"import {name}\n" for name in external_imports)
        output.append("\n")

    for name, path, body in modules:
        relative = path.relative_to(cplib_root)
        output.append(f"/- BEGIN {name} ({relative}) -/\n")
        output.append("section\n")
        output.append(body)
        if body and not body.endswith("\n"):
            output.append("\n")
        output.append("end\n")
        output.append(f"/- END {name} -/\n\n")

    output.append(f"/- BEGIN entry ({entry.name}) -/\n")
    output.append(entry_body)
    if entry_body and not entry_body.endswith("\n"):
        output.append("\n")
    output.append("/- END entry -/\n")
    return "".join(output)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entry", type=Path, help="Lean source containing main")
    parser.add_argument(
        "--cplib-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="directory containing Cplib.lean (default: parent of this script)",
    )
    parser.add_argument(
        "--source-url",
        default=DEFAULT_SOURCE_URL,
        help=f"reference URL written into the generated file (default: {DEFAULT_SOURCE_URL})",
    )
    parser.add_argument(
        "--license",
        type=Path,
        help="license file to embed (default: LICENSE under --cplib-root)",
    )
    parser.add_argument(
        "--no-license",
        action="store_true",
        help="do not embed a license notice",
    )
    parser.add_argument("-o", "--output", type=Path, help="output file (default: stdout)")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        license_text = None
        if not args.no_license:
            license_path = args.license or args.cplib_root / "LICENSE"
            license_text = license_path.read_text(encoding="utf-8")
        result = bundle(args.entry, args.cplib_root, args.source_url, license_text)
        if args.output is None:
            sys.stdout.write(result)
        else:
            args.output.write_text(result, encoding="utf-8")
    except (BundleError, OSError) as error:
        print(f"bundle.py: error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
