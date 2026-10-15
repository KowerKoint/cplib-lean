#!/usr/bin/env python3
"""Expand Cplib imports in a Lean source into one AtCoder submission file."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


IMPORT_RE = re.compile(r"^[ \t]*import[ \t]+(.+?)[ \t]*(?:--.*)?$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


class BundleError(Exception):
    pass


def split_imports(source: str, path: Path) -> tuple[list[str], str]:
    """Return imported modules and source with import commands removed."""
    modules: list[str] = []
    body: list[str] = []
    for line_number, line in enumerate(source.splitlines(keepends=True), 1):
        match = IMPORT_RE.match(line.rstrip("\r\n"))
        if match is None:
            body.append(line)
            continue
        names = match.group(1).split()
        if not names or any(MODULE_RE.fullmatch(name) is None for name in names):
            raise BundleError(f"unsupported import syntax at {path}:{line_number}: {line.rstrip()}")
        modules.extend(names)
    return modules, "".join(body)


def module_path(cplib_root: Path, module: str) -> Path:
    return cplib_root.joinpath(*module.split(".")).with_suffix(".lean")


def bundle(entry: Path, cplib_root: Path) -> str:
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

    output: list[str] = [
        "/- This file is generated. Edit the original sources, not this file. -/\n"
    ]
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
    parser.add_argument("-o", "--output", type=Path, help="output file (default: stdout)")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        result = bundle(args.entry, args.cplib_root)
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
