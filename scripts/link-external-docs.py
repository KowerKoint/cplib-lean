#!/usr/bin/env python3
"""Point doc-gen4 links at declarations outside this library to a hosted site.

`scripts/make-docs.sh` renders pages for the `Cplib` modules only: rendering
every imported module would mean rendering all of `Init`, `Lean` and `Mathlib`,
which is thousands of pages and hours of build time.  doc-gen4 still emits
relative links to those declarations, and without their pages the links 404.

Every such link is rewritten here to point at a site that does host them,
`mathlib4_docs` by default, which covers the core library and `Batteries` as
well as `Mathlib`.  That site tracks Mathlib master rather than the toolchain
this library pins, so a declaration may well have moved to another module since;
keeping the local path would then land the reader on a page the declaration is
no longer on.  Its declaration index is therefore downloaded and each link
resolved by name, which survives the move.  Should the download fail, or a name
be gone upstream, the link falls back to the same path under that site: the page
exists even when the anchor does not, so nothing 404s either way.

A dangling link into `Cplib` itself is a real fault rather than something to
redirect, so it is reported and fails the run.
"""

from __future__ import annotations

import argparse
import posixpath
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from urllib.parse import unquote

DEFAULT_BASE_URL = "https://leanprover-community.github.io/mathlib4_docs"
DECLARATION_DATA = "declarations/declaration-data.bmp"
INTERNAL_ROOT = "Cplib"

HREF_RE = re.compile(r'href="([^"]*)"')
SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
# The index is one flat JSON object mapping a declaration name to its entry,
# whose first field is the link.  Scanning for that pair keeps the 70 MB file
# out of a `json.load`, which would blow it up into gigabytes of `dict`.
ENTRY_RE = re.compile(rb'"((?:[^"\\]|\\.)*)":\{"docLink":"((?:[^"\\]|\\.)*)"')


def is_relative(target: str) -> bool:
    """Is `target` a link this documentation tree has to supply itself?"""
    return bool(target) and not (
        target.startswith(("#", "/", "?")) or SCHEME_RE.match(target)
    )


def load_pages(doc_dir: Path) -> dict[Path, str]:
    return {page: page.read_text(encoding="utf-8") for page in sorted(doc_dir.rglob("*.html"))}


def split_target(doc_dir: Path, page: Path, target: str) -> tuple[str, str] | None:
    """Resolve `target` against `page`, or `None` when it already has a page."""
    path, _, fragment = target.partition("#")
    here = page.parent.relative_to(doc_dir).as_posix()
    resolved = posixpath.normpath(posixpath.join(here, path))
    if resolved.startswith("..") or (doc_dir / resolved).exists():
        return None
    return resolved, fragment


def is_internal(path: str) -> bool:
    return path.split("/", 1)[0].removesuffix(".html") == INTERNAL_ROOT


def fetch_index(url: str, cache: Path | None) -> bytes | None:
    """Return the raw declaration index, or `None` when it cannot be had."""
    if cache is not None and cache.is_file():
        return cache.read_bytes()
    try:
        with urllib.request.urlopen(url) as response:
            data = response.read()
    except (urllib.error.URLError, OSError) as error:
        print(f"link-external-docs.py: warning: cannot read {url}: {error}", file=sys.stderr)
        return None
    if cache is not None:
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(data)
    return data


def resolve_names(names: set[str], url: str, cache: Path | None) -> dict[str, str]:
    """Map each wanted declaration name to its path on the hosting site."""
    data = fetch_index(url, cache)
    if data is None:
        return {}
    wanted = {name.encode("utf-8") for name in names}
    found: dict[str, str] = {}
    for match in ENTRY_RE.finditer(data):
        if match.group(1) in wanted:
            name = match.group(1).decode("utf-8")
            found[name] = match.group(2).decode("utf-8").removeprefix("./")
    return found


def retarget(doc_dir: Path, base_url: str, index_url: str, cache: Path | None) -> int:
    pages = load_pages(doc_dir)

    wanted: set[str] = set()
    dangling: list[str] = []
    for page, text in pages.items():
        for target in HREF_RE.findall(text):
            if not is_relative(target):
                continue
            split = split_target(doc_dir, page, target)
            if split is None:
                continue
            path, fragment = split
            if is_internal(path):
                dangling.append(f"{page.relative_to(doc_dir).as_posix()}: {target}")
            elif fragment:
                wanted.add(unquote(fragment))

    resolved = resolve_names(wanted, index_url, cache) if wanted else {}

    rewritten = 0
    for page, text in pages.items():

        def replace(match: re.Match[str]) -> str:
            nonlocal rewritten
            target = match.group(1)
            if not is_relative(target):
                return match.group(0)
            split = split_target(doc_dir, page, target)
            if split is None:
                return match.group(0)
            path, fragment = split
            if is_internal(path):
                return match.group(0)
            rewritten += 1
            location = resolved.get(unquote(fragment)) if fragment else None
            if location is None:
                location = f"{path}#{fragment}" if fragment else path
            return f'href="{base_url}/{location}"'

        updated = HREF_RE.sub(replace, text)
        if updated != text:
            page.write_text(updated, encoding="utf-8")

    unresolved = len(wanted - resolved.keys())
    print(f"link-external-docs.py: retargeted {rewritten} links to {base_url}")
    print(
        f"link-external-docs.py: resolved {len(resolved)} of {len(wanted)} declaration names"
        + (f", {unresolved} fell back to the module page" if unresolved else "")
    )
    if dangling:
        print(
            f"link-external-docs.py: error: {len(dangling)} dangling {INTERNAL_ROOT} links",
            file=sys.stderr,
        )
        for entry in dangling:
            print(f"  {entry}", file=sys.stderr)
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("doc_dir", type=Path, help="generated documentation root")
    parser.add_argument(
        "--base-url",
        default=DEFAULT_BASE_URL,
        help=f"site hosting the other libraries (default: {DEFAULT_BASE_URL})",
    )
    parser.add_argument(
        "--declaration-data",
        help=f"that site's declaration index (default: <base-url>/{DECLARATION_DATA})",
    )
    parser.add_argument(
        "--cache",
        type=Path,
        help="file to keep the downloaded index in; delete it to refresh",
    )
    args = parser.parse_args()
    if not args.doc_dir.is_dir():
        print(f"link-external-docs.py: error: no such directory: {args.doc_dir}", file=sys.stderr)
        return 1
    base_url = args.base_url.rstrip("/")
    index_url = args.declaration_data or f"{base_url}/{DECLARATION_DATA}"
    return retarget(args.doc_dir, base_url, index_url, args.cache)


if __name__ == "__main__":
    raise SystemExit(main())
