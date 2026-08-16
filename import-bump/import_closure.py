#!/usr/bin/env python3
"""Compute (transitive) import closures of Lean modules in a Lean 4 library.

Usage:
    python3 scripts/import_closure.py MOD [MOD ...]           # size of each closure
    python3 scripts/import_closure.py --cost BASE EXTRA [...]  # modules EXTRA adds to BASE's closure

`BASE` and `EXTRA` are module names such as `Mathlib.GroupTheory.GroupAction.Basic`.
The library root is taken from `--root` (default: the Mathlib pinned by this project).
Handles both plain `import X` and the module-system forms `public import X`,
`import all X`, `meta import X`, `private import X`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|meta\s+|protected\s+)*import(?:\s+all)?\s+([A-Za-z_][\w.]*)"
)


def module_path(root: Path, mod: str) -> Path:
    return root / (mod.replace(".", "/") + ".lean")


def direct_imports(root: Path, mod: str) -> list[str]:
    p = module_path(root, mod)
    if not p.exists():
        return []
    out = []
    in_comment = False
    for line in p.read_text().splitlines():
        s = line.strip()
        if in_comment:
            if "-/" in s:
                in_comment = False
            continue
        if s.startswith("/-"):
            if "-/" not in s:
                in_comment = True
            continue
        if not s or s.startswith("--"):
            continue
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
            continue
        if s in ("module", "prelude") or s.startswith("set_option"):
            continue
        break  # first real command: the import block is over
    return out


def closure(root: Path, mods: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(mods)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(direct_imports(root, m))
    return seen


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".lake/packages/mathlib")
    ap.add_argument("--cost", action="store_true",
                    help="first module is the base; report what each other module adds")
    ap.add_argument("--list", action="store_true", help="list the added modules")
    ap.add_argument("--downstream", action="store_true",
                    help="with --cost: also report every module of the library whose own "
                         "closure would grow if the base gained the extra import")
    ap.add_argument("--lib", default="Mathlib",
                    help="top-level directory scanned by --downstream")
    ap.add_argument("mods", nargs="+")
    a = ap.parse_args()
    root = Path(a.root)

    if not a.cost:
        for m in a.mods:
            print(f"{len(closure(root, [m])):6d}  {m}")
        return 0

    base, extras = a.mods[0], a.mods[1:]
    cb = closure(root, [base])
    print(f"base closure |{base}| = {len(cb)}")
    for e in extras:
        ce = closure(root, [e])
        added = ce - cb
        print(f"  + {e}: {len(added)} new module(s)")
        if a.list:
            for m in sorted(added):
                print(f"      {m}")
        if a.downstream:
            memo: dict[str, set[str]] = {}

            def cl(m: str) -> set[str]:
                if m in memo:
                    return memo[m]
                memo[m] = set()  # cycle guard
                s = {m}
                for d in direct_imports(root, m):
                    s |= cl(d)
                memo[m] = s
                return s

            mods = [str(p.relative_to(root)).replace("/", ".")[:-5]
                    for p in (root / a.lib).glob("**/*.lean")]
            dep = [m for m in mods if base in cl(m)]
            aff = [m for m in dep if e not in cl(m)]
            print(f"    downstream: {len(dep)} module(s) import {base} transitively; "
                  f"{len(aff)} of them would gain modules")
            for m in sorted(aff):
                print(f"      +{len(ce - cl(m))}  {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
