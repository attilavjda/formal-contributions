#!/usr/bin/env python3
"""deletion_scout -- find and verify *pure deletion* opportunities in a Lean 4 library.

The heuristics below only ever *propose* a deletion; nothing is trusted until the
`verify` / `prune-simp` sub-commands have actually removed the text and rebuilt the
file with `lake env lean`.  The file is always restored afterwards.

Sub-commands
------------
  scan-twins  PATH...   hand-written `to_additive`/`to_multiplicative` twins:
                        a declaration whose whole proof is a call to its partner
                        through `Multiplicative`/`Additive`.  Such a declaration can
                        usually be deleted and replaced by `@[to_additive]` on the
                        partner (net line decrease, identical generated statement).
                        This scan (and the rewrite that verifies it by rebuilding) now
                        lives in the standalone module `to_additive_twins.py`; use
                        `to_additive_twins.py verify` to actually check a candidate.
  scan-dupes  PATH...   pairs of declarations with a syntactically identical
                        statement (candidate duplicate lemmas).
  scan-hyps   PATH...   named hypotheses `(h... : ...)` that occur nowhere else in
                        their declaration (candidate dead hypotheses).
  verify      FILE      remove a line range (--drop A-B) and/or append a check
                        snippet (--check "..."), rebuild, restore, report.
  prune-simp  FILE      brute force: drop each argument of each `simp [...]`-style
                        call in turn, rebuild, and report the ones that were not
                        needed.

Every sub-command works on any Lean 4 project managed by `lake`; the project root is
detected by walking up from the file to the nearest `lakefile.toml`/`lakefile.lean`.

Examples
--------
  ./deletion_scout.py scan-twins .lake/packages/mathlib/Mathlib
  ./deletion_scout.py prune-simp .lake/packages/mathlib/Mathlib/Data/Nat/Choose/Sum.lean
  ./deletion_scout.py verify .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Intervals.lean \
      --drop 151-153 --check '#check @Finset.sum_Ico_reflect'
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

DECL = r'\n(?:@\[[^\]]*\]\s*\n)?(?:private |protected |nonrec |)(?:theorem|lemma) '


def lean_files(paths):
    for p in paths:
        if os.path.isdir(p):
            for dp, _, fns in os.walk(p):
                for fn in sorted(fns):
                    if fn.endswith('.lean'):
                        yield os.path.join(dp, fn)
        elif p.endswith('.lean'):
            yield p


def read(path):
    with open(path, encoding='utf-8', errors='replace') as fh:
        return fh.read()


def decls(src):
    """Yield (line, name, statement, body) for every theorem/lemma in `src`."""
    for m in re.finditer(DECL + r'([^\s(){\[:]+)', src):
        start = m.start() + 1
        end = len(src)
        nxt = re.search(DECL, src[m.end():])
        if nxt:
            end = m.end() + nxt.start() + 1
        chunk = src[start:end]
        i = chunk.find(':=')
        if i < 0:
            continue
        yield src[:start].count('\n') + 1, m.group(1), chunk[:i], chunk[i + 2:]


def outer_root(path):
    """Outermost lake project containing `path` (deps live in `.lake/packages`)."""
    d = os.path.dirname(os.path.abspath(path))
    found = None
    while True:
        if os.path.exists(os.path.join(d, 'lakefile.toml')) or \
           os.path.exists(os.path.join(d, 'lakefile.lean')):
            found = d
        parent = os.path.dirname(d)
        if parent == d:
            return found
        d = parent


def compile_file(path, timeout=3600):
    root = outer_root(path)
    if root is None:
        sys.exit(f'no lake project found above {path}')
    r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(path)],
                       cwd=root, capture_output=True, text=True, timeout=timeout)
    out = r.stdout + r.stderr
    return (r.returncode == 0 and 'error' not in out), out


# --------------------------------------------------------------------------- scans

def scan_twins(paths):
    """Delegate to the standalone module, which can also verify what it finds."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from to_additive_twins import find_twins
    twins = find_twins(paths)
    for t in twins:
        print(f'{t.path}:{t.twin.head + 1}: {t.twin.name} is a hand-written twin of '
              f'{t.partner.name} (via {t.via}) -- try `@[to_additive]` on '
              f'{t.partner.name}')
    print(f'-- {len(twins)} candidate(s)')


def scan_dupes(paths):
    from collections import defaultdict
    seen = defaultdict(list)
    for f in lean_files(paths):
        src = read(f)
        for line, name, stmt, _body in decls(src):
            key = re.sub(r'\s+', ' ', stmt).strip()
            if len(key) < 25:
                continue
            seen[key].append((f, line, name))
    hits = 0
    for key, v in seen.items():
        if len({n for _, _, n in v}) > 1:
            hits += 1
            print(key)
            for f, line, n in v:
                print(f'    {f}:{line}: {n}')
    print(f'-- {hits} candidate group(s)')


AUTO = re.compile(r'\b(simp_all|simpa|rwa|omega|lia|grind|aesop|tauto|assumption|'
                  r'positivity|field_simp|gcongr|decide|norm_num|linarith|nlinarith|'
                  r'exact_mod_cast|solve_by_elim|trivial|apply_rules|order|bound)\b'
                  r'|simp[^\n]*\[\*')


def scan_hyps(paths):
    hits = 0
    for f in lean_files(paths):
        src = read(f)
        for line, name, stmt, body in decls(src):
            if AUTO.search(body):      # tactics that can pick a hypothesis up silently
                continue
            whole = stmt + body
            for m in re.finditer(r'\((h[A-Za-z0-9_\'₀-₉]*)\s*:\s*([^()]*)\)', stmt):
                h, ty = m.group(1), m.group(2)
                if not re.search(r'[≤<=≠∣∈⊆∨∧→¬]|Prop', ty):
                    continue
                uses = re.findall(r'(?<![A-Za-z0-9_\'])' + re.escape(h) +
                                  r'(?![A-Za-z0-9_\'])', whole)
                if len(uses) <= 1:
                    hits += 1
                    print(f'{f}:{line}: {name} never uses ({h} : {ty.strip()})')
    print(f'-- {hits} candidate(s)')


# ---------------------------------------------------------------------- verifiers

def with_restored(path, fn):
    orig = read(path)
    try:
        return fn(orig)
    finally:
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(orig)


def verify(path, drop, check):
    def run(orig):
        ok, out = compile_file(path)
        if not ok:
            print('baseline does NOT compile:\n' + out)
            return 1
        lines = orig.split('\n')
        new = lines
        if drop:
            a, b = (int(x) for x in drop.split('-'))
            new = lines[:a - 1] + lines[b:]
        text = '\n'.join(new)
        if check:
            text += '\n' + check + '\n'
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(text)
        ok, out = compile_file(path)
        print('DELETION IS SAFE' if ok else 'deletion breaks the file')
        if out.strip():
            print(out.strip())
        return 0 if ok else 1
    return with_restored(path, run)


SIMP = re.compile(r'\b(simp only|simp|simpa only|simpa|field_simp|norm_num)\b[^\[\n]{0,20}\[')


def prune_simp(path):
    def run(orig):
        ok, out = compile_file(path)
        if not ok:
            print('baseline does NOT compile:\n' + out)
            return 1
        calls = []
        for m in SIMP.finditer(orig):
            s = m.end() - 1
            depth, i = 0, s
            while i < len(orig):
                if orig[i] == '[':
                    depth += 1
                elif orig[i] == ']':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            inner = orig[s + 1:i]
            if '[' in inner or ']' in inner:
                continue
            calls.append((s + 1, i, inner.split(',')))
        print(f'-- {len(calls)} simp-style call(s) to probe')
        found = 0
        for s, e, parts in calls:
            for k, part in enumerate(parts):
                if part.strip() in ('', '*'):
                    continue
                rest = ','.join(p for j, p in enumerate(parts) if j != k)
                if not rest.strip():
                    continue
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(orig[:s] + rest + orig[e:])
                ok, _ = compile_file(path)
                if ok:
                    found += 1
                    print(f'{path}:{orig[:s].count(chr(10)) + 1}: '
                          f'redundant simp argument `{part.strip()}`')
                    sys.stdout.flush()
        print(f'-- {found} redundant argument(s)')
        return 0
    return with_restored(path, run)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name in ('scan-twins', 'scan-dupes', 'scan-hyps'):
        p = sub.add_parser(name)
        p.add_argument('paths', nargs='+')
    p = sub.add_parser('verify')
    p.add_argument('file')
    p.add_argument('--drop', help='line range A-B to delete (1-based, inclusive)')
    p.add_argument('--check', default='', help='Lean code appended after the deletion')
    p = sub.add_parser('prune-simp')
    p.add_argument('file')
    a = ap.parse_args()
    if a.cmd == 'scan-twins':
        scan_twins(a.paths)
    elif a.cmd == 'scan-dupes':
        scan_dupes(a.paths)
    elif a.cmd == 'scan-hyps':
        scan_hyps(a.paths)
    elif a.cmd == 'verify':
        sys.exit(verify(a.file, a.drop, a.check))
    elif a.cmd == 'prune-simp':
        sys.exit(prune_simp(a.file))


if __name__ == '__main__':
    main()
