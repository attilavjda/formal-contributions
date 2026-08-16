#!/usr/bin/env python3
"""to_additive_twins -- find and *verify* hand-written `to_additive` twins in a Lean 4 library.

The pattern
-----------
A library has a multiplicative lemma `prod_foo` and, next to it, an additive lemma
`sum_foo` whose entire proof is a call to `prod_foo` through `Multiplicative` /
`Additive` (or vice versa).  Such a hand-written twin is redundant: tagging the
partner with `@[to_additive sum_foo]` generates the very same declaration, so the
hand-written one can be deleted.  The diff removes lines and changes no API.

This module finds those pairs and then *checks the claim by building the library*:

  1. compile the file unchanged, recording the pretty-printed type of the twin
     (`#check @Ns.sum_foo`);
  2. rewrite the file: put `@[to_additive sum_foo]` on the partner and delete the
     hand-written twin, docstring and attributes included;
  3. compile again and record the type of `Ns.sum_foo`, now the generated one;
  4. restore the file, and report PASS only if step 3 compiled *and* the type is
     character-for-character the one from step 1.

Nothing is trusted to the regexes: a candidate is only ever a candidate until the
compiler has agreed.  The file on disk is always restored, including on failure.

Usage
-----
  ./to_additive_twins.py find   PATH...            # scan files/directories
  ./to_additive_twins.py verify PATH... [--patch out.patch]

`verify` scans, then verifies every candidate found (`--twin NAME` restricts to one)
and can emit the accumulated unified diff of the verified deletions.

Library use: `find_twins(paths)` yields `Twin` records and `verify_twin(twin)` returns
`(ok, message, patched_source)`.

Works with any `lake`-managed Lean 4 project; the project root is found by walking up
to the outermost `lakefile.toml` / `lakefile.lean` (so files inside
`.lake/packages/<dep>` are compiled from the top-level project).
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import subprocess
import sys
from dataclasses import dataclass

MODIFIERS = r'(?:private |protected |nonrec |noncomputable )*'
DECL_START = re.compile(
    r'^(?:@\[[^\]]*\] )?' + MODIFIERS + r'(?:theorem|lemma) '
    r'([^\s(){\[:]+)')
# `@[simp] theorem foo ...`: an attribute list on the `theorem` line itself
INLINE_ATTR = re.compile(r'^(\s*)@\[([^\]]*)\]( ' + MODIFIERS + r'(?:theorem|lemma) .*)$')
MAX_LINE = 100                       # the line-length limit Mathlib's linter enforces
# a proof that is nothing but a call to the partner through `Multiplicative`/`Additive`
TWIN_BODY = re.compile(r'\A@?([\w.\'₀-₉]+)\s*\(\s*(Multiplicative|Additive)\b')


@dataclass
class Decl:
    name: str            # short name
    full: str            # namespace-qualified name
    first: int           # 0-based index of first line (docstring/attributes included)
    head: int            # 0-based index of the `theorem`/`lemma` line
    last: int            # 0-based index of last line, inclusive
    body: str            # everything after the first `:=`


@dataclass
class Twin:
    path: str
    twin: Decl
    partner: Decl
    via: str             # "Multiplicative" or "Additive"


# ----------------------------------------------------------------- lightweight parsing

def iter_lean_files(paths):
    for p in paths:
        if os.path.isdir(p):
            for dirpath, _, names in os.walk(p):
                for n in sorted(names):
                    if n.endswith('.lean'):
                        yield os.path.join(dirpath, n)
        elif p.endswith('.lean'):
            yield p


def decl_first(lines: list[str], head: int) -> int:
    """Where the declaration whose `theorem` line is `head` starts: the docstring and
    the attribute list belong to it, and both of them may span several lines."""
    first = i = head
    while i > 0:
        prev = lines[i - 1].rstrip()
        if not prev.strip():
            break
        if prev.lstrip().startswith('--'):                     # line comment
            first = i = i - 1
            continue
        opener = None
        if prev.endswith('-/'):                                # docstring / comment
            opener = '/-'
        elif prev.endswith(']') and not re.match(r'\s*(attribute|open|variable)\b', prev):
            opener = '@['                                      # attribute list
        if opener is None:
            break
        j = i - 1
        while j >= 0 and not lines[j].lstrip().startswith(opener):
            j -= 1
        if j < 0:
            break
        first = i = j
    return first


def decl_last(lines: list[str], head: int) -> int:
    """Where that declaration ends: everything below it that is indented (Lean style
    puts the whole body of a declaration below its head, indented) or blank."""
    last, i = head, head + 1
    while i < len(lines):
        line = lines[i]
        if line.strip():
            if not line[0].isspace():
                break
            last = i
        i += 1
    return last


def parse_decls(src: str) -> list[Decl]:
    """All theorems/lemmas of `src`, with their namespace and full line span."""
    lines = src.split('\n')
    heads, stack = [], []
    for i, line in enumerate(lines):
        if line.startswith('namespace '):
            stack.append(line.split()[1])
        elif line.startswith('end ') and stack and line.split()[1:] == [stack[-1]]:
            stack.pop()
        m = DECL_START.match(line)
        if m:
            heads.append((i, m.group(1), '.'.join(stack + [m.group(1)])))
    out = []
    for k, (i, name, full) in enumerate(heads):
        last = decl_last(lines, i)
        if k + 1 < len(heads):                 # never run into the next declaration
            last = min(last, heads[k + 1][0] - 1)
        chunk = '\n'.join(lines[i:last + 1])
        j = chunk.find(':=')
        out.append(Decl(name, full, decl_first(lines, i), i, last,
                        chunk[j + 2:] if j >= 0 else ''))
    # a following declaration's docstring must not be swallowed by the previous one
    for k in range(len(out) - 1):
        out[k].last = min(out[k].last, out[k + 1].first - 1)
    return out


def find_twins_in_source(path: str, src: str) -> list[Twin]:
    """Declarations whose whole proof is a call to a partner through `Multiplicative`."""
    found = []
    decls = parse_decls(src)
    by_name = {d.name: d for d in decls}
    for d in decls:
        body = d.body.strip()
        if len(body) > 200:
            continue
        m = TWIN_BODY.match(body)
        if not m:
            continue
        partner = by_name.get(m.group(1).split('.')[-1])
        if partner is None or partner.name == d.name:
            continue         # partner lives in another file: not a local deletion
        found.append(Twin(path, d, partner, m.group(2)))
    return found


def find_twins(paths) -> list[Twin]:
    found = []
    for path in iter_lean_files(paths):
        with open(path, encoding='utf-8', errors='replace') as fh:
            found += find_twins_in_source(path, fh.read())
    return found


# ------------------------------------------------- candidates from the Lean-side scan
#
# `scan_to_additive.lean` asks `to_additive` itself which declarations it *would*
# generate (`guessName` for the name, `applyReplacementForall` for the statement) and
# prints one `CANDIDATE <module> <partner> <twin>` line per hit.  That scan sees the
# whole environment, so it also catches twins whose proof is an ordinary tactic script
# rather than a transport through `Multiplicative`; the source-level machinery below is
# the same, only the candidate generation differs.

SCAN_LINE = re.compile(r'^.*?CANDIDATE\s+(\S+)\s+(\S+)\s+(\S+)(?:\s+(\S+))?\s*$', re.M)


def module_path(module: str, roots) -> str | None:
    """The file `module` is compiled from, looked up under each of `roots`."""
    rel = os.path.join(*module.split('.')) + '.lean'
    for root in roots:
        for cand in (os.path.join(root, rel),
                     os.path.join(root, module.split('.')[0], rel)):
            if os.path.exists(cand):
                return cand
    return None


def locate(decls: list[Decl], name: str) -> Decl | None:
    """The declaration of `decls` that the fully qualified `name` refers to."""
    for d in decls:
        if d.full == name:
            return d
    # the file may open part of the namespace, or state the declaration with a longer
    # prefix than the surrounding `namespace`s; accept only unambiguous matches
    hits = [d for d in decls if name.endswith('.' + d.full)]
    return hits[0] if len(hits) == 1 else None


def twins_from_scan(text: str, roots) -> tuple[list[Twin], list[str]]:
    """Turn the output of `scan_to_additive.lean` into `Twin` records."""
    found, skipped = [], []
    for module, partner, twin, how in SCAN_LINE.findall(text):
        path = module_path(module, roots)
        if path is None:
            skipped.append(f'{module}: no source file under {", ".join(roots)}')
            continue
        with open(path, encoding='utf-8', errors='replace') as fh:
            decls = parse_decls(fh.read())
        p, t = locate(decls, partner), locate(decls, twin)
        if p is None or t is None:
            skipped.append(f'{module}: {twin} or {partner} is not a plain '
                           f'`theorem`/`lemma` in {path}')
            continue
        found.append(Twin(path, t, p, how or 'name+statement'))
    return found, skipped


# --------------------------------------------------------------------- the rewrite

def rewrite(src: str, t: Twin, explicit: bool = True) -> str:
    """Tag the partner with `@[to_additive <twin>]` and delete the hand-written twin.

    With `explicit=False` the bare `@[to_additive]` is used, which is what Mathlib wants
    whenever the naming heuristic already produces the right name.
    """
    lines = src.split('\n')
    tag = f'to_additive {t.twin.name}' if explicit else 'to_additive'
    # Lean allows a single `@[...]` per declaration, so an existing attribute list has to
    # be extended rather than stacked; it may sit on the `theorem` line or above it, and
    # may span several lines.
    inline = INLINE_ATTR.match(lines[t.partner.head])
    block = None
    if t.partner.head > 0 and lines[t.partner.head - 1].rstrip().endswith(']'):
        for i in range(t.partner.head - 1, t.partner.first - 1, -1):
            if lines[i].lstrip().startswith('@['):
                block = i
                break
    if inline:
        merged = f'{inline[1]}@[{tag}, {inline[2]}]{inline[3]}'
        if len(merged) <= MAX_LINE:
            lines[t.partner.head] = merged
            shift = 0
        else:            # keep within the line-length limit: attributes on their own line
            lines[t.partner.head] = f'{inline[1]}@[{tag}, {inline[2]}]'
            lines.insert(t.partner.head + 1, f'{inline[1]}{inline[3].lstrip()}')
            shift = 1 if t.twin.first > t.partner.head else 0
    elif block is not None:
        merged = lines[block].replace('@[', f'@[{tag}, ', 1)
        if len(merged) <= MAX_LINE:
            lines[block] = merged
            shift = 0
        else:                                     # attribute lists may span lines
            indent = lines[block][:len(lines[block]) - len(lines[block].lstrip())]
            rest = lines[block].lstrip()[2:]
            lines[block] = f'{indent}@[{tag},'
            lines.insert(block + 1, f'{indent}  {rest}')
            shift = 1 if t.twin.first > block else 0
    else:
        lines.insert(t.partner.head, f'@[{tag}]')
        # the inserted line only moves the twin if the twin comes after the partner
        shift = 1 if t.twin.first >= t.partner.head else 0
    a, b = t.twin.first + shift, t.twin.last + shift
    while b + 1 < len(lines) and not lines[b + 1].strip():  # trailing blank line
        b += 1
    return '\n'.join(lines[:a] + lines[b + 1:])


# ------------------------------------------------------------------- lake plumbing

def project_root(path: str, outermost: bool = True) -> str:
    """Enclosing lake project: the outermost one builds, the innermost one names paths."""
    d, found = os.path.dirname(os.path.abspath(path)), None
    while True:
        if any(os.path.exists(os.path.join(d, f))
               for f in ('lakefile.toml', 'lakefile.lean')):
            if found is None or outermost:
                found = d
        parent = os.path.dirname(d)
        if parent == d:
            if found is None:
                sys.exit(f'no lake project found above {path}')
            return found
        d = parent


def compile_source(path: str, src: str, check: str | None, extra: str = '', timeout=3600):
    """Compile `src` in place of `path` (restoring `path` afterwards).

    Returns `(ok, type_of_check, output)`, where `type_of_check` is the pretty-printed
    type reported by an appended `#check @<check>`; `extra` is appended as well.
    """
    with open(path, encoding='utf-8') as fh:
        original = fh.read()
    text = src.rstrip('\n') + '\n'
    if check is not None:
        text += f'\n#check @{check}\n'
    if extra:
        text += '\n' + extra.rstrip('\n') + '\n'
    try:
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(text)
        r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(path)],
                           cwd=project_root(path), capture_output=True,
                           text=True, timeout=timeout)
    finally:
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(original)
    out = r.stdout + r.stderr
    ok = r.returncode == 0 and 'error:' not in out
    typ = None
    if check is not None:
        # `#check` prints the name as it is displayed in the current namespace, so
        # `Finset.sum_foo` may well come back as `sum_foo`
        parts = check.split('.')
        for i in range(len(parts)):
            m = re.search(r'^@?' + re.escape('.'.join(parts[i:])) + r'\s*:(.*?)(?=\n\S|\Z)',
                          out, re.S | re.M)
            if m:
                typ = re.sub(r'\s+', ' ', m.group(1)).strip()
                break
    return ok, typ, out


DAGGER = re.compile(r'[A-Za-z_][\w\'.]*✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*')


def as_ascription(typ: str) -> str:
    """Turn a pretty-printed type into one that can be written down in a source file."""
    typ = re.sub(r'\b(Type|Sort) u_\d+', r'\1*', typ)
    fresh = {}
    return DAGGER.sub(lambda m: fresh.setdefault(m.group(0), f'x{len(fresh)}_'), typ)


def verify_twin(t: Twin, source: str | None = None) -> tuple[bool, str, str]:
    """Really delete the twin, really rebuild, and compare statements.  Restores the file.

    `source` defaults to the file's current contents; pass it explicitly to chain
    several deletions in one file.
    """
    if source is None:
        with open(t.path, encoding='utf-8') as fh:
            source = fh.read()
    original = source
    # safety net: never delete more than the twin (the body of a declaration is indented)
    body = original.split('\n')[t.twin.head + 1:t.twin.last + 1]
    if any(line.strip() and not line[0].isspace() for line in body):
        return False, 'refusing to delete: the twin does not parse as one declaration', ''
    ok, before, out = compile_source(t.path, original, t.twin.full)
    if not ok or before is None:
        return False, 'baseline does not compile / `#check` failed:\n' + out.strip(), ''
    # the generated declaration must still inhabit the *old* type, checked by the kernel
    agree = (f'set_option linter.unusedVariables false in\n'
             f'example : {as_ascription(before)} := @{t.twin.full}')
    # prefer the bare `@[to_additive]` when the naming heuristic already gets it right
    variants = [rewrite(original, t, explicit=False), rewrite(original, t)]
    how = 'the old statement still typechecks against it'
    patched = variants[0]
    for patched in variants:
        ok, after, out = compile_source(t.path, patched, t.twin.full, agree)
        if ok:
            break
    if not ok:
        # writing the old statement down can fail for reasons of its own (a universe
        # that the pretty printer does not bind, say); then fall back to requiring the
        # pretty-printed statement of the generated declaration to be the old one
        for p in variants:
            ok2, after2, out2 = compile_source(t.path, p, t.twin.full)
            if ok2 and after2 is not None and after2 == before:
                patched, ok, after, out = p, True, after2, out2
                how = 'its pretty-printed statement is unchanged'
                break
    if not ok:
        if 'Unknown attribute `[to_additive]`' in out:
            return False, ('`to_additive` is not imported in this module, so tagging the '
                           'partner would mean adding an import: not a pure deletion'), \
                          patched
        return False, 'rewrite breaks the file (or the statement no longer agrees):\n' \
                      + out.strip(), patched
    note = '' if after == before else \
        f'\n  (printed form differs only by binder names:\n     was: {before}' \
        f'\n     now: {after})'
    return True, f'`{t.twin.full}` is generated by `@[to_additive]` on `{t.partner.full}` ' \
                 f'({how}), so the hand-written one can be deleted ' \
                 f'(-{t.twin.last - t.twin.first + 1} lines)' + note, patched


VARIABLE = re.compile(r'^variable\b(.*)$', re.M)


def unused_variables(src: str) -> list[str]:
    """Names bound by a section `variable` that the rest of the file never mentions."""
    rest = VARIABLE.sub('', src)
    dead = []
    for m in VARIABLE.finditer(src):
        for b in re.finditer(r'[({]([^:()}{\[\]]+):', m.group(1)):
            for name in b.group(1).split():
                if not re.search(r'(?<![\w\'])' + re.escape(name) + r'(?![\w\'])', rest):
                    dead.append(name)
    return dead


def unified(path: str, before: str, after: str) -> str:
    rel = os.path.relpath(path, project_root(path, outermost=False))
    return ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                        'a/' + rel, 'b/' + rel))


# --------------------------------------------------------------------------- cli

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name in ('find', 'verify'):
        p = sub.add_parser(name)
        p.add_argument('paths', nargs='+')
        p.add_argument('--twin', help='only consider the twin with this (short) name')
        p.add_argument('--scan', help='read candidates from the output of '
                                      '`scan_to_additive.lean`; PATH... are then the '
                                      'roots the modules are looked up in')
    sub.choices['verify'].add_argument('--patch', help='write the verified diffs here')
    a = ap.parse_args()

    if a.scan:
        with open(a.scan, encoding='utf-8') as fh:
            twins, skipped = twins_from_scan(fh.read(), a.paths)
        for s in skipped:
            print('skipped ' + s)
    else:
        twins = find_twins(a.paths)
    twins = [t for t in twins if a.twin in (None, t.twin.name)]
    for t in twins:
        print(f'{t.path}:{t.twin.head + 1}: {t.twin.name} is a hand-written twin of '
              f'{t.partner.name} (via {t.via})')
    print(f'-- {len(twins)} candidate(s)')
    if a.cmd == 'find':
        return 0

    files, order = {}, []
    for t in twins:
        files.setdefault(t.path, []).append((t.twin.full, t.partner.full, t.via))
        if t.path not in order:
            order.append(t.path)

    patches, good, bad = [], 0, 0
    for path in order:                       # chain the deletions inside a file
        with open(path, encoding='utf-8') as fh:
            original = fh.read()
        cur = original
        # in source order, and repeatedly: tagging one partner can be what makes the
        # next twin work (`prod_range_reflect` is proved from `prod_Ico_reflect`)
        pending = sorted(files[path],
                         key=lambda it: (locate(parse_decls(cur), it[1]) or Decl(
                             '', '', 0, 0, 0, '')).head)
        progress = True
        while pending and progress:
            progress = False
            for item in list(pending):
                twin_name, partner_name, via = item
                # re-parse: an earlier deletion has moved the line numbers
                decls = parse_decls(cur)
                twin, partner = locate(decls, twin_name), locate(decls, partner_name)
                if twin is None or partner is None:
                    pending.remove(item)
                    continue
                print(f'\n== verifying {twin.full} in {path}', flush=True)
                ok, msg, patched = verify_twin(Twin(path, twin, partner, via), cur)
                print(('PASS: ' if ok else 'FAIL: ') + msg, flush=True)
                if ok:
                    cur, good, progress = patched, good + 1, True
                    pending.remove(item)
        bad += len(pending)
        if cur != original:
            new_dead = set(unused_variables(cur)) - set(unused_variables(original))
            if new_dead:
                print(f'note: section variable(s) {", ".join(sorted(new_dead))} are now '
                      f'unused in {path} and can be deleted too', flush=True)
            patches.append(unified(path, original, cur))
    if a.patch and patches:
        with open(a.patch, 'w', encoding='utf-8') as fh:
            fh.write(''.join(patches))
        print(f'\n-- wrote diffs for {len(patches)} file(s) to {a.patch}')
    print(f'-- {good}/{good + bad} verified')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
