# Reproducing the import bump in VS Code, against today's Mathlib

This walks through, step by step, the experiment behind the section *Import cost of homing
`smul_eq_self_of_mem_zpowers` in the stabilizer file* of `CONTRIBUTION.md` — but on a fresh
clone of the **online** `leanprover-community/mathlib4` master rather than the Mathlib this
project pins, and driven from VS Code.

What is being tested:

* moving `smul_eq_self_of_mem_zpowers` out of `Mathlib/GroupTheory/OrderOfElement.lean` and
  into `Mathlib/GroupTheory/GroupAction/Basic.lean`, the file that defines
  `MulAction.stabilizer`, rerouting its proof through the stabilizer subgroup so that a plain
  `@[to_additive]` generates the additive twin `vadd_eq_self_of_mem_zmultiples` instead of it
  being written out by hand;
* the claim that this costs the host file **exactly one extra module** in its import closure
  (`Mathlib.Algebra.Group.Subgroup.ZPowers.Basic`), while the thematically similar
  `Mathlib/GroupTheory/GroupAction/FixedPoints.lean` would cost **eight**.

**Result of the run recorded here** (master commit `97b6a17d7e93a942ab7f7f777bb8fac2af129040`,
15 Aug 2026, toolchain `leanprover/lean4:v4.34.0-rc1`): the claim still holds, the patched
file compiles clean, and a **whole-library `lake build` of patched master succeeds (8724
jobs, no errors, no warnings)**. Raw log: `contribution/master-import-bump.txt`. Patch:
`contribution/master-import-bump-stabilizer.patch`. Checker file:
`contribution/check_import_bump.lean`.

| host file | closure on `8f9d9cf` (pinned) | closure on master `97b6a17` | modules added by the extra import | downstream files that grow |
|---|---|---|---|---|
| `GroupTheory/GroupAction/Basic.lean` | 522 → 523 | 533 → 534 | **1** | 13 (of 2850 dependants), by 1 each |
| `GroupTheory/GroupAction/FixedPoints.lean` | 483 → 491 | 497 → 505 | **8** | 3 (of 1719 dependants), by ≤ 8 |

The two figures are unchanged since the pinned revision; only the absolute closure sizes and
the dependant counts have grown, and `LinearAlgebra.Alternating.DomCoprod` has dropped off
the list of files that would grow (it now reaches `ZPowers/Basic` by another route).

---

## 0. Prerequisites

* **VS Code** with the **`leanprover.lean4`** extension (Extensions view, `Ctrl+Shift+X`,
  search "lean4"). The extension installs and manages `elan`, `lake` and the toolchain.
* **git**, **python3** (3.8+; the measuring script has no dependencies), **curl**.
* About **12 GB** of free disk and **8 GB** of RAM. Step 6 (whole-library build) took
  ~70 minutes on 8 cores; every other step is seconds to minutes.
* The file `scripts/import_closure.py` from this project.

Throughout, `Ctrl+`` ` `` opens the integrated terminal, `Ctrl+P` opens a file by name,
`Ctrl+G` jumps to a line, and `Ctrl+Shift+Enter` opens the Lean **InfoView** (also reachable
from the **∀** menu in the top-right corner of a `.lean` editor).

## 1. Clone Mathlib master

In any terminal:

```bash
git clone https://github.com/leanprover-community/mathlib4.git mathlib-master
cd mathlib-master
git log -1 --format='%H %cd %s'     # record which master you are testing
cat lean-toolchain                  # e.g. leanprover/lean4:v4.34.0-rc1
```

A full clone takes ~2 minutes; `--depth 1` is enough for this experiment and is faster.

## 2. Open the clone in VS Code

**File → Open Folder…** and pick `mathlib-master`. Open the **∀** menu → *Documentation…* is
not needed, but the first time you open a `.lean` file the extension will offer to install
the toolchain named in `lean-toolchain` — accept it (`elan` downloads it once).

Do **not** open a Mathlib file yet: without prebuilt `.olean` files, the language server
would start compiling the library from scratch in the background. Do step 3 first.

## 3. Fetch the prebuilt oleans

In the VS Code terminal (`Ctrl+`` ` ``), from the project root:

```bash
lake exe cache get
```

This downloads the compiled library for exactly this commit (~8700 files, a few minutes on a
fast connection) and decompresses it. When it prints `Decompressed 8709 file(s)` you are
ready. If you cloned a commit for which no cache exists (a very recent master, or a fork),
either check out a slightly older commit or expect a full build.

Sanity check that the editor is happy: `Ctrl+P` → `GroupAction/Basic.lean`. The InfoView
should show *No info found* / no red squiggles, and the file should be ready in seconds
rather than minutes.

## 4. Measure the import cost — before touching anything

Copy `scripts/import_closure.py` from this project into the clone (or refer to it by path)
and run, in the VS Code terminal:

```bash
python3 import_closure.py --root . --cost --list --downstream \
    Mathlib.GroupTheory.GroupAction.Basic \
    Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
```

Expected (on master `97b6a17`):

```
base closure |Mathlib.GroupTheory.GroupAction.Basic| = 533
  + Mathlib.Algebra.Group.Subgroup.ZPowers.Basic: 1 new module(s)
      Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
    downstream: 2850 module(s) import Mathlib.GroupTheory.GroupAction.Basic transitively; 13 of them would gain modules
      +1  Mathlib.CategoryTheory.Action.Concrete
      ...
```

and, for the alternative host file,

```bash
python3 import_closure.py --root . --cost --list --downstream \
    Mathlib.GroupTheory.GroupAction.FixedPoints \
    Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
```

```
base closure |Mathlib.GroupTheory.GroupAction.FixedPoints| = 497
  + Mathlib.Algebra.Group.Subgroup.ZPowers.Basic: 8 new module(s)
      ...
```

This step is purely textual — it reads `import` lines, so it needs no build and takes about a
second. The full output of both commands is in `contribution/master-import-bump.txt`, §1.

*Optional, inside the editor:* Mathlib ships `#min_imports in <command>` (from
`Mathlib.Tactic.MinImports`); typing it above a declaration reports, in the InfoView, the
minimal imports that declaration needs. It answers a related but different question — what a
single declaration requires — whereas the script answers what a *file* would pay.

## 5. Make the edit in VS Code

Either apply the ready-made patch,

```bash
git apply /path/to/contribution/master-import-bump-stabilizer.patch
```

or make the two edits by hand, which is the point of doing this in an editor:

**(a) `Mathlib/GroupTheory/GroupAction/Basic.lean`** — `Ctrl+P`, type
`GroupAction/Basic.lean`. In the import block at the top, add, in alphabetical position right
after `public import Mathlib.Algebra.Group.Subgroup.Map`:

```lean
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
```

Then scroll to the end of `section Stabilizer` (`Ctrl+F` for `end Stabilizer`) and insert,
just before it:

```lean
/-- If `y` fixes `a`, then so does every element of the subgroup generated by `y`. -/
@[to_additive
  /-- If `y` fixes `a`, then so does every element of the subgroup generated by `y`. -/]
theorem _root_.smul_eq_self_of_mem_zpowers {x y : G} (hx : x ∈ Subgroup.zpowers y) {a : α}
    (hs : y • a = a) : x • a = a :=
  mem_stabilizer_iff.1 <| Subgroup.zpowers_le.2 (mem_stabilizer_iff.2 hs) hx
```

`_root_` keeps the name it had before the move (the file is inside `namespace MulAction`);
`G`, `α` and their instances come from the section `variable`s.

> **Important VS Code behaviour.** Changing the *import block* does not take effect until the
> file is restarted: the extension shows an "imports out of date" / "Restart File" prompt at
> the top of the editor. Click it, or run `Ctrl+Shift+P` → **Lean 4: Restart File**. Until
> you do, `Subgroup.zpowers` will still be reported as an unknown constant.

After the restart the InfoView should report no errors. To *see* that the extra import is
what makes the lemma legal, comment the import line out, restart the file, and observe

```
Unknown constant `Subgroup.zpowers`
Unknown constant `Subgroup.zpowers_le`
```

then put it back and restart again.

**(b) `Mathlib/GroupTheory/OrderOfElement.lean`** — `Ctrl+P`, then `Ctrl+F` for
`smul_eq_self_of_mem_zpowers` (around line 822). Delete the whole block: the old lemma with
its `MulAction.toPermHom` proof, the hand-written `vadd_eq_self_of_mem_zmultiples`, and the
`attribute [to_additive existing] smul_eq_self_of_mem_zpowers` line — 13 lines including the
blank separators. The InfoView should again show no errors.

Nothing else in Mathlib mentions either name; confirm with VS Code's search
(`Ctrl+Shift+F`) for `smul_eq_self_of_mem_zpowers`, or in the terminal:

```bash
rg -n 'smul_eq_self_of_mem_zpowers|vadd_eq_self_of_mem_zmultiples' Mathlib/
```

## 6. Check the edit

**Per file, from the terminal** (fast, uses the cached oleans of everything else):

```bash
lake env lean Mathlib/GroupTheory/GroupAction/Basic.lean   # exit 0, no output
lake env lean Mathlib/GroupTheory/OrderOfElement.lean      # exit 0, no output
```

**Then the whole library**, which is the real test — 2850 modules import the edited file:

```bash
lake build
```

Only the affected modules are recompiled (everything else is served from the cache). Here it
finished with `Build completed successfully (8724 jobs).` in about 70 minutes on 8 cores, no
error and no warning in the log.

> **Why `lake build` matters even in the editor.** The language server reads *imports from
> `.olean` files*, never from your unsaved (or saved-but-unbuilt) editor buffers. Until
> `Mathlib/GroupTheory/GroupAction/Basic.lean` has been rebuilt, any other file you open will
> still see the pre-move environment. Rebuild just that one module with
> `lake build Mathlib.GroupTheory.GroupAction.Basic` if you do not want to wait for the
> whole library.

## 7. Check that the statements are the old ones

Copy `contribution/check_import_bump.lean` into the root of the clone and open it in VS Code
(after step 6, so that the new oleans exist; otherwise use **Lean 4: Restart File** once the
rebuild finishes). It contains the two pre-move statements as `example`s, applied to the
moved and to the generated declaration, plus two `#check`s. In the InfoView you should see

```
@smul_eq_self_of_mem_zpowers : ∀ {G : Type u_1} {α : Type u_2} [inst : Group G]
  [inst_1 : MulAction G α] {x y : G},
  x ∈ Subgroup.zpowers y → ∀ {a : α}, y • a = a → x • a = a
@vadd_eq_self_of_mem_zmultiples : ∀ {G : Type u_1} {α : Type u_2} [inst : AddGroup G]
  [inst_1 : AddAction G α] {x y : G},
  x ∈ AddSubgroup.zmultiples y → ∀ {a : α}, y +ᵥ a = a → x +ᵥ a = a
```

and no errors. Note that the additive lemma is now *generated* by `@[to_additive]`: put the
cursor on `vadd_eq_self_of_mem_zmultiples` and **Go to Definition** (`F12`) lands on the
multiplicative lemma in the stabilizer file.

The only difference from before the move is binder *order*: `{α}` now precedes `{x y : G}`,
because `G` and `α` are section variables of the stabilizer file. That is invisible to every
existing use (there are none outside the declaration site, and both lemmas are only ever
applied positionally), and step 6 confirms it library-wide.

Equivalently, from the terminal:

```bash
lake env lean check_import_bump.lean
```

## 8. Restore the checkout

```bash
git checkout -- Mathlib && rm -f check_import_bump.lean
git status --porcelain      # empty: the tree is byte-identical to the clone again
lake exe cache get          # restore the unpatched oleans
```

## 9. Reading the result

The move is *possible* at a genuine, small cost: one module added to one file's import
closure, and 13 downstream files gaining one module each. It is not *necessary*: the −12/+3
simplification of `contribution/master-smul_eq_self_of_mem_zpowers.patch` — same rerouted
proof, same deletion of the hand-written additive twin — can be done in
`OrderOfElement.lean`, which already imports everything needed, at zero import cost. So the
move buys placement (the lemma stated next to `MulAction.stabilizer`, whose theory it now
uses) and nothing else, and is worth proposing only if reviewers value that placement.

## Troubleshooting

* **"Import out of date" / stale errors after editing imports** — `Ctrl+Shift+P` → *Lean 4:
  Restart File*. If a *dependency* was edited, rebuild it (`lake build <Module.Name>`) and
  then restart the dependent file, or *Lean 4: Restart Server*.
* **The editor starts building all of Mathlib** — you opened a file before `lake exe cache
  get` finished. Stop the server (*Lean 4: Restart Server*), finish the cache download, then
  reopen.
* **`lake exe cache get` reports missing files** — the commit has no cache yet (too new, or a
  fork). Use `lake exe cache get!` to force re-download of what does exist, and expect the
  rest to be built locally.
* **Out of memory during `lake build`** — cap the parallelism, e.g. `lake build -j4`.
* **Different numbers from step 4** — master moves; re-run `git log -1` and report the commit
  alongside the figures, as done above.
