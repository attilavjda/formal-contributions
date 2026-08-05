# Visual companion

`proof-visualisations.pdf` (source: `proof-visualisations.tex`) draws the mathematics of
the Lean development in `RequestProject/`.  Every figure is TikZ / TikZ-CD and every
caption names the Lean declaration it depicts.

## Files

| File | Contents |
| --- | --- |
| `proof-visualisations.tex` | master document (title, abstract, contents, `\input`s) |
| `preamble.tex` | packages, tag colours, node styles, Unicode mappings for Lean names |
| `fig-lattice.tex` | §1 the statement drawn: squares, Hasse diagrams, concrete lattices, a counterexample, the analytic corollary |
| `fig-graph.tex` | §2 the proof space as a graph: the dependency DAG, the three-colouring, the spanning tree, cofinality as a bipartite graph |
| `fig-cat.tex` | §3 arrow diagrams: commuting triangles, Fubini for colimits, finality of the diagonal functor, transport along the bridges, the bridge hub |
| `fig-variations.tex` | §4 the design space of proofs as a Boolean lattice, duality as an involution, the application map |
| `build.sh` | one-line build |

## Building

```sh
cd visuals && ./build.sh          # or: tectonic proof-visualisations.tex
```

Any LaTeX engine works; the document needs `tikz`, `tikz-cd`, `newunicodechar`,
`rotating`, `booktabs`, `caption` and `hyperref`.  With `pdflatex` the
`newunicodechar` mappings in `preamble.tex` are what make the Unicode in Lean names
(`iSup₂`, `αᵒᵈ`, `·`) typeset correctly; two figures use `sidewaysfigure`, so a second
run is needed for the page references.

## Figure index

1. the diagonal hypothesis as a combinatorial statement about a square
2. three readings of the same supremum (rows-then-column / product index / diagonal)
3. the lattice picture of `le_antisymm` for mutual cofinality
4. a numerical square of sums in `ℝ≥0∞`
5. where boundedness enters: a ceiling transported down cofinality
6. the Boolean lattice `2^{a,b,c}` with two monotone chains
7. a three-element chain: the counterexample when the hypothesis fails
8. the monotone staircase behind `ennreal_tendsto_add_atTop`
9. the dependency DAG of the 25 lemmas (ranked, tag-coloured, with the two bridges)
10. the three connected components of the use-graph
11. the spanning tree given by `toRoot` / `depth`
12. cofinality as a bipartite graph
13. the two collapse proofs as commuting triangles
14. the binary-operation form as a square
15. currying and Fubini for colimits
16. finality of the diagonal functor
17. transport along `OrderIso`, `sSupHom`, `GaloisConnection`
18. the duality bridge
19. the bridge hub: one theorem, eight contexts
20. the design space of proofs as the Boolean lattice `B₃`
21. duality as an involution on the whole design space
22. from the abstraction to the applications
