# Edmonds' matching polytopes in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of J. Edmonds' polyhedral description of matchings
(*Maximum matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards 69B (1965)
125–130). The results hold for every finite simple graph `G`, with vectors indexed by the edges
of `G`:

* **the perfect matching polytope**: the convex hull of the incidence vectors of the perfect
  matchings is `{x ≥ 0, x(δ(v)) = 1 for every vertex v, x(δ(S)) ≥ 1 for every odd S}`;
* **the matching polytope**: the convex hull of the incidence vectors of all matchings is
  `{x ≥ 0, x(δ(v)) ≤ 1 for every vertex v, x(E[S]) ≤ (|S| − 1)/2 for every odd S}`.

All statements are in the namespace `EdmondsPolytope` of `Challenge.lean`.

## Definitions

* `cutEdges G S` is the cut `δ(S)`, the edges with exactly one endpoint in `S`.
* `innerEdges G S` is `E[S]`, the edges with both endpoints in `S`.
* `incidence G M` is the incidence vector of a subgraph `M`.
* `perfectMatchingVectors G` and `matchingVectors G` collect these vectors for Mathlib's
  `Subgraph.IsPerfectMatching` and `Subgraph.IsMatching`.
* `edmondsPolytope G` and `matchingPolytope G` are Edmonds' inequality descriptions.
* The convex hull is Mathlib's `convexHull ℝ`.

## Results

| Lean | Statement |
|---|---|
| `edmonds_perfect_matching_polytope` | `convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G` |
| `edmonds_matching_polytope` | `convexHull ℝ (matchingVectors G) = matchingPolytope G` |

## Proofs

The proofs are in `MatchingPolytope/`. Shrinking a vertex set creates parallel edges, so the
perfect-matching theorem is proved for multigraphs (`Multigraph.lean`). These are given by an
endpoint map on fixed vertex and edge types together with active vertex and edge sets, so no new
types are built during the induction.

The induction (`Induction.lean`) is on the number of active vertices plus active edges:

* an edge with `x_e = 0` is deleted;
* if an odd set `S`, with at least two vertices on each side, is tight (`x(δ(S)) = 1`), `S` and
  its complement are shrunk in turn (`Shrink.lean`), the induction is applied to both, and the
  two convex combinations are glued along the cut (`Glue.lean`);
* otherwise either `x` lies strictly between two reducible points, or the degree map is injective
  and a counting argument finishes the proof.

The matching polytope (`Matching.lean`) follows by the standard doubling construction. No `sorry`
and no `native_decide` is used; the only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports
  only Mathlib.
- [`Solution.lean`](Solution.lean) and [`MatchingPolytope/`](MatchingPolytope): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## Sources

* J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards
  69B (1965) 125–130, doi:10.6028/jres.069B.013.
* A. Schrijver, *Short proofs on the matching polyhedron*, J. Combin. Theory Ser. B 34 (1983)
  104–108, doi:10.1016/0095-8956(83)90011-4.

## Authorship and use of AI

The author chose the result and directed the work. The proofs were produced by Harmonic's
Aristotle from formal statements and a suggested proof route (Schrijver's short proof). Claude
(Claude Code) wrote the definitions and statements, audited the return, built it locally and
prepared this package. Lean checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
