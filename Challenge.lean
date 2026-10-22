/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Edmonds' matching polytopes

J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards
69B (1965) 125–130. Statements in the namespace `EdmondsPolytope`, for a finite simple graph `G`
with vectors indexed by its edges:

* `edmonds_perfect_matching_polytope`: the convex hull of the incidence vectors of the perfect
  matchings is `{x ≥ 0, x(δ(v)) = 1 for every vertex v, x(δ(S)) ≥ 1 for every odd S}`.
* `edmonds_matching_polytope`: the convex hull of the incidence vectors of all matchings is
  `{x ≥ 0, x(δ(v)) ≤ 1 for every vertex v, x(E[S]) ≤ (|S| − 1)/2 for every odd S}`.

The definitions below are part of the audited statements; the Mathlib definitions used are
reproduced in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace EdmondsPolytope

section Polytopes

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` with exactly one endpoint in `S` (the cut `δ(S)`). -/
def cutEdges (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e => (∃ u ∈ (e : Sym2 V), u ∈ S) ∧ ∃ u ∈ (e : Sym2 V), u ∉ S

open Classical in
/-- The incidence vector of a subgraph's edge set. -/
noncomputable def incidence (M : G.Subgraph) : G.edgeSet → ℝ :=
  fun e => if (e : Sym2 V) ∈ M.edgeSet then 1 else 0

/-- The incidence vectors of the perfect matchings of `G`. -/
def perfectMatchingVectors : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = incidence G M}

/-- Edmonds' description: nonnegativity, degree equations, and odd-set (blossom) inequalities. -/
def edmondsPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ cutEdges G {v}, x e = 1) ∧
    ∀ S : Finset V, Odd S.card → 1 ≤ ∑ e ∈ cutEdges G S, x e}

/-- The edges of `G` with both endpoints in `S` (the edge set `E[S]`). -/
def innerEdges (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e => ∀ u ∈ (e : Sym2 V), u ∈ S

/-- The incidence vectors of the matchings of `G`. -/
def matchingVectors : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = incidence G M}

/-- Edmonds' description of the matching polytope: nonnegativity, degree inequalities and
odd-set inequalities `x(E[S]) ≤ (|S| - 1)/2`. -/
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ cutEdges G {v}, x e ≤ 1) ∧
    ∀ S : Finset V, Odd S.card → ∑ e ∈ innerEdges G S, x e ≤ ((S.card : ℝ) - 1) / 2}

end Polytopes

/-- **Edmonds' perfect matching polytope theorem** (Edmonds 1965): the convex hull of the
incidence vectors of the perfect matchings of a finite simple graph is described by
nonnegativity, the degree equations and the odd-set inequalities. -/
theorem edmonds_perfect_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G := by
  sorry

/-- **Edmonds' matching polytope theorem**: the convex hull of the incidence vectors of the
matchings of a finite simple graph is described by nonnegativity, the degree inequalities and
the odd-set inequalities. -/
theorem edmonds_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (matchingVectors G) = matchingPolytope G := by
  sorry

end EdmondsPolytope
