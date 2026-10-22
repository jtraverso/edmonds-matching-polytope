/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The perfect matching polytope: definitions

Vectors are indexed by the edges of a finite simple graph `G` (`G.edgeSet`).
-/

@[expose] public section

namespace MatchingPolytope

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` with exactly one endpoint in `S` (the cut `δ(S)`). -/
def cutEdges (S : Finset V) : Finset G.edgeSet :=
  univ.filter fun e => (∃ u ∈ (e : Sym2 V), u ∈ S) ∧ ∃ u ∈ (e : Sym2 V), u ∉ S

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

end MatchingPolytope
