/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MatchingPolytope.Defs
public import MatchingPolytope.Induction

/-!
# Edmonds' perfect matching polytope theorem

For a finite simple graph `G`, the convex hull of the incidence vectors of the perfect matchings
of `G` is the polytope `edmondsPolytope G` given by nonnegativity, the degree equations and the
odd-set inequalities (J. Edmonds, 1965). The proof (following Schrijver) is carried out for
multigraphs in `MatchingPolytope.Induction`; here we specialise it to simple graphs.
-/

@[expose] public section

namespace MatchingPolytope

open Finset Multi

section Convexity

variable {V E : Type*}

lemma convex_poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    Convex ℝ (Multi.Poly ends W F) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
  have hs : ∀ s : Finset E, ∑ e ∈ s, (a • x + b • y) e =
      a * ∑ e ∈ s, x e + b * ∑ e ∈ s, y e := by
    intro s
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp [hx0 e he, hy0 e he]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx1 e; have := hy1 e; positivity
  · rw [hs, hx2 v hv, hy2 v hv]; linarith
  · rw [hs]
    have h1 := hx3 S hS hodd
    have h2 := hy3 S hS hodd
    nlinarith

end Convexity

section Subgraph

variable {V : Type*} (G : SimpleGraph V)

/-- The subgraph with edge set `M` and all vertices. -/
def subgraphOf (M : Finset G.edgeSet) : G.Subgraph where
  verts := Set.univ
  Adj a b := ∃ e ∈ M, (e : Sym2 V) = s(a, b)
  adj_sub := by
    rintro a b ⟨e, -, he⟩
    have := e.2
    rw [he] at this
    exact (SimpleGraph.mem_edgeSet G).1 this
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    rintro a b ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩

lemma mem_edgeSet_subgraphOf {M : Finset G.edgeSet} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (subgraphOf G M).edgeSet ↔ e ∈ M := by
  obtain ⟨a, b, hab⟩ := exists_pair (e : Sym2 V)
  rw [hab, SimpleGraph.Subgraph.mem_edgeSet]
  constructor
  · rintro ⟨e', he', h⟩
    have : e' = e := Subtype.ext (h.trans hab.symm)
    exact this ▸ he'
  · intro he
    exact ⟨e, he, hab⟩

end Subgraph

section

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The endpoint map of the edges of a simple graph. -/
abbrev edgeEnds : G.edgeSet → Sym2 V := fun e => (e : Sym2 V)

lemma valid_edgeSet : Valid (edgeEnds G) univ univ :=
  ⟨fun _ _ _ _ => Finset.mem_univ _, fun e _ => G.not_isDiag_of_mem_edgeSet e.2⟩

lemma gcut_eq_cutEdges [DecidableEq V] (S : Finset V) :
    gcut (edgeEnds G) univ S = cutEdges G S := by
  ext e
  simp [gcut, cutEdges]

lemma edmondsPolytope_eq [DecidableEq V] :
    edmondsPolytope G = Multi.Poly (edgeEnds G) univ univ := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun e he => absurd (Finset.mem_univ e) he, h1, fun v _ => ?_, fun S _ hS => ?_⟩
    · rw [gcut_eq_cutEdges]; exact h2 v
    · rw [gcut_eq_cutEdges]; exact h3 S hS
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨h1, fun v => ?_, fun S hS => ?_⟩
    · rw [← gcut_eq_cutEdges]; exact h2 v (Finset.mem_univ v)
    · rw [← gcut_eq_cutEdges]; exact h3 S (Finset.subset_univ S) hS

open Classical in
/-- The edges of a subgraph, as a finset of edges of `G`. -/
noncomputable def edgesOf (M : G.Subgraph) : Finset G.edgeSet :=
  univ.filter fun e => (e : Sym2 V) ∈ M.edgeSet

lemma mem_edgesOf {M : G.Subgraph} {e : G.edgeSet} :
    e ∈ edgesOf G M ↔ (e : Sym2 V) ∈ M.edgeSet := by
  classical
  simp [edgesOf]

lemma incidence_eq_chi (M : G.Subgraph) : incidence G M = chi (edgesOf G M) := by
  funext e
  unfold incidence chi
  split_ifs with h1 h2 h2 <;> simp_all [mem_edgesOf]

lemma isPM_edgesOf {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    IsPM (edgeEnds G) univ univ (edgesOf G M) := by
  refine ⟨Finset.subset_univ _, fun v _ => ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  obtain ⟨w, hw, huniq⟩ := hM v
  have hvw : G.Adj v w := M.adj_sub hw
  rw [Finset.card_eq_one]
  refine ⟨⟨s(v, w), (SimpleGraph.mem_edgeSet G).2 hvw⟩, ?_⟩
  ext e
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_edgesOf,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hve⟩
    obtain ⟨u, -, -, hu⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e) hve
    simp only [edgeEnds] at hu
    rw [hu, SimpleGraph.Subgraph.mem_edgeSet] at he
    have := huniq u he
    apply Subtype.ext
    simp only [hu, this]
  · rintro rfl
    simp only [edgeEnds, SimpleGraph.Subgraph.mem_edgeSet, Sym2.mem_iff, true_or, and_true]
    exact hw

lemma isPerfectMatching_subgraphOf {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : (subgraphOf G M).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 (hM.2 v (Finset.mem_univ v))
  have hmem : e0 ∈ gcut (edgeEnds G) M {v} := by rw [he0]; exact Finset.mem_singleton_self _
  rw [mem_gcut_singleton (valid_edgeSet G) hM.1] at hmem
  obtain ⟨he0M, hve0⟩ := hmem
  obtain ⟨w, -, -, hw⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e0) hve0
  refine ⟨w, ⟨e0, he0M, hw⟩, fun w' hw' => ?_⟩
  obtain ⟨e, heM, he⟩ := hw'
  have : e ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton (valid_edgeSet G) hM.1]
    exact ⟨heM, by simp [edgeEnds, he]⟩
  rw [he0, Finset.mem_singleton] at this
  subst this
  simp only [edgeEnds] at hw
  rw [hw] at he
  exact (Sym2.congr_right.1 he).symm

lemma chi_mem_perfectMatchingVectors {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : chi M ∈ perfectMatchingVectors G := by
  refine ⟨subgraphOf G M, isPerfectMatching_subgraphOf G hM, ?_⟩
  funext e
  unfold incidence chi
  by_cases h : e ∈ M <;> simp [h, mem_edgeSet_subgraphOf]

end

/-- **Edmonds' perfect matching polytope theorem** (Edmonds 1965): the convex hull of the
incidence vectors of the perfect matchings of a finite simple graph is described by
nonnegativity, the degree equations and the odd-set inequalities. -/
theorem edmonds_perfect_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G := by
  apply le_antisymm
  · rw [edmondsPolytope_eq]
    refine convexHull_min ?_ (convex_poly _ _ _)
    rintro x ⟨M, hM, rfl⟩
    rw [incidence_eq_chi]
    exact chi_mem_poly (valid_edgeSet G) (isPM_edgesOf G hM)
  · intro x hx
    rw [edmondsPolytope_eq] at hx
    obtain ⟨w, hw0, hw1, hw2, hw3⟩ := inHull_of_mem_poly _ _ _ (valid_edgeSet G) hx
    classical
    rw [← hw3, ← Finset.sum_filter_of_ne (p := fun M => w M ≠ 0)
      (fun M _ h h0 => h (by simp [h0]))]
    refine (convex_convexHull ℝ _).sum_mem (fun M _ => hw0 M) ?_ fun M hM => ?_
    · rw [Finset.sum_filter_ne_zero, hw2]
    · exact subset_convexHull ℝ _
        (chi_mem_perfectMatchingVectors G (hw1 M (Finset.mem_filter.1 hM).2))

end MatchingPolytope
