/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MatchingPolytope.PerfectMatchingPolytope

/-!
# Edmonds' matching polytope theorem

For a finite simple graph `G`, the convex hull of the incidence vectors of all matchings of `G`
is `{x ≥ 0, x(δ(v)) ≤ 1, x(E[S]) ≤ (|S| - 1)/2 for odd S}`.

The inclusion `⊇` is derived from the perfect matching polytope theorem (for multigraphs) by
the standard doubling construction: take two disjoint copies of `G` and join each vertex to its
copy by a new edge carrying the slack `1 - x(δ(v))`.
-/

@[expose] public section

namespace MatchingPolytope

open Finset Multi

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` with both endpoints in `S` (the edge set `E[S]`). -/
def innerEdges (S : Finset V) : Finset G.edgeSet :=
  univ.filter fun e => ∀ u ∈ (e : Sym2 V), u ∈ S

/-- The incidence vectors of the matchings of `G`. -/
def matchingVectors : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = incidence G M}

/-- Edmonds' description of the matching polytope: nonnegativity, degree inequalities and
odd-set inequalities `x(E[S]) ≤ (|S| - 1)/2`. -/
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ cutEdges G {v}, x e ≤ 1) ∧
    ∀ S : Finset V, Odd S.card → ∑ e ∈ innerEdges G S, x e ≤ ((S.card : ℝ) - 1) / 2}

lemma inside_eq_innerEdges (S : Finset V) : inside (edgeEnds G) univ S = innerEdges G S := by
  ext e
  simp [inside, innerEdges]

/-! ### Matchings as edge sets -/

section Subgraph

variable {V : Type*} (G : SimpleGraph V)

/-- The subgraph with edge set `M` whose vertices are the endpoints of `M`. -/
def matchingSubgraphOf (M : Finset G.edgeSet) : G.Subgraph where
  verts := {v | ∃ w, ∃ e ∈ M, (e : Sym2 V) = s(v, w)}
  Adj a b := ∃ e ∈ M, (e : Sym2 V) = s(a, b)
  adj_sub := by
    rintro a b ⟨e, -, he⟩
    have := e.2
    rw [he] at this
    exact (SimpleGraph.mem_edgeSet G).1 this
  edge_vert := fun h => ⟨_, h⟩
  symm := ⟨by
    rintro a b ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩

lemma mem_edgeSet_matchingSubgraphOf {M : Finset G.edgeSet} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (matchingSubgraphOf G M).edgeSet ↔ e ∈ M := by
  obtain ⟨a, b, hab⟩ := exists_pair (e : Sym2 V)
  rw [hab, SimpleGraph.Subgraph.mem_edgeSet]
  constructor
  · rintro ⟨e', he', h⟩
    have : e' = e := Subtype.ext (h.trans hab.symm)
    exact this ▸ he'
  · intro he
    exact ⟨e, he, hab⟩

lemma isMatching_matchingSubgraphOf {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : (matchingSubgraphOf G M).IsMatching := by
  rintro v ⟨w, e, he, hew⟩
  refine ⟨w, ⟨e, he, hew⟩, fun w' hw' => ?_⟩
  obtain ⟨e', he', hew'⟩ := hw'
  have h1 : e ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton_of_nodiag fun e _ => G.not_isDiag_of_mem_edgeSet e.2]
    exact ⟨he, by simp [edgeEnds, hew]⟩
  have h2 : e' ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton_of_nodiag fun e _ => G.not_isDiag_of_mem_edgeSet e.2]
    exact ⟨he', by simp [edgeEnds, hew']⟩
  have := Finset.card_le_one.1 (hM v) e h1 e' h2
  subst this
  rw [hew] at hew'
  exact (Sym2.congr_right.1 hew').symm

lemma chi_mem_matchingVectors {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingVectors G := by
  refine ⟨matchingSubgraphOf G M, isMatching_matchingSubgraphOf G hM, ?_⟩
  funext e
  unfold incidence chi
  by_cases h : e ∈ M <;> simp [h, mem_edgeSet_matchingSubgraphOf]

end Subgraph

section Fin

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma card_gcut_edgesOf_le {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (gcut (edgeEnds G) (edgesOf G M) {v}).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro e he e' he'
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_edgesOf] at he he'
  obtain ⟨u, -, -, hu⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e) he.2
  obtain ⟨u', -, -, hu'⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e') he'.2
  simp only [edgeEnds] at hu hu'
  have h1 : M.Adj v u := by rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hu]; exact he.1
  have h2 : M.Adj v u' := by rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hu']; exact he'.1
  obtain ⟨w, -, huniq⟩ := hM (M.edge_vert h1)
  apply Subtype.ext
  rw [hu, hu', huniq u h1, huniq u' h2]

end Fin

lemma sum_chi_innerEdges (M : Finset G.edgeSet) (S : Finset V) :
    ∑ e ∈ innerEdges G S, chi M e = ((inside (edgeEnds G) M S).card : ℝ) := by
  rw [← inside_eq_innerEdges, sum_chi_inside (Finset.subset_univ M)]

lemma chi_mem_matchingPolytope {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingPolytope G := by
  refine ⟨fun e => ?_, fun v => ?_, fun S hS => ?_⟩
  · unfold chi; split_ifs <;> norm_num
  · rw [← gcut_eq_cutEdges, sum_chi_gcut (Finset.subset_univ M)]
    exact_mod_cast hM v
  · rw [sum_chi_innerEdges]
    have h := sum_degree (β := ℕ) (valid_edgeSet G) (Finset.subset_univ M) S (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    have hle : ∑ v ∈ S, (gcut (edgeEnds G) M {v}).card ≤ ∑ v ∈ S, 1 :=
      Finset.sum_le_sum fun v _ => hM v
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
    obtain ⟨k, hk⟩ := hS
    have : 2 * (inside (edgeEnds G) M S).card ≤ 2 * k := by omega
    have h' : ((inside (edgeEnds G) M S).card : ℝ) ≤ k := by exact_mod_cast (by omega)
    rw [hk]
    push_cast
    linarith

lemma convex_matchingPolytope : Convex ℝ (matchingPolytope G) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hs : ∀ s : Finset G.edgeSet, ∑ e ∈ s, (a • x + b • y) e =
      a * ∑ e ∈ s, x e + b * ∑ e ∈ s, y e := by
    intro s
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun e => ?_, fun v => ?_, fun S hS => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx1 e; have := hy1 e; positivity
  · rw [hs]
    have := hx2 v; have := hy2 v
    nlinarith
  · rw [hs]
    have h1 := hx3 S hS
    have h2 := hy3 S hS
    have : a * ∑ e ∈ innerEdges G S, x e + b * ∑ e ∈ innerEdges G S, y e ≤
        a * (((S.card : ℝ) - 1) / 2) + b * (((S.card : ℝ) - 1) / 2) := by
      gcongr
    rw [← add_mul, hab, one_mul] at this
    exact this

/-! ### The doubled multigraph -/

/-- Edges of the doubled graph: two copies of the edges of `G`, and one edge per vertex. -/
abbrev DEdge := G.edgeSet ⊕ (G.edgeSet ⊕ V)

/-- Endpoints in the doubled graph on `V ⊕ V`. -/
def dEnds : DEdge G → Sym2 (V ⊕ V)
  | Sum.inl e => (e : Sym2 V).map Sum.inl
  | Sum.inr (Sum.inl e) => (e : Sym2 V).map Sum.inr
  | Sum.inr (Sum.inr v) => s(Sum.inl v, Sum.inr v)

/-- The vector on the doubled graph associated with `x`. -/
def dvec (x : G.edgeSet → ℝ) : DEdge G → ℝ
  | Sum.inl e => x e
  | Sum.inr (Sum.inl e) => x e
  | Sum.inr (Sum.inr v) => 1 - ∑ e ∈ cutEdges G {v}, x e

omit [DecidableEq V] in
lemma dValid : Valid (dEnds G) univ univ := by
  refine ⟨fun _ _ _ _ => Finset.mem_univ _, fun e _ => ?_⟩
  rcases e with e | e | v
  · obtain ⟨a, b, hab, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    simpa [dEnds, h] using hab
  · obtain ⟨a, b, hab, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    simpa [dEnds, h] using hab
  · simp [dEnds]

lemma sum_gcut_dEnds (z : DEdge G → ℝ) (T : Finset (V ⊕ V)) :
    ∑ e ∈ gcut (dEnds G) univ T, z e =
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inl v ∈ T), z (Sum.inl e) +
      ∑ e ∈ cutEdges G (univ.filter fun v => Sum.inr v ∈ T), z (Sum.inr (Sum.inl e)) +
      ∑ v ∈ univ.filter (fun v => ¬ (Sum.inl v ∈ T ↔ Sum.inr v ∈ T)),
        z (Sum.inr (Sum.inr v)) := by
  classical
  have hfil : ∀ {α : Type _} [Fintype α] (s : Finset α) (f : α → ℝ),
      ∑ a ∈ s, f a = ∑ a, if a ∈ s then f a else 0 := by
    intro α _ s f
    rw [← Finset.sum_filter]
    congr 1
    ext a; simp
  rw [hfil, Fintype.sum_sum_type, Fintype.sum_sum_type, hfil (cutEdges G _),
    hfil (cutEdges G _), hfil (univ.filter _), add_assoc]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    have h' : dEnds G (Sum.inl e) = s(Sum.inl a, Sum.inl b) := by simp [dEnds, h]
    rw [← gcut_eq_cutEdges]
    congr 1
    rw [mem_gcut_of_pair h', mem_gcut_of_pair (ends := edgeEnds G) h]
    simp
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    simp only [edgeEnds] at h
    have h' : dEnds G (Sum.inr (Sum.inl e)) = s(Sum.inr a, Sum.inr b) := by simp [dEnds, h]
    rw [← gcut_eq_cutEdges]
    congr 1
    rw [mem_gcut_of_pair h', mem_gcut_of_pair (ends := edgeEnds G) h]
    simp
  · apply Finset.sum_congr rfl
    intro v _
    have h' : dEnds G (Sum.inr (Sum.inr v)) = s(Sum.inl v, Sum.inr v) := rfl
    congr 1
    rw [mem_gcut_of_pair h']
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    exact propext (by tauto)

lemma cutEdges_empty : cutEdges G ∅ = ∅ := by
  ext e
  simp [cutEdges]

lemma lower_bound {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) (A B : Finset V)
    (hodd : Odd (A \ B).card) :
    1 ≤ ∑ e ∈ cutEdges G A, x e + ∑ e ∈ cutEdges G B, x e +
      ∑ v ∈ univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)), (1 - ∑ e ∈ cutEdges G {v}, x e) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  set S := A \ B with hS
  -- posimodularity of the cut function
  have hsub : cutEdges G S ⊆ cutEdges G A ∪ cutEdges G B := by
    intro e he
    rw [← gcut_eq_cutEdges] at he
    rw [Finset.mem_union, ← gcut_eq_cutEdges, ← gcut_eq_cutEdges]
    obtain ⟨a, b, -, -, -, h⟩ := (valid_edgeSet G).pair (Finset.mem_univ e)
    rw [mem_gcut_of_pair h] at he
    rw [mem_gcut_of_pair h, mem_gcut_of_pair h]
    simp only [hS, Finset.mem_sdiff, Finset.mem_univ, true_and] at he ⊢
    tauto
  have h1 : ∑ e ∈ cutEdges G S, x e ≤ ∑ e ∈ cutEdges G A, x e + ∑ e ∈ cutEdges G B, x e := by
    calc ∑ e ∈ cutEdges G S, x e ≤ ∑ e ∈ cutEdges G A ∪ cutEdges G B, x e :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx1 e)
      _ ≤ ∑ e ∈ cutEdges G A ∪ cutEdges G B, x e + ∑ e ∈ cutEdges G A ∩ cutEdges G B, x e :=
          le_add_of_nonneg_right (Finset.sum_nonneg fun e _ => hx1 e)
      _ = _ := Finset.sum_union_inter
  have h2 : ∑ v ∈ S, (1 - ∑ e ∈ cutEdges G {v}, x e) ≤
      ∑ v ∈ univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)), (1 - ∑ e ∈ cutEdges G {v}, x e) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      simp only [hS, Finset.mem_sdiff] at hv
      simp [hv.1, hv.2]
    · intro v _ _
      linarith [hx2 v]
  have h3 := sum_degree (valid_edgeSet G) (D := univ) subset_rfl S x
  simp only [gcut_eq_cutEdges, inside_eq_innerEdges, nsmul_eq_mul] at h3
  have h4 := hx3 S hodd
  have h5 : ∑ v ∈ S, (1 - ∑ e ∈ cutEdges G {v}, x e) =
      (S.card : ℝ) - ∑ v ∈ S, ∑ e ∈ cutEdges G {v}, x e := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h5, h3] at h2
  push_cast at h2
  linarith

lemma dvec_mem_poly {x : G.edgeSet → ℝ} (hx : x ∈ matchingPolytope G) :
    dvec G x ∈ Multi.Poly (dEnds G) univ univ := by
  refine ⟨fun e he => absurd (Finset.mem_univ e) he, fun e => ?_, fun t _ => ?_,
    fun T _ hT => ?_⟩
  · rcases e with e | e | v
    · exact hx.1 e
    · exact hx.1 e
    · simp only [dvec]; linarith [hx.2.1 v]
  · rw [sum_gcut_dEnds]
    rcases t with v | v
    · have hA : (univ.filter fun u => (Sum.inl u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V))) =
          {v} := by ext u; simp
      have hB : (univ.filter fun u => (Sum.inr u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V))) =
          ∅ := by ext u; simp
      have hC : (univ.filter fun u => ¬ ((Sum.inl u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V)) ↔
          (Sum.inr u : V ⊕ V) ∈ ({Sum.inl v} : Finset (V ⊕ V)))) = {v} := by ext u; simp
      rw [hA, hB, hC, cutEdges_empty]
      simp [dvec]
    · have hA : (univ.filter fun u => (Sum.inl u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V))) =
          ∅ := by ext u; simp
      have hB : (univ.filter fun u => (Sum.inr u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V))) =
          {v} := by ext u; simp
      have hC : (univ.filter fun u => ¬ ((Sum.inl u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V)) ↔
          (Sum.inr u : V ⊕ V) ∈ ({Sum.inr v} : Finset (V ⊕ V)))) = {v} := by ext u; simp
      rw [hA, hB, hC, cutEdges_empty]
      simp [dvec]
  · rw [sum_gcut_dEnds]
    set A := univ.filter fun v => (Sum.inl v : V ⊕ V) ∈ T with hA
    set B := univ.filter fun v => (Sum.inr v : V ⊕ V) ∈ T with hB
    have hTAB : T = A.disjSum B := by
      ext t; rcases t with v | v <;> simp [hA, hB]
    have hcard : T.card = A.card + B.card := by rw [hTAB, Finset.card_disjSum]
    have hfil : (univ.filter fun v => ¬ ((Sum.inl v : V ⊕ V) ∈ T ↔ (Sum.inr v : V ⊕ V) ∈ T)) =
        univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)) := by
      ext v; simp [hA, hB]
    rw [hfil]
    simp only [dvec]
    have e1 := Finset.card_sdiff_add_card_inter A B
    have e2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at e2
    rcases Nat.even_or_odd (A \ B).card with hev | hodd
    · have hodd' : Odd (B \ A).card := by
        obtain ⟨k, hk⟩ := hT
        obtain ⟨j, hj⟩ := hev
        exact ⟨k - j - (A ∩ B).card, by omega⟩
      have := lower_bound G hx B A hodd'
      have hfil' : (univ.filter fun v => ¬ (v ∈ B ↔ v ∈ A)) =
          univ.filter (fun v => ¬ (v ∈ A ↔ v ∈ B)) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      rw [hfil'] at this
      linarith
    · exact lower_bound G hx A B hodd

/-- Restriction of an edge set of the doubled graph to the first copy of `G`. -/
noncomputable def proj (N : Finset (DEdge G)) : Finset G.edgeSet := by
  classical exact univ.filter fun e => Sum.inl e ∈ N

lemma mem_proj {N : Finset (DEdge G)} {e : G.edgeSet} : e ∈ proj G N ↔ Sum.inl e ∈ N := by
  classical
  simp [proj]

lemma chi_proj (N : Finset (DEdge G)) (e : G.edgeSet) : chi (proj G N) e = chi N (Sum.inl e) := by
  unfold chi
  by_cases h : Sum.inl e ∈ N <;> simp [h, mem_proj]

lemma card_gcut_proj_le {N : Finset (DEdge G)} (hN : IsPM (dEnds G) univ univ N) (v : V) :
    (gcut (edgeEnds G) (proj G N) {v}).card ≤ 1 := by
  rw [← hN.2 (Sum.inl v) (Finset.mem_univ _)]
  rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
  apply Finset.card_le_card
  intro e' he'
  rw [Finset.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_proj] at he
  rw [mem_gcut_singleton (dValid G) (Finset.subset_univ _)]
  refine ⟨he.1, ?_⟩
  simp only [Function.Embedding.coeFn_mk, dEnds, Sym2.mem_map]
  exact ⟨v, he.2, rfl⟩

/-- **Edmonds' matching polytope theorem**: the convex hull of the incidence vectors of the
matchings of a finite simple graph is described by nonnegativity, the degree inequalities and
the odd-set inequalities. -/
theorem edmonds_matching_polytope :
    convexHull ℝ (matchingVectors G) = matchingPolytope G := by
  apply le_antisymm
  · refine convexHull_min ?_ (convex_matchingPolytope G)
    rintro x ⟨M, hM, rfl⟩
    rw [incidence_eq_chi]
    exact chi_mem_matchingPolytope G (card_gcut_edgesOf_le G hM)
  · intro x hx
    obtain ⟨w, hw0, hw1, hw2, hw3⟩ := inHull_of_mem_poly _ _ _ (dValid G) (dvec_mem_poly G hx)
    have hxeq : x = ∑ N, w N • chi (proj G N) := by
      funext e
      have := congrFun hw3 (Sum.inl e)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dvec] at this
      rw [← this, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro N _
      simp only [Pi.smul_apply, smul_eq_mul, chi_proj]
    classical
    rw [hxeq, ← Finset.sum_filter_of_ne (p := fun N => w N ≠ 0)
      (fun N _ h h0 => h (by simp [h0]))]
    refine (convex_convexHull ℝ _).sum_mem (fun N _ => hw0 N) ?_ fun N hN => ?_
    · rw [Finset.sum_filter_ne_zero, hw2]
    · exact subset_convexHull ℝ _ (chi_mem_matchingVectors G
        (card_gcut_proj_le G (hw1 N (Finset.mem_filter.1 hN).2)))

end MatchingPolytope
