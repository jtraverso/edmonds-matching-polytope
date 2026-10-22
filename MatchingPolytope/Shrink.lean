/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MatchingPolytope.Multigraph

/-!
# Shrinking a vertex set

Shrinking an active vertex set `R` to one of its vertices `r` collapses all endpoints in `R`
to `r`, deletes the edges inside `R` and keeps all other edges (possibly creating parallel
edges). If `x` lies in the polytope and the cut of `R` is tight, then the restriction of `x`
lies in the polytope of the shrunk multigraph.
-/

@[expose] public section

namespace MatchingPolytope.Multi

open Finset

variable {V E : Type*}

open Classical in
/-- Edges after shrinking `R`: those not inside `R`. -/
noncomputable def shrinkF (ends : E → Sym2 V) (F : Finset E) (R : Finset V) : Finset E :=
  F.filter fun e => ∃ u ∈ ends e, u ∉ R

section NoDec

variable {ends : E → Sym2 V} {F : Finset E}

lemma mem_shrinkF {R : Finset V} {e : E} :
    e ∈ shrinkF ends F R ↔ e ∈ F ∧ ∃ u ∈ ends e, u ∉ R := by
  classical
  simp [shrinkF]

lemma shrinkF_subset (R : Finset V) : shrinkF ends F R ⊆ F := fun _ h => (mem_shrinkF.1 h).1

lemma shrinkF_of_subset {R : Finset V} {M : Finset E} (hM : M ⊆ shrinkF ends F R) :
    shrinkF ends M R = M := by
  ext e
  rw [mem_shrinkF]
  exact ⟨fun h => h.1, fun h => ⟨h, (mem_shrinkF.1 (hM h)).2⟩⟩

end NoDec

variable [DecidableEq V]

/-- Collapse the vertices of `R` to `r`. -/
def collapse (R : Finset V) (r : V) (u : V) : V := if u ∈ R then r else u

/-- Endpoints after shrinking `R` to `r`. -/
def shrinkEnds (ends : E → Sym2 V) (R : Finset V) (r : V) : E → Sym2 V :=
  fun e => (ends e).map (collapse R r)

/-- Vertices after shrinking `R` to `r`. -/
def shrinkW (W R : Finset V) (r : V) : Finset V := insert r (W \ R)

variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

lemma shrinkEnds_pair {R : Finset V} {r : V} {e : E} {a b : V} (h : ends e = s(a, b)) :
    shrinkEnds ends R r e = s(collapse R r a, collapse R r b) := by
  simp [shrinkEnds, h]

lemma shrink_valid (hV : Valid ends W F) {R : Finset V} {r : V} (hr : r ∈ R) :
    Valid (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by
  constructor
  · intro e he u hu
    obtain ⟨heF, -⟩ := mem_shrinkF.1 he
    obtain ⟨a, b, -, ha, hb, h⟩ := hV.pair heF
    rw [shrinkEnds_pair h, Sym2.mem_iff] at hu
    simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff]
    rcases hu with rfl | rfl <;> simp only [collapse] <;> split_ifs <;> simp [*]
  · intro e he
    obtain ⟨heF, u, hu, huR⟩ := mem_shrinkF.1 he
    obtain ⟨a, b, hab, -, -, h⟩ := hV.pair heF
    rw [shrinkEnds_pair h, Sym2.mk_isDiag_iff]
    rw [h, Sym2.mem_iff] at hu
    simp only [collapse]
    rcases hu with rfl | rfl
    · simp only [huR, ↓reduceIte]
      split_ifs with hb
      · rintro rfl; exact huR hr
      · exact hab
    · simp only [huR, ↓reduceIte]
      split_ifs with ha
      · rintro rfl; exact huR hr
      · exact hab

lemma card_shrinkW_lt {R : Finset V} (hRW : R ⊆ W) (hR : 1 < R.card) (r : V) :
    (shrinkW W R r).card < W.card := by
  have h1 := Finset.card_insert_le r (W \ R)
  have h2 := Finset.card_sdiff_of_subset hRW
  have h3 := Finset.card_le_card hRW
  unfold shrinkW
  omega

/-- The cut of `T` in the shrunk multigraph is the cut of the preimage of `T`. -/
lemma gcut_shrink (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (R : Finset V) (r : V)
    (T : Finset V) :
    gcut (shrinkEnds ends R r) (shrinkF ends D R) T =
      gcut ends D (W.filter fun u => collapse R r u ∈ T) := by
  ext e
  constructor
  · intro h
    have he := shrinkF_subset R (gcut_subset _ _ h)
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair (shrinkEnds_pair hab), mem_shrinkF] at h
    rw [mem_gcut_of_pair hab]
    simp only [Finset.mem_filter, ha, hb, true_and]
    exact ⟨he, h.2⟩
  · intro h
    have he := gcut_subset _ _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h
    simp only [Finset.mem_filter, ha, hb, true_and] at h
    rw [mem_gcut_of_pair (shrinkEnds_pair hab), mem_shrinkF]
    refine ⟨⟨he, ?_⟩, h.2⟩
    rw [hab]
    by_contra hcon
    simp only [Sym2.mem_iff, exists_eq_or_imp, exists_eq_left, not_or, not_not] at hcon
    simp only [collapse, hcon.1, hcon.2, ↓reduceIte] at h
    tauto

lemma filter_collapse_self {R : Finset V} {r : V} (hr : r ∈ R) (hRW : R ⊆ W) :
    W.filter (fun u => collapse R r u ∈ ({r} : Finset V)) = R := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_singleton, collapse]
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with hu
    · exact hu
    · exact h ▸ hr
  · intro hu
    exact ⟨hRW hu, by simp [hu]⟩

lemma filter_collapse_other {R : Finset V} {r : V} (hr : r ∈ R) {v : V} (hv : v ∈ W)
    (hvR : v ∉ R) : W.filter (fun u => collapse R r u ∈ ({v} : Finset V)) = {v} := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_singleton, collapse]
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with hu
    · subst h; exact absurd hr hvR
    · exact h
  · rintro rfl
    exact ⟨hv, by simp [hvR]⟩

lemma filter_collapse_odd {R : Finset V} {r : V} (hr : r ∈ R) (hRW : R ⊆ W)
    (hRodd : Odd R.card) {T : Finset V} (hT : T ⊆ shrinkW W R r) (hTodd : Odd T.card) :
    Odd (W.filter fun u => collapse R r u ∈ T).card := by
  by_cases hrT : r ∈ T
  · have hU : W.filter (fun u => collapse R r u ∈ T) = R ∪ T.erase r := by
      ext u
      rw [Finset.mem_filter]
      simp only [Finset.mem_union, Finset.mem_erase, collapse]
      constructor
      · rintro ⟨-, h⟩
        split_ifs at h with hu
        · exact Or.inl hu
        · exact Or.inr ⟨fun h' => hu (h' ▸ hr), h⟩
      · rintro (hu | ⟨hur, hu⟩)
        · exact ⟨hRW hu, by simp [hu, hrT]⟩
        · have := hT hu
          simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
          rcases this with h | ⟨huW, huR⟩
          · exact absurd h hur
          · exact ⟨huW, by simp [huR, hu]⟩
    have hdisj : Disjoint R (T.erase r) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      rw [Finset.mem_erase] at hu'
      have := hT hu'.2
      simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
      rcases this with h | ⟨-, huR⟩
      · exact hu'.1 h
      · exact huR hu
    rw [hU, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hrT]
    obtain ⟨k, hk⟩ := hTodd
    rw [hk]
    simpa using hRodd.add_even (even_two_mul k)
  · have hU : W.filter (fun u => collapse R r u ∈ T) = T := by
      ext u
      rw [Finset.mem_filter]
      simp only [collapse]
      constructor
      · rintro ⟨-, h⟩
        split_ifs at h with hu
        · exact absurd h hrT
        · exact h
      · intro hu
        have := hT hu
        simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at this
        rcases this with h | ⟨huW, huR⟩
        · exact absurd (h ▸ hu) hrT
        · exact ⟨huW, by simp [huR, hu]⟩
    rw [hU]; exact hTodd

lemma sum_restr_gcut_shrink (hV : Valid ends W F) (R : Finset V) (r : V) (T : Finset V)
    (x : E → ℝ) :
    ∑ e ∈ gcut (shrinkEnds ends R r) (shrinkF ends F R) T, restr (shrinkF ends F R) x e =
      ∑ e ∈ gcut ends F (W.filter fun u => collapse R r u ∈ T), x e := by
  rw [← gcut_shrink hV subset_rfl R r T]
  apply Finset.sum_congr rfl
  intro e he
  simp [restr, gcut_subset _ _ he]

/-- The restriction of `x` to the shrunk multigraph lies in its polytope. -/
lemma restr_mem_poly_shrink (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R) (hRodd : Odd R.card)
    (htight : ∑ e ∈ gcut ends F R, x e = 1) :
    restr (shrinkF ends F R) x ∈ Poly (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  refine ⟨fun e he => by simp [restr, he], fun e => ?_, fun v hv => ?_, fun T hT hTodd => ?_⟩
  · simp only [restr]; split_ifs
    · exact hx1 e
    · exact le_rfl
  · rw [sum_restr_gcut_shrink hV]
    simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at hv
    rcases hv with rfl | ⟨hvW, hvR⟩
    · rw [filter_collapse_self hr hRW]; exact htight
    · rw [filter_collapse_other hr hvW hvR]; exact hx2 v hvW
  · rw [sum_restr_gcut_shrink hV]
    exact hx3 _ (Finset.filter_subset _ _) (filter_collapse_odd hr hRW hRodd hT hTodd)

/-- A perfect matching of the shrunk multigraph, seen in the original multigraph. -/
lemma IsPM.of_shrink (hV : Valid ends W F) {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R)
    {M : Finset E} (hM : IsPM (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) M) :
    M ⊆ shrinkF ends F R ∧ (gcut ends M R).card = 1 ∧
      ∀ v ∈ W, v ∉ R → (gcut ends M {v}).card = 1 := by
  have hMF : M ⊆ F := hM.1.trans (shrinkF_subset R)
  have key : ∀ T, gcut (shrinkEnds ends R r) M T =
      gcut ends M (W.filter fun u => collapse R r u ∈ T) := by
    intro T
    rw [← gcut_shrink hV hMF R r T, shrinkF_of_subset hM.1]
  refine ⟨hM.1, ?_, fun v hv hvR => ?_⟩
  · have := hM.2 r (Finset.mem_insert_self _ _)
    rwa [key, filter_collapse_self hr hRW] at this
  · have := hM.2 v (by simp [shrinkW, hv, hvR])
    rwa [key, filter_collapse_other hr hv hvR] at this

end MatchingPolytope.Multi
