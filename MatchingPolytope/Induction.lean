/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MatchingPolytope.Glue

/-!
# Schrijver's induction for the perfect matching polytope of a multigraph

We prove by strong induction on `|W| + |F|` that every point of `Poly ends W F` is a convex
combination of incidence vectors of perfect matchings.

A point `y` is *reducible* if some edge has `y e = 0` (delete the edge) or some odd set `S`
with `|S| ≥ 2` and `|W \ S| ≥ 2` is tight (shrink `S` and its complement and glue).
Reducible points are handled by the induction hypothesis. For an irreducible point `x`:

* if the degree map has a nonzero kernel vector `d` (supported on `F`), we move from `x` in the
  directions `±d` until a new constraint becomes tight; both endpoints are reducible and `x`
  is a convex combination of them;
* otherwise `|F| ≤ |W|`; if `|W| ≥ 5` every vertex has degree at least `3` (a vertex of degree
  at most `2` gives a tight odd set of size `3`), which is impossible; if `|W| ≤ 4` a perfect
  matching `M` exists and `x = χ_M` by injectivity of the degree map.
-/

@[expose] public section

namespace MatchingPolytope.Multi

open Finset

variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

/-- A point is reducible if an edge has value zero or a nontrivial odd cut is tight. -/
def Reducible [DecidableEq V] (ends : E → Sym2 V) (W : Finset V) (F : Finset E)
    (y : E → ℝ) : Prop :=
  (∃ e ∈ F, y e = 0) ∨
    ∃ S ⊆ W, Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card ∧ ∑ e ∈ gcut ends F S, y e = 1

lemma odd_card_sdiff [DecidableEq V] {S : Finset V} (hSW : S ⊆ W) (hW : Even W.card)
    (hS : Odd S.card) :
    Odd (W \ S).card := by
  have h := Finset.card_sdiff_add_card_eq_card hSW
  obtain ⟨a, ha⟩ := hW
  obtain ⟨b, hb⟩ := hS
  exact ⟨a - b - 1, by omega⟩

/-! ### Reducible points -/

section Reducible

lemma gcut_erase [DecidableEq E] (e : E) (T : Finset V) :
    gcut ends (F.erase e) T = (gcut ends F T).erase e := by
  classical
  ext e'
  simp only [gcut, Finset.mem_filter, Finset.mem_erase]
  tauto

lemma mem_poly_erase [DecidableEq E] {y : E → ℝ} (hy : y ∈ Poly ends W F) {e : E} (he0 : y e = 0) :
    y ∈ Poly ends W (F.erase e) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  refine ⟨fun e' he' => ?_, h1, fun v hv => ?_, fun S hS hodd => ?_⟩
  · by_cases h : e' = e
    · rw [h, he0]
    · exact h0 e' (fun h' => he' (Finset.mem_erase.2 ⟨h, h'⟩))
  · rw [gcut_erase, Finset.sum_erase _ he0]; exact h2 v hv
  · rw [gcut_erase, Finset.sum_erase _ he0]; exact h3 S hS hodd

/-- Reducible points are in the hull, assuming the theorem for smaller multigraphs. -/
theorem inHull_of_reducible [DecidableEq V] [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {y : E → ℝ} (hy : y ∈ Poly ends W F) (hr : Reducible ends W F y) :
    InHull (IsPM ends W F) y := by
  classical
  by_cases h0 : ∃ e ∈ F, y e = 0
  · obtain ⟨e, he, he0⟩ := h0
    have hlt : W.card + (F.erase e).card < W.card + F.card := by
      have := Finset.card_erase_lt_of_mem he
      omega
    have := IH ends W (F.erase e) hlt (hV.mono (Finset.erase_subset _ _)) y
      (mem_poly_erase hy he0)
    exact this.mono fun M hM => ⟨hM.1.trans (Finset.erase_subset _ _), hM.2⟩
  · have hpos : ∀ e ∈ F, 0 < y e := by
      intro e he
      refine lt_of_le_of_ne (hy.2.1 e) ?_
      intro h
      exact h0 ⟨e, he, h.symm⟩
    obtain ⟨S, hSW, hSodd, hS1, hWS1, htight⟩ := hr.resolve_left h0
    have hW := even_card_of_mem_poly hV hy
    obtain ⟨s, hs⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨t, ht⟩ : (W \ S).Nonempty := Finset.card_pos.1 (by omega)
    have hWSodd := odd_card_sdiff hSW hW hSodd
    have hS' : W \ S ⊆ W := Finset.sdiff_subset
    apply inHull_glue hV hy hpos hSW hs ht
    · apply IH _ _ _ _ (shrink_valid hV hs) _ (restr_mem_poly_shrink hV hy hSW hs hSodd htight)
      have := card_shrinkW_lt hSW hS1 s
      have := Finset.card_le_card (shrinkF_subset (ends := ends) (F := F) S)
      omega
    · apply IH _ _ _ _ (shrink_valid hV ht) _
        (restr_mem_poly_shrink hV hy hS' ht hWSodd (by rwa [gcut_compl hV subset_rfl]))
      have := card_shrinkW_lt hS' hWS1 t
      have := Finset.card_le_card (shrinkF_subset (ends := ends) (F := F) (W \ S))
      omega

end Reducible

/-! ### Moving along kernel directions -/

lemma sum_add_smul (s : Finset E) (y d : E → ℝ) (ε : ℝ) :
    ∑ e ∈ s, (y + ε • d) e = ∑ e ∈ s, y e + ε * ∑ e ∈ s, d e := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- From an irreducible point one can move a little in any kernel direction. -/
lemma exists_pos_add_mem [DecidableEq V] (hV : Valid ends W F) {y d : E → ℝ}
    (hy : y ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F y) (hd : Ker ends W F d) :
    ∃ ε : ℝ, 0 < ε ∧ y + ε • d ∈ Poly ends W F := by
  have hW := even_card_of_mem_poly hV hy
  have hpos : ∀ e ∈ F, 0 < y e := by
    intro e he
    refine lt_of_le_of_ne (hy.2.1 e) ?_
    intro h
    exact hirr (Or.inl ⟨e, he, h.symm⟩)
  have hnt : ∀ S ∈ W.powerset.filter (fun S => Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card),
      1 < ∑ e ∈ gcut ends F S, y e := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    refine lt_of_le_of_ne (hy.2.2.2 S hS.1 hS.2.1) ?_
    intro h
    exact hirr (Or.inr ⟨S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, h.symm⟩)
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (∀ e ∈ F, 0 < y e + ε * d e) ∧
      (∀ S ∈ W.powerset.filter (fun S => Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card),
        1 < ∑ e ∈ gcut ends F S, y e + ε * ∑ e ∈ gcut ends F S, d e) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all_finset]
      intro e he
      have hc : Continuous fun ε : ℝ => y e + ε * d e := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hpos e he)
    · rw [Filter.eventually_all_finset]
      intro S hS
      have hc : Continuous fun ε : ℝ =>
          ∑ e ∈ gcut ends F S, y e + ε * ∑ e ∈ gcut ends F S, d e := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hnt S hS)
  obtain ⟨ε, hε, hε1, hε2⟩ := hev.exists_gt
  refine ⟨ε, hε, fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp [hy.1 e he, hd.1 e he]
  · by_cases he : e ∈ F
    · exact (hε1 e he).le
    · simp [hy.1 e he, hd.1 e he]
  · rw [sum_add_smul, hy.2.2.1 v hv, hd.2 v hv]; ring
  · rw [sum_add_smul]
    by_cases h1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h1
      have hv : v ∈ W := hS (Finset.mem_singleton_self v)
      rw [hy.2.2.1 v hv, hd.2 v hv]; norm_num
    by_cases h2 : (W \ S).card = 1
    · obtain ⟨v, hv'⟩ := Finset.card_eq_one.1 h2
      have hv : v ∈ W := Finset.sdiff_subset (hv' ▸ Finset.mem_singleton_self v)
      rw [← gcut_compl hV subset_rfl, hv', hy.2.2.1 v hv, hd.2 v hv]; norm_num
    have hodd' := odd_card_sdiff hS hW hodd
    have hS1 : 1 < S.card := by
      obtain ⟨k, hk⟩ := hodd; omega
    have hS2 : 1 < (W \ S).card := by
      obtain ⟨k, hk⟩ := hodd'; omega
    have := hε2 S (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hS, hodd, hS1, hS2⟩)
    exact this.le

lemma exists_neg_of_ker (hV : Valid ends W F) {d : E → ℝ} (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ e, d e < 0 := by
  by_contra h
  push Not at h
  apply hd0
  funext e
  by_cases he : e ∈ F
  · obtain ⟨a, b, -, ha, -, hab⟩ := hV.pair he
    have hsum := hd.2 a ha
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => h e)] at hsum
    exact hsum e ((mem_gcut_singleton hV subset_rfl).2 ⟨he, by simp [hab]⟩)
  · exact hd.1 e he

/-- Moving from an irreducible point along a nonzero kernel direction reaches a reducible
point. -/
lemma exists_reducible_along [DecidableEq V] (hV : Valid ends W F) {x d : E → ℝ}
    (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ Poly ends W F ∧ Reducible ends W F (x + t • d) := by
  obtain ⟨e₀, he₀⟩ := exists_neg_of_ker hV hd hd0
  set T : Set ℝ := {t | 0 ≤ t ∧ x + t • d ∈ Poly ends W F} with hT
  have hbdd : BddAbove T := by
    refine ⟨x e₀ / -d e₀, fun t ht => ?_⟩
    have h := ht.2.2.1 e₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcl : IsClosed T := by
    have : T = Set.Ici 0 ∩ (fun t : ℝ => x + t • d) ⁻¹' Poly ends W F := rfl
    rw [this]
    exact isClosed_Ici.inter ((isClosed_poly ends W F).preimage (by fun_prop))
  have hne : T.Nonempty := ⟨0, le_rfl, by simpa using hx⟩
  have hmem := hcl.csSup_mem hne hbdd
  obtain ⟨ε, hε, hεmem⟩ := exists_pos_add_mem hV hx hirr hd
  have hpos : 0 < sSup T := lt_of_lt_of_le hε (le_csSup hbdd ⟨hε.le, hεmem⟩)
  refine ⟨sSup T, hpos, hmem.2, ?_⟩
  by_contra hred
  obtain ⟨ε', hε', hmem'⟩ := exists_pos_add_mem hV hmem.2 hred hd
  have : sSup T + ε' ∈ T := by
    refine ⟨by linarith, ?_⟩
    have heq : x + (sSup T + ε') • d = x + sSup T • d + ε' • d := by
      rw [add_smul, add_assoc]
    rw [heq]; exact hmem'
  have := le_csSup hbdd this
  linarith

/-! ### The injective case -/

lemma exists_ker_of_card_lt [Finite E] (hlt : W.card < F.card) :
    ∃ d, Ker ends W F d ∧ d ≠ 0 := by
  classical
  have := Fintype.ofFinite E
  let L : (E → ℝ) →ₗ[ℝ] (W → ℝ) × ((univ \ F : Finset E) → ℝ) :=
    (LinearMap.pi fun v : W => ∑ e ∈ gcut ends F {(v : V)}, LinearMap.proj e).prod
      (LinearMap.pi fun e : (univ \ F : Finset E) => LinearMap.proj (e : E))
  have hrank : Module.finrank ℝ ((W → ℝ) × ((univ \ F : Finset E) → ℝ)) <
      Module.finrank ℝ (E → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have := Finset.card_le_univ F
    omega
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt hrank
    (f := L))
  rw [LinearMap.mem_ker] at hd
  refine ⟨d, ⟨fun e he => ?_, fun v hv => ?_⟩, hd0⟩
  · have := congrArg (fun p => p.2 ⟨e, by simp [he]⟩) hd
    simpa [L] using this
  · have := congrArg (fun p => p.1 ⟨v, hv⟩) hd
    simpa [L] using this

lemma exists_pm_small (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hW4 : W.card ≤ 4) : ∃ M, IsPM ends W F M := by
  classical
  have hW := even_card_of_mem_poly hV hx
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · refine ⟨∅, Finset.empty_subset _, fun v hv => ?_⟩
    rw [Finset.card_eq_zero.1 h0] at hv
    simp at hv
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  have hsa := hx.2.2.1 a ha
  obtain ⟨e, he, hxe⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsa]; norm_num :
    ∑ e ∈ gcut ends F {a}, x e ≠ 0)
  rw [mem_gcut_singleton hV subset_rfl] at he
  obtain ⟨heF, hae⟩ := he
  obtain ⟨b, hba, hbW, hab⟩ := hV.pair_of_mem heF hae
  have hxe' : 0 < x e := lt_of_le_of_ne (hx.2.1 e) (Ne.symm hxe)
  set A : Finset V := {a, b} with hA
  have hAW : A ⊆ W := by
    intro u hu; simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have hAcard : A.card = 2 := Finset.card_pair (Ne.symm hba)
  have hmemA : ∀ v, v ∈ ends e ↔ v ∈ A := by
    intro v; rw [hab]; simp [hA]
  obtain ⟨k, hk⟩ := hW
  have hcases : W.card = 2 ∨ W.card = 4 := by omega
  rcases hcases with h2 | h4
  · -- `W = {a, b}` and `{e}` is a perfect matching
    have hWA : W = A := (Finset.eq_of_subset_of_card_le hAW (by omega)).symm
    refine ⟨{e}, Finset.singleton_subset_iff.2 heF, fun v hv => ?_⟩
    rw [Finset.card_eq_one]
    refine ⟨e, ?_⟩
    ext e'
    rw [mem_gcut_singleton hV (Finset.singleton_subset_iff.2 heF), Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, (hmemA v).2 (hWA ▸ hv)⟩
  · set B := W \ A with hB
    have hBcard : B.card = 2 := by
      have := Finset.card_sdiff_add_card_eq_card hAW
      rw [← hB] at this
      omega
    have hBW : B ⊆ W := Finset.sdiff_subset
    -- the inner weights of `A` and `B` agree
    have hA2 := sum_degree hV subset_rfl A x
    have hB2 := sum_degree hV subset_rfl B x
    rw [Finset.sum_congr rfl (fun v hv => hx.2.2.1 v (hAW hv))] at hA2
    rw [Finset.sum_congr rfl (fun v hv => hx.2.2.1 v (hBW hv))] at hB2
    rw [hB, gcut_compl hV subset_rfl] at hB2
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hA2 hB2
    rw [hAcard] at hA2
    rw [← hB, hBcard] at hB2
    have heA : e ∈ inside ends F A := by
      rw [mem_inside_of_pair hab]
      exact ⟨heF, by simp [hA], by simp [hA]⟩
    have hinA : x e ≤ ∑ e ∈ inside ends F A, x e :=
      Finset.single_le_sum (fun e _ => hx.2.1 e) heA
    have hinB : ∑ e ∈ inside ends F B, x e ≠ 0 := by
      push_cast at hA2 hB2
      linarith
    obtain ⟨g, hg, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinB
    simp only [inside, Finset.mem_filter] at hg
    obtain ⟨hgF, hgB⟩ := hg
    obtain ⟨c, c', hcc', -, -, hgc⟩ := hV.pair hgF
    have hcB : c ∈ B := hgB c (by simp [hgc])
    have hc'B : c' ∈ B := hgB c' (by simp [hgc])
    have hmemB : ∀ v, v ∈ ends g ↔ v ∈ B := by
      intro v
      constructor
      · exact hgB v
      · intro hv
        by_contra hvg
        rw [hgc, Sym2.mem_iff, not_or] at hvg
        have hsub : ({v, c, c'} : Finset V) ⊆ B := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hvg.1, hvg.2]),
          Finset.card_pair hcc'] at this
        omega
    have hdisj : ∀ v, v ∈ A → v ∉ B := fun v hv hvB => (Finset.mem_sdiff.1 hvB).2 hv
    have heg : e ≠ g := by
      rintro rfl
      exact hdisj a (by simp [hA]) ((hmemB a).1 hae)
    have hMF : ({e, g} : Finset E) ⊆ F := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    refine ⟨{e, g}, hMF, fun v hv => ?_⟩
    rw [Finset.card_eq_one]
    by_cases hvA : v ∈ A
    · refine ⟨e, ?_⟩
      ext e'
      rw [mem_gcut_singleton hV hMF, Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · exact absurd ((hmemB v).1 h) (hdisj v hvA)
      · rintro rfl; exact ⟨Or.inl rfl, (hmemA v).2 hvA⟩
    · have hvB : v ∈ B := Finset.mem_sdiff.2 ⟨hv, hvA⟩
      refine ⟨g, ?_⟩
      ext e'
      rw [mem_gcut_singleton hV hMF, Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · exact absurd ((hmemA v).1 h) hvA
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, (hmemB v).2 hvB⟩

/-- In an irreducible point of a multigraph with at least five vertices, every vertex has
degree at least three. -/
lemma three_le_card_gcut [DecidableEq V] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hW5 : 5 ≤ W.card) {v : V} (hv : v ∈ W) :
    3 ≤ (gcut ends F {v}).card := by
  classical
  by_contra hlt
  push Not at hlt
  set N : Finset V := insert v ((gcut ends F {v}).biUnion
    fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v) with hN
  have hinner : ∀ e ∈ gcut ends F {v}, (W.filter fun u => u ∈ ends e ∧ u ≠ v).card ≤ 1 := by
    intro e he
    rw [mem_gcut_singleton hV subset_rfl] at he
    obtain ⟨b, -, -, hb⟩ := hV.pair_of_mem he.1 he.2
    apply Finset.card_le_one.2
    intro u hu u' hu'
    simp only [Finset.mem_filter, hb, Sym2.mem_iff] at hu hu'
    rcases hu.2.1 with h | h
    · exact absurd h hu.2.2
    rcases hu'.2.1 with h' | h'
    · exact absurd h' hu'.2.2
    rw [h, h']
  have hNcard : N.card ≤ 3 := by
    have h1 := Finset.card_insert_le v ((gcut ends F {v}).biUnion
      fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v)
    have h2 := Finset.card_biUnion_le (s := gcut ends F {v})
      (t := fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v)
    have h3 : ∑ e ∈ gcut ends F {v}, (W.filter fun u => u ∈ ends e ∧ u ≠ v).card ≤
        ∑ e ∈ gcut ends F {v}, 1 := Finset.sum_le_sum hinner
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h3
    rw [← hN] at h1
    omega
  have hNW : N ⊆ W := by
    intro u hu
    rw [hN, Finset.mem_insert, Finset.mem_biUnion] at hu
    rcases hu with rfl | ⟨e, -, hu⟩
    · exact hv
    · exact (Finset.mem_filter.1 hu).1
  obtain ⟨S, hNS, hSW, hS3⟩ := Finset.exists_subsuperset_card_eq hNW hNcard (by omega)
  have hsub : gcut ends F {v} ⊆ inside ends F S := by
    intro e he
    have he' := (mem_gcut_singleton hV subset_rfl).1 he
    simp only [inside, Finset.mem_filter]
    refine ⟨he'.1, fun u hu => hNS ?_⟩
    by_cases huv : u = v
    · rw [huv, hN]; exact Finset.mem_insert_self _ _
    · rw [hN, Finset.mem_insert, Finset.mem_biUnion]
      exact Or.inr ⟨e, he, Finset.mem_filter.2 ⟨hV.sub e he'.1 u hu, hu, huv⟩⟩
  have hdeg := sum_degree hV subset_rfl S x
  rw [Finset.sum_congr rfl (fun u hu => hx.2.2.1 u (hSW hu))] at hdeg
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hS3] at hdeg
  have hin : 1 ≤ ∑ e ∈ inside ends F S, x e := by
    rw [← hx.2.2.1 v hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx.2.1 e)
  have hodd : Odd S.card := by rw [hS3]; decide
  have hge := hx.2.2.2 S hSW hodd
  apply hirr
  refine Or.inr ⟨S, hSW, hodd, by omega, ?_, ?_⟩
  · have := Finset.card_sdiff_add_card_eq_card hSW
    omega
  · push_cast at hdeg
    linarith

/-! ### The main induction -/

lemma inHull_step [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by
  classical
  by_cases hred : Reducible ends W F x
  · exact inHull_of_reducible IH hV hx hred
  by_cases hk : ∃ d, Ker ends W F d ∧ d ≠ 0
  · obtain ⟨d, hd, hd0⟩ := hk
    have hd' : Ker ends W F (-d) :=
      ⟨fun e he => by simp [hd.1 e he], fun v hv => by simp [hd.2 v hv]⟩
    obtain ⟨t1, ht1, hm1, hr1⟩ := exists_reducible_along hV hx hred hd hd0
    obtain ⟨t2, ht2, hm2, hr2⟩ := exists_reducible_along hV hx hred hd' (neg_ne_zero.2 hd0)
    have h1 := inHull_of_reducible IH hV hm1 hr1
    have h2 := inHull_of_reducible IH hV hm2 hr2
    have hconv := h1.convex h2 (a := t2 / (t1 + t2)) (b := t1 / (t1 + t2)) (by positivity)
      (by positivity) (by field_simp; ring)
    convert hconv using 1
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring
  push Not at hk
  have hFW : F.card ≤ W.card := by
    by_contra h
    obtain ⟨d, hd, hd0⟩ := exists_ker_of_card_lt (ends := ends) (lt_of_not_ge h)
    exact hd0 (hk d hd)
  by_cases hW4 : W.card ≤ 4
  · obtain ⟨M, hM⟩ := exists_pm_small hV hx hW4
    have hchi := chi_mem_poly hV hM
    have hker : Ker ends W F (chi M - x) := by
      refine ⟨fun e he => by simp [hchi.1 e he, hx.1 e he], fun v hv => ?_⟩
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hchi.2.2.1 v hv, hx.2.2.1 v hv, sub_self]
    have := hk _ hker
    rw [sub_eq_zero] at this
    rw [← this]
    exact InHull.of_mem hM
  · exfalso
    have hdeg := sum_degree (β := ℕ) hV subset_rfl W (fun _ => 1)
    rw [gcut_self hV subset_rfl, inside_self hV subset_rfl] at hdeg
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_empty, zero_add] at hdeg
    have h3 : ∑ v ∈ W, 3 ≤ ∑ v ∈ W, (gcut ends F {v}).card :=
      Finset.sum_le_sum fun v hv => three_le_card_gcut hV hx hred (by omega) hv
    simp only [Finset.sum_const, smul_eq_mul] at h3
    omega

/-- **Edmonds' theorem for multigraphs**: every point of the polytope is a convex combination
of perfect matchings. -/
theorem inHull_of_mem_poly [Fintype E] (ends : E → Sym2 V) (W : Finset V) (F : Finset E)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by
  suffices h : ∀ n : ℕ, ∀ (ends : E → Sym2 V) (W : Finset V) (F : Finset E),
      W.card + F.card = n → Valid ends W F → ∀ x ∈ Poly ends W F, InHull (IsPM ends W F) x from
    h _ ends W F rfl hV x hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ends W F hn hV x hx
    exact inHull_step (fun ends' W' F' hlt hV' y hy => ih _ (hn ▸ hlt) ends' W' F' rfl hV' y hy)
      hV hx

end MatchingPolytope.Multi
