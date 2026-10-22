/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MatchingPolytope.Shrink

/-!
# Gluing convex combinations along a tight odd cut

If `x` lies in the polytope, the odd set `S` is tight, and the restrictions of `x` to the two
multigraphs obtained by shrinking `S` and its complement are convex combinations of perfect
matchings, then so is `x`: matchings on both sides are paired up along the cut edges.
-/

@[expose] public section

namespace MatchingPolytope.Multi

open Finset

variable {V E : Type*}

/-- Weights of the glued pairs of matchings. -/
noncomputable def gw (C : Finset E) (x : E → ℝ) (w1 w2 : Finset E → ℝ)
    (p : Finset E × Finset E) : ℝ :=
  ∑ g ∈ C, chi p.1 g * chi p.2 g * w1 p.1 * w2 p.2 / x g

lemma chi_nonneg (M : Finset E) (e : E) : 0 ≤ chi M e := by
  unfold chi; split_ifs <;> norm_num

lemma chi_ne_zero {M : Finset E} {e : E} (h : chi M e ≠ 0) : e ∈ M := by
  unfold chi at h; split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

lemma gw_nonneg {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, 0 < x g) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ M, 0 ≤ w1 M) (h2 : ∀ M, 0 ≤ w2 M) (p : Finset E × Finset E) :
    0 ≤ gw C x w1 w2 p := by
  unfold gw
  apply Finset.sum_nonneg
  intro g hg
  have := hx g hg
  have := chi_nonneg p.1 g
  have := chi_nonneg p.2 g
  have := h1 p.1
  have := h2 p.2
  positivity

lemma gw_ne_zero {C : Finset E} {x : E → ℝ} {w1 w2 : Finset E → ℝ} {p : Finset E × Finset E}
    (h : gw C x w1 w2 p ≠ 0) :
    ∃ g ∈ C, g ∈ p.1 ∧ g ∈ p.2 ∧ w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 := by
  obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨g, hg, chi_ne_zero ?_, chi_ne_zero ?_, ?_, ?_⟩ <;> intro h0 <;> apply hne <;>
    simp [h0]

lemma gw_left [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h2 : ∀ g ∈ C, ∑ N, w2 N * chi N g = x g)
    (h1' : ∀ M, w1 M ≠ 0 → ∑ g ∈ C, chi M g = 1) (φ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * φ p.1 = ∑ M, w1 M * φ M := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro M _
  simp only [gw, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ g ∈ C, ∑ N, chi M g * chi N g * w1 M * w2 N / x g * φ M =
      chi M g * w1 M * φ M := by
    intro g hg
    have e1 : ∀ N, chi M g * chi N g * w1 M * w2 N / x g * φ M =
        (chi M g * w1 M * φ M / x g) * (w2 N * chi N g) := by
      intro N; field_simp
    simp_rw [e1]
    rw [← Finset.mul_sum, h2 g hg]
    field_simp [hx g hg]
  rw [Finset.sum_congr rfl this]
  by_cases hw : w1 M = 0
  · simp [hw]
  · rw [← Finset.sum_mul, ← Finset.sum_mul, h1' M hw]
    ring

lemma gw_swap (C : Finset E) (x : E → ℝ) (w1 w2 : Finset E → ℝ) (p : Finset E × Finset E) :
    gw C x w1 w2 p = gw C x w2 w1 p.swap := by
  unfold gw
  apply Finset.sum_congr rfl
  intro g _
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

lemma gw_right [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ g ∈ C, ∑ M, w1 M * chi M g = x g)
    (h2' : ∀ N, w2 N ≠ 0 → ∑ g ∈ C, chi N g = 1) (ψ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * ψ p.2 = ∑ N, w2 N * ψ N := by
  rw [← gw_left hx h1 h2' ψ]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => by rw [gw_swap]; rfl)

variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

lemma gcut_union [DecidableEq E] (M N : Finset E) (T : Finset V) :
    gcut ends (M ∪ N) T = gcut ends M T ∪ gcut ends N T := by
  classical
  ext e
  simp [gcut, or_and_right]

lemma gcut_subset_shrinkF {S R : Finset V} (h : ∀ u, u ∉ S → u ∉ R) :
    gcut ends F S ⊆ shrinkF ends F R := by
  intro e he
  simp only [gcut, Finset.mem_filter] at he
  obtain ⟨heF, -, u, hu, huS⟩ := he
  exact mem_shrinkF.2 ⟨heF, u, hu, h u huS⟩

variable [DecidableEq V]

/-- Gluing two matchings that agree on the cut of `S`. -/
lemma isPM_union [DecidableEq E] (hV : Valid ends W F) {S : Finset V} {M N : Finset E}
    (hM : M ⊆ shrinkF ends F S) (hN : N ⊆ shrinkF ends F (W \ S))
    (hcut : gcut ends M S = gcut ends N S)
    (hMdeg : ∀ v ∈ W, v ∉ S → (gcut ends M {v}).card = 1)
    (hNdeg : ∀ v ∈ W, v ∈ S → (gcut ends N {v}).card = 1) :
    IsPM ends W F (M ∪ N) := by
  have hMF : M ⊆ F := hM.trans (shrinkF_subset _)
  have hNF : N ⊆ F := hN.trans (shrinkF_subset _)
  refine ⟨Finset.union_subset hMF hNF, fun v hv => ?_⟩
  rw [gcut_union]
  by_cases hvS : v ∈ S
  · have : gcut ends M {v} ⊆ gcut ends N {v} := by
      intro e he
      rw [mem_gcut_singleton hV hMF] at he
      obtain ⟨heM, hve⟩ := he
      obtain ⟨-, u, hu, huS⟩ := mem_shrinkF.1 (hM heM)
      have : e ∈ gcut ends M S := by
        simp only [gcut, Finset.mem_filter]
        exact ⟨heM, ⟨v, hve, hvS⟩, ⟨u, hu, huS⟩⟩
      rw [hcut] at this
      rw [mem_gcut_singleton hV hNF]
      exact ⟨gcut_subset _ _ this, hve⟩
    rw [Finset.union_eq_right.2 this]
    exact hNdeg v hv hvS
  · have : gcut ends N {v} ⊆ gcut ends M {v} := by
      intro e he
      rw [mem_gcut_singleton hV hNF] at he
      obtain ⟨heN, hve⟩ := he
      obtain ⟨-, u, hu, huS⟩ := mem_shrinkF.1 (hN heN)
      have huS' : u ∈ S := by
        by_contra h
        exact huS (Finset.mem_sdiff.2 ⟨hV.sub e (hNF heN) u hu, h⟩)
      have : e ∈ gcut ends N S := by
        simp only [gcut, Finset.mem_filter]
        exact ⟨heN, ⟨u, hu, huS'⟩, ⟨v, hve, hvS⟩⟩
      rw [← hcut] at this
      rw [mem_gcut_singleton hV hMF]
      exact ⟨gcut_subset _ _ this, hve⟩
    rw [Finset.union_eq_left.2 this]
    exact hMdeg v hv hvS

lemma mem_gcut_of_mem_both (hV : Valid ends W F) {S : Finset V} {e : E}
    (h1 : e ∈ shrinkF ends F S) (h2 : e ∈ shrinkF ends F (W \ S)) : e ∈ gcut ends F S := by
  obtain ⟨heF, u, hu, huS⟩ := mem_shrinkF.1 h1
  obtain ⟨-, u', hu', hu'S⟩ := mem_shrinkF.1 h2
  have : u' ∈ S := by
    by_contra h
    exact hu'S (Finset.mem_sdiff.2 ⟨hV.sub e heF u' hu', h⟩)
  simp only [gcut, Finset.mem_filter]
  exact ⟨heF, ⟨u', hu', this⟩, ⟨u, hu, huS⟩⟩

lemma gcut_subset_shrinkF' (S : Finset V) :
    gcut ends F S ⊆ shrinkF ends F (W \ S) := by
  intro e he
  simp only [gcut, Finset.mem_filter] at he
  obtain ⟨heF, ⟨u, hu, huS⟩, -⟩ := he
  exact mem_shrinkF.2 ⟨heF, u, hu, fun h => (Finset.mem_sdiff.1 h).2 huS⟩

lemma mem_shrinkF_or (hV : Valid ends W F) {S : Finset V} {e : E} (he : e ∈ F) :
    e ∈ shrinkF ends F S ∨ e ∈ shrinkF ends F (W \ S) := by
  obtain ⟨a, b, -, ha, -, h⟩ := hV.pair he
  by_cases haS : a ∈ S
  · right; exact mem_shrinkF.2 ⟨he, a, by simp [h], fun h' => (Finset.mem_sdiff.1 h').2 haS⟩
  · left; exact mem_shrinkF.2 ⟨he, a, by simp [h], haS⟩

lemma eval_sum_smul_chi [Fintype E] (w : Finset E → ℝ) (e : E) :
    (∑ M, w M • chi M) e = ∑ M, w M * chi M e := by
  simp [Finset.sum_apply]

/-- The gluing step of Schrijver's proof. -/
theorem inHull_glue [Fintype E] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hpos : ∀ e ∈ F, 0 < x e) {S : Finset V} (hSW : S ⊆ W) {s t : V} (hs : s ∈ S)
    (ht : t ∈ W \ S)
    (h1 : InHull (IsPM (shrinkEnds ends S s) (shrinkW W S s) (shrinkF ends F S))
      (restr (shrinkF ends F S) x))
    (h2 : InHull (IsPM (shrinkEnds ends (W \ S) t) (shrinkW W (W \ S) t)
      (shrinkF ends F (W \ S))) (restr (shrinkF ends F (W \ S)) x)) :
    InHull (IsPM ends W F) x := by
  classical
  set F1 := shrinkF ends F S with hF1
  set F2 := shrinkF ends F (W \ S) with hF2
  set C := gcut ends F S with hC
  obtain ⟨w1, h10, h11, h12, h13⟩ := h1
  obtain ⟨w2, h20, h21, h22, h23⟩ := h2
  have hS' : W \ S ⊆ W := Finset.sdiff_subset
  have hWS : W \ (W \ S) = S := Finset.sdiff_sdiff_eq_self hSW
  -- properties of the matchings on each side
  have pm1 : ∀ M, w1 M ≠ 0 → M ⊆ F1 ∧ (gcut ends M S).card = 1 ∧
      ∀ v ∈ W, v ∉ S → (gcut ends M {v}).card = 1 :=
    fun M hM => (h11 M hM).of_shrink hV hSW hs
  have pm2 : ∀ N, w2 N ≠ 0 → N ⊆ F2 ∧ (gcut ends N S).card = 1 ∧
      ∀ v ∈ W, v ∈ S → (gcut ends N {v}).card = 1 := by
    intro N hN
    obtain ⟨a, b, c⟩ := (h21 N hN).of_shrink hV hS' ht
    refine ⟨a, ?_, fun v hv hvS => c v hv (fun h => (Finset.mem_sdiff.1 h).2 hvS)⟩
    rwa [gcut_compl hV (a.trans (shrinkF_subset _))] at b
  have hCF1 : C ⊆ F1 := gcut_subset_shrinkF (fun u hu => hu)
  have hCF2 : C ⊆ F2 := gcut_subset_shrinkF' S
  have hxC : ∀ g ∈ C, x g ≠ 0 := fun g hg => (hpos g (gcut_subset _ _ hg)).ne'
  have ev1 : ∀ e, ∑ M, w1 M * chi M e = restr F1 x e := fun e => by
    rw [← h13, eval_sum_smul_chi]
  have ev2 : ∀ e, ∑ N, w2 N * chi N e = restr F2 x e := fun e => by
    rw [← h23, eval_sum_smul_chi]
  have hc1 : ∀ g ∈ C, ∑ M, w1 M * chi M g = x g := fun g hg => by
    rw [ev1]; simp [restr, hCF1 hg]
  have hc2 : ∀ g ∈ C, ∑ N, w2 N * chi N g = x g := fun g hg => by
    rw [ev2]; simp [restr, hCF2 hg]
  have hd1 : ∀ M, w1 M ≠ 0 → ∑ g ∈ C, chi M g = 1 := fun M hM => by
    obtain ⟨a, b, -⟩ := pm1 M hM
    rw [hC, sum_chi_gcut (a.trans (shrinkF_subset _)), b]; simp
  have hd2 : ∀ N, w2 N ≠ 0 → ∑ g ∈ C, chi N g = 1 := fun N hN => by
    obtain ⟨a, b, -⟩ := pm2 N hN
    rw [hC, sum_chi_gcut (a.trans (shrinkF_subset _)), b]; simp
  -- a nonzero glued weight gives two matchings with the same cut edge
  have hpair : ∀ p : Finset E × Finset E, gw C x w1 w2 p ≠ 0 →
      gcut ends p.1 S = gcut ends p.2 S ∧ w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 := by
    intro p hp
    obtain ⟨g, hgC, hg1, hg2, hw1, hw2⟩ := gw_ne_zero hp
    obtain ⟨a1, b1, -⟩ := pm1 _ hw1
    obtain ⟨a2, b2, -⟩ := pm2 _ hw2
    have hgC' := hgC
    simp only [hC, gcut, Finset.mem_filter] at hgC'
    have m1 : g ∈ gcut ends p.1 S := by
      simp only [gcut, Finset.mem_filter]; exact ⟨hg1, hgC'.2⟩
    have m2 : g ∈ gcut ends p.2 S := by
      simp only [gcut, Finset.mem_filter]; exact ⟨hg2, hgC'.2⟩
    obtain ⟨g1, hg1'⟩ := Finset.card_eq_one.1 b1
    obtain ⟨g2, hg2'⟩ := Finset.card_eq_one.1 b2
    rw [hg1'] at m1 ⊢
    rw [hg2'] at m2 ⊢
    rw [Finset.mem_singleton] at m1 m2
    exact ⟨by rw [← m1, ← m2], hw1, hw2⟩
  have hsum : ∑ p, gw C x w1 w2 p = 1 := by
    have := gw_left hxC hc2 hd1 (fun _ => 1)
    simp only [mul_one] at this
    rw [this, h12]
  have key := InHull.push (Q := IsPM ends W F) (gw C x w1 w2) (gw_nonneg
    (fun g hg => hpos g (gcut_subset _ _ hg)) h10 h20) hsum (fun p => p.1 ∪ p.2) (by
      intro p hp
      obtain ⟨hcut, hw1, hw2⟩ := hpair p hp
      obtain ⟨a1, -, c1⟩ := pm1 _ hw1
      obtain ⟨a2, -, c2⟩ := pm2 _ hw2
      exact isPM_union hV a1 a2 hcut c1 c2)
  convert key using 1
  funext e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases he : e ∈ F1 ∨ e ∉ F2
  · have hterm : ∀ p : Finset E × Finset E,
        gw C x w1 w2 p * chi (p.1 ∪ p.2) e = gw C x w1 w2 p * chi p.1 e := by
      intro p
      by_cases hp : gw C x w1 w2 p = 0
      · simp [hp]
      obtain ⟨hcut, hw1, hw2⟩ := hpair p hp
      obtain ⟨a2, -, -⟩ := pm2 _ hw2
      congr 1
      have : e ∈ p.2 → e ∈ p.1 := by
        intro he2
        have heF2 : e ∈ F2 := a2 he2
        have heF1 : e ∈ F1 := he.resolve_right (not_not.2 heF2)
        have heC : e ∈ gcut ends p.2 S := by
          have := mem_gcut_of_mem_both hV heF1 heF2
          simp only [gcut, Finset.mem_filter] at this ⊢
          exact ⟨he2, this.2⟩
        rw [← hcut] at heC
        exact gcut_subset _ _ heC
      simp only [chi, Finset.mem_union]
      by_cases h1 : e ∈ p.1
      · simp [h1]
      · simp [h1, show e ∉ p.2 from fun h => h1 (this h)]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), gw_left hxC hc2 hd1 (fun M => chi M e), ev1]
    simp only [restr]
    split_ifs with h
    · rfl
    · have heF : e ∉ F := by
        intro heF
        rcases mem_shrinkF_or hV (S := S) heF with h' | h'
        · exact h h'
        · exact (he.resolve_left h) h'
      exact hx.1 e heF
  · push Not at he
    obtain ⟨he1, he2⟩ := he
    have hterm : ∀ p : Finset E × Finset E,
        gw C x w1 w2 p * chi (p.1 ∪ p.2) e = gw C x w1 w2 p * chi p.2 e := by
      intro p
      by_cases hp : gw C x w1 w2 p = 0
      · simp [hp]
      obtain ⟨-, hw1, -⟩ := hpair p hp
      obtain ⟨a1, -, -⟩ := pm1 _ hw1
      congr 1
      have : e ∉ p.1 := fun h => he1 (a1 h)
      simp [chi, this]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), gw_right hxC hc1 hd2 (fun N => chi N e), ev2]
    simp [restr, he2]

end MatchingPolytope.Multi
