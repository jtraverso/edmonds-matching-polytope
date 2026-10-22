/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Perfect matchings in finite multigraphs: basic definitions

To run Schrijver's induction (which shrinks vertex sets and therefore creates parallel edges),
we work with a fixed vertex type `V` and a fixed finite edge type `E`, together with

* an endpoint map `ends : E → Sym2 V`,
* an active vertex set `W : Finset V`,
* an active edge set `F : Finset E`.

All edges of `F` are required to be non-loops with endpoints in `W` (`Valid`).
Shrinking a vertex set then only changes `ends`, `W` and `F`, never the types.
-/

@[expose] public section

namespace MatchingPolytope.Multi

open Finset

variable {V E : Type*}

open Classical in
/-- The edges of `F` with exactly one endpoint in `S`. -/
noncomputable def gcut (ends : E → Sym2 V) (F : Finset E) (S : Finset V) : Finset E :=
  F.filter fun e => (∃ u ∈ ends e, u ∈ S) ∧ ∃ u ∈ ends e, u ∉ S

open Classical in
/-- The edges of `F` with both endpoints in `S`. -/
noncomputable def inside (ends : E → Sym2 V) (F : Finset E) (S : Finset V) : Finset E :=
  F.filter fun e => ∀ u ∈ ends e, u ∈ S

/-- Well-formedness: active edges are non-loops with active endpoints. -/
structure Valid (ends : E → Sym2 V) (W : Finset V) (F : Finset E) : Prop where
  sub : ∀ e ∈ F, ∀ u ∈ ends e, u ∈ W
  nodiag : ∀ e ∈ F, ¬ (ends e).IsDiag

/-- The perfect matching polytope (Edmonds' description) of the multigraph `(W, F)`. -/
def Poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) : Set (E → ℝ) :=
  {x | (∀ e, e ∉ F → x e = 0) ∧ (∀ e, 0 ≤ x e) ∧ (∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1) ∧
    ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e}

/-- `M` is a perfect matching of `(W, F)`. -/
def IsPM (ends : E → Sym2 V) (W : Finset V) (F : Finset E) (M : Finset E) : Prop :=
  M ⊆ F ∧ ∀ v ∈ W, (gcut ends M {v}).card = 1

open Classical in
/-- Incidence vector of an edge set. -/
noncomputable def chi (M : Finset E) : E → ℝ := fun e => if e ∈ M then 1 else 0

/-- `x` is a convex combination of incidence vectors of edge sets satisfying `Q`. -/
def InHull [Fintype E] (Q : Finset E → Prop) (x : E → ℝ) : Prop :=
  ∃ w : Finset E → ℝ, (∀ M, 0 ≤ w M) ∧ (∀ M, w M ≠ 0 → Q M) ∧ ∑ M, w M = 1 ∧
    ∑ M, w M • chi M = x

open Classical in
/-- Restriction of a vector to an edge set (zero elsewhere). -/
noncomputable def restr (F : Finset E) (x : E → ℝ) : E → ℝ := fun e => if e ∈ F then x e else 0

/-- The kernel of the degree map, restricted to vectors supported on `F`. -/
def Ker (ends : E → Sym2 V) (W : Finset V) (F : Finset E) (d : E → ℝ) : Prop :=
  (∀ e, e ∉ F → d e = 0) ∧ ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, d e = 0

/-! ### Endpoints -/

lemma exists_pair (z : Sym2 V) : ∃ a b, z = s(a, b) := by
  induction z using Sym2.ind with
  | h a b => exact ⟨a, b, rfl⟩

lemma mem_gcut_of_pair {ends : E → Sym2 V} {F : Finset E} {S : Finset V} {e : E} {a b : V}
    (h : ends e = s(a, b)) :
    e ∈ gcut ends F S ↔ e ∈ F ∧ (a ∈ S ∨ b ∈ S) ∧ (a ∉ S ∨ b ∉ S) := by
  simp [gcut, h]

lemma mem_inside_of_pair {ends : E → Sym2 V} {F : Finset E} {S : Finset V} {e : E} {a b : V}
    (h : ends e = s(a, b)) :
    e ∈ inside ends F S ↔ e ∈ F ∧ a ∈ S ∧ b ∈ S := by
  simp [inside, h]

variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

lemma Valid.pair (hV : Valid ends W F) {e : E} (he : e ∈ F) :
    ∃ a b, a ≠ b ∧ a ∈ W ∧ b ∈ W ∧ ends e = s(a, b) := by
  obtain ⟨a, b, h⟩ := exists_pair (ends e)
  refine ⟨a, b, ?_, hV.sub e he a (by simp [h]), hV.sub e he b (by simp [h]), h⟩
  intro hab
  exact hV.nodiag e he (by simp [h, hab])

lemma Valid.mono {F' : Finset E} (hV : Valid ends W F) (h : F' ⊆ F) : Valid ends W F' :=
  ⟨fun e he => hV.sub e (h he), fun e he => hV.nodiag e (h he)⟩

lemma Valid.pair_of_mem (hV : Valid ends W F) {e : E} (he : e ∈ F) {v : V} (hv : v ∈ ends e) :
    ∃ b, b ≠ v ∧ b ∈ W ∧ ends e = s(v, b) := by
  obtain ⟨a, b, hab, ha, hb, h⟩ := hV.pair he
  rw [h, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, hab.symm, hb, h⟩
  · exact ⟨a, hab, ha, h.trans Sym2.eq_swap⟩

lemma mem_gcut_singleton_of_nodiag {D : Finset E} (hD : ∀ e ∈ D, ¬ (ends e).IsDiag) {e : E}
    {v : V} : e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e := by
  classical
  constructor
  · intro h
    obtain ⟨hD', ⟨u, hu, hu'⟩, -⟩ := Finset.mem_filter.1 h
    rw [Finset.mem_singleton] at hu'
    exact ⟨hD', hu' ▸ hu⟩
  · rintro ⟨he, hv⟩
    obtain ⟨a, b, h⟩ := exists_pair (ends e)
    have hab : a ≠ b := fun hab => hD e he (by simp [h, hab])
    rw [mem_gcut_of_pair h]
    rw [h, Sym2.mem_iff] at hv
    refine ⟨he, ?_⟩
    rcases hv with rfl | rfl
    · simp [Ne.symm hab]
    · simp [hab]

lemma mem_gcut_singleton (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) {e : E} {v : V} :
    e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e :=
  mem_gcut_singleton_of_nodiag fun e he => hV.nodiag e (hD he)

lemma gcut_subset (D : Finset E) (S : Finset V) : gcut ends D S ⊆ D := by
  classical exact Finset.filter_subset _ _

lemma inside_subset (D : Finset E) (S : Finset V) : inside ends D S ⊆ D := by
  classical exact Finset.filter_subset _ _

lemma gcut_mono {D D' : Finset E} (h : D ⊆ D') (S : Finset V) : gcut ends D S ⊆ gcut ends D' S := by
  classical exact Finset.filter_subset_filter _ h

lemma gcut_compl [DecidableEq V] (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) (S : Finset V) :
    gcut ends D (W \ S) = gcut ends D S := by
  ext e
  constructor
  · intro h
    have he := gcut_subset D _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h ⊢
    simp only [Finset.mem_sdiff] at h
    tauto
  · intro h
    have he := gcut_subset D _ h
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_gcut_of_pair hab] at h ⊢
    simp only [Finset.mem_sdiff]
    tauto

lemma gcut_self (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) : gcut ends D W = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro h
  have he := gcut_subset D _ h
  obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
  rw [mem_gcut_of_pair hab] at h
  tauto

lemma inside_self (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) : inside ends D W = D := by
  ext e
  constructor
  · exact fun h => inside_subset D W h
  · intro he
    obtain ⟨a, b, -, ha, hb, hab⟩ := hV.pair (hD he)
    rw [mem_inside_of_pair hab]
    exact ⟨he, ha, hb⟩

/-- Double counting: summing degrees over `S` counts cut edges once and inner edges twice. -/
lemma sum_degree {β : Type*} [AddCommMonoid β] (hV : Valid ends W F) {D : Finset E}
    (hD : D ⊆ F) (S : Finset V) (x : E → β) :
    ∑ v ∈ S, ∑ e ∈ gcut ends D {v}, x e =
      ∑ e ∈ gcut ends D S, x e + 2 • ∑ e ∈ inside ends D S, x e := by
  classical
  have h1 : ∀ v, ∑ e ∈ gcut ends D {v}, x e = ∑ e ∈ D, if v ∈ ends e then x e else 0 := by
    intro v
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    rw [mem_gcut_singleton hV hD, Finset.mem_filter]
  simp_rw [h1]
  rw [Finset.sum_comm, gcut, inside, Finset.sum_filter, Finset.sum_filter, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨a, b, hab, -, -, h⟩ := hV.pair (hD he)
  have h2 : ∀ v, (if v ∈ ends e then x e else 0) =
      (if v = a then x e else 0) + (if v = b then x e else 0) := by
    intro v
    by_cases hva : v = a
    · subst hva; simp [h, hab]
    · simp [h, hva]
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [h, Sym2.mem_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, two_smul]

lemma even_card_of_mem_poly (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    Even W.card := by
  by_contra h
  have := hx.2.2.2 W subset_rfl (Nat.not_even_iff_odd.1 h)
  rw [gcut_self hV subset_rfl] at this
  simp at this
  linarith

lemma sum_chi_gcut {M D : Finset E} (hM : M ⊆ D) (S : Finset V) :
    ∑ e ∈ gcut ends D S, chi M e = ((gcut ends M S).card : ℝ) := by
  classical
  simp only [chi]
  rw [Finset.sum_boole]
  congr 2
  ext e
  simp only [gcut, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, h⟩, hm⟩; exact ⟨hm, h⟩
  · rintro ⟨hm, h⟩; exact ⟨⟨hM hm, h⟩, hm⟩

lemma sum_chi_inside {M D : Finset E} (hM : M ⊆ D) (S : Finset V) :
    ∑ e ∈ inside ends D S, chi M e = ((inside ends M S).card : ℝ) := by
  classical
  simp only [chi]
  rw [Finset.sum_boole]
  congr 2
  ext e
  simp only [inside, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, h⟩, hm⟩; exact ⟨hm, h⟩
  · rintro ⟨hm, h⟩; exact ⟨⟨hM hm, h⟩, hm⟩

lemma card_gcut_odd (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) {S : Finset V}
    (hS : S ⊆ W) (hodd : Odd S.card) : Odd (gcut ends M S).card := by
  have h := sum_degree (β := ℕ) hV hM.1 S (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [Finset.sum_congr rfl (fun v hv => hM.2 v (hS hv))] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h] at hodd
  rcases Nat.even_or_odd (gcut ends M S).card with he | ho
  · exfalso
    rw [Nat.odd_iff] at hodd
    obtain ⟨k, hk⟩ := he
    omega
  · exact ho

lemma chi_mem_poly (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) :
    chi M ∈ Poly ends W F := by
  refine ⟨fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp only [chi, ite_eq_right_iff]; exact fun h => absurd (hM.1 h) he
  · simp only [chi]; split_ifs <;> norm_num
  · rw [sum_chi_gcut hM.1, hM.2 v hv]; simp
  · rw [sum_chi_gcut hM.1]
    have := (card_gcut_odd hV hM hS hodd).pos
    exact_mod_cast this

/-! ### Convex combinations -/

section Hull

variable [Fintype E]

lemma InHull.of_mem {Q : Finset E → Prop} {M : Finset E} (hM : Q M) : InHull Q (chi M) := by
  classical
  refine ⟨fun N => if N = M then 1 else 0, fun N => by dsimp only; split_ifs <;> norm_num,
    fun N hN => ?_, by simp, by simp⟩
  dsimp only at hN
  split_ifs at hN with h
  · exact h ▸ hM
  · exact absurd rfl hN

lemma InHull.mono {Q Q' : Finset E → Prop} (hQ : ∀ M, Q M → Q' M) {x : E → ℝ}
    (h : InHull Q x) : InHull Q' x := by
  obtain ⟨w, h0, h1, h2, h3⟩ := h
  exact ⟨w, h0, fun M hM => hQ M (h1 M hM), h2, h3⟩

lemma InHull.convex {Q : Finset E → Prop} {x y : E → ℝ} (hx : InHull Q x) (hy : InHull Q y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : InHull Q (a • x + b • y) := by
  obtain ⟨w, h0, h1, h2, h3⟩ := hx
  obtain ⟨u, g0, g1, g2, g3⟩ := hy
  refine ⟨fun M => a * w M + b * u M, fun M => by have := h0 M; have := g0 M; positivity,
    fun M hM => ?_, ?_, ?_⟩
  · by_cases hw : w M = 0
    · have : u M ≠ 0 := by intro hu; apply hM; simp [hw, hu]
      exact g1 M this
    · exact h1 M hw
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h2, g2]; simpa using hab
  · rw [← h3, ← g3, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro M _
    rw [add_smul, mul_smul, mul_smul]

/-- Pushing forward a probability vector along a map to edge sets. -/
lemma InHull.push {ι : Type*} [Fintype ι] {Q : Finset E → Prop} (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∑ i, c i = 1) (φ : ι → Finset E) (hφ : ∀ i, c i ≠ 0 → Q (φ i)) :
    InHull Q (∑ i, c i • chi (φ i)) := by
  classical
  refine ⟨fun M => ∑ i ∈ univ.filter (fun i => φ i = M), c i,
    fun M => Finset.sum_nonneg (fun i _ => hc i), fun M hM => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
    rw [Finset.mem_filter] at hi
    exact hi.2 ▸ hφ i hci
  · rw [Finset.sum_fiberwise]; exact hc1
  · have : ∀ M, (∑ i ∈ univ.filter (fun i => φ i = M), c i) • chi M =
        ∑ i ∈ univ.filter (fun i => φ i = M), c i • chi (φ i) := by
      intro M
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.1 hi).2]
    simp_rw [this]
    rw [Finset.sum_fiberwise]

lemma InHull.exists {Q : Finset E → Prop} {x : E → ℝ} (h : InHull Q x) : ∃ M, Q M := by
  obtain ⟨w, -, h1, h2, -⟩ := h
  have : ∑ M, w M ≠ 0 := by rw [h2]; norm_num
  obtain ⟨M, -, hM⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
  exact ⟨M, h1 M hM⟩

end Hull

/-! ### Topology -/

lemma isClosed_poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    IsClosed (Poly ends W F) := by
  have e1 : IsClosed {x : E → ℝ | ∀ e, e ∉ F → x e = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply e) continuous_const
  have e2 : IsClosed {x : E → ℝ | ∀ e, 0 ≤ x e} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
  have e3 : IsClosed {x : E → ℝ | ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_eq (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
  have e4 : IsClosed {x : E → ℝ | ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun S => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_finsetSum _ fun e _ => continuous_apply e)
  have : Poly ends W F = {x : E → ℝ | ∀ e, e ∉ F → x e = 0} ∩ ({x | ∀ e, 0 ≤ x e} ∩
      ({x | ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1} ∩
        {x | ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e})) := by
    ext x; simp [Poly]
  rw [this]
  exact e1.inter (e2.inter (e3.inter e4))

end MatchingPolytope.Multi
