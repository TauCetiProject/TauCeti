/-
Copyright (c) 2026 Ralf Stephan and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import TauCeti.Algebra.Order.BigOperators.Min
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms
public import TauCeti.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Local bounds for wedge forms

Evertse's triangular basis correction gives bounds of the form
`v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j)` for increasing positive `μ`.
Passing to exterior powers preserves more than the separate row bounds: if the vector subset
meets the first `k` indices, but every form index comes from the last block, each permutation
product gains the factor `μ (k - 1) / μ k`. This is the small factor that produces a large last
minimum in the exterior-power argument for the Subspace Theorem.

The product of the minima attached to a set `T` of forms, with this gain when `T` lies in the
top block, is `TauCeti.wedgeGain k μ σ T`. `AbsoluteValue.apply_wedgeForms_plucker_le` proves the
refined bound in terms of it, uniformly in the exterior power: its constant is
`N! * max 1 C ^ N`, where `N` is the number of forms. At a nonarchimedean absolute value,
`AbsoluteValue.apply_wedgeForms_plucker_le_prod` passes row bounds to wedge forms without any
factorial loss. Together these are the local estimates needed to
put Plücker vectors into an approximation domain for the wedge forms.

## Main definitions

* `TauCeti.wedgeGain`: the minima attached to a set of forms, with the gain on the top block.

## Main results

* `TauCeti.wedgeGain_const_mul_rpow`: for nonempty `T` and minima `f` nonnegative below `n`, the
  gain of minima `b · f ^ a` is `b ^ #T` times the `a`-th power of the gain of `f`.
* `TauCeti.wedgeGain_eq_prod_update`: for `μ k ≠ 0` and a set of forms in the top block
  containing the form `σ k`, the gain cancels `μ k`, leaving the product of the minima with `μ k`
  replaced by `μ (k - 1)`.
* `TauCeti.prod_wedgeGain`: the product of the gains over all `p`-subsets, for `0 < p` and
  `k + p = card κ`.

* `AbsoluteValue.apply_wedgeForms_plucker_le`: the refined local wedge bound.
* `AbsoluteValue.apply_wedgeForms_plucker_le_prod`: the wedge bound at a nonarchimedean absolute
  value.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5.30,
  inequalities (7.44) and (7.45).
* The refined estimate and its proof follow Ralf Stephan's
  `DiophantineApproximation/WedgeDomain.lean` in `rwst/Subspace-Theorems`, commit
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0), adapted to Tau Ceti's
  `wedgeForms` and `plucker` and generalized from number fields to commutative rings.
-/

public section

open Finset Module Set Set.powersetCard TauCeti

namespace TauCeti

variable {κ : Type*} {n : ℕ}

/-- **The minima attached to a set of forms, with the gain on the top block.** Given a jump index
`k`, minima `μ` and a bijection `σ` from the indices of the minima to the forms, this is the
product of the `μ (σ.symm t)` over `t ∈ T`, multiplied by the gain `μ (k - 1) / μ k` when every
`σ.symm t` is at least `k`, that is, when `T` lies in the top block of `σ`. Use `wedgeGain_def`,
`wedgeGain_of_forall_le` and `wedgeGain_of_not_forall_le` to evaluate it. -/
noncomputable def wedgeGain (k : ℕ) (μ : ℕ → ℝ) (σ : Fin n ≃ κ) (T : Finset κ) : ℝ :=
  (if ∀ t ∈ T, k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) * ∏ t ∈ T, μ (σ.symm t)

/-- The definition of `wedgeGain`, as a rewrite rule. -/
theorem wedgeGain_def (k : ℕ) (μ : ℕ → ℝ) (σ : Fin n ≃ κ) (T : Finset κ) :
    wedgeGain k μ σ T =
      (if ∀ t ∈ T, k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) * ∏ t ∈ T, μ (σ.symm t) :=
  (rfl)

/-- On the top block, the minima attached to `T` carry the gain `μ (k - 1) / μ k`. -/
@[simp]
theorem wedgeGain_of_forall_le {k : ℕ} {μ : ℕ → ℝ} {σ : Fin n ≃ κ} {T : Finset κ}
    (hT : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)) :
    wedgeGain k μ σ T = μ (k - 1) / μ k * ∏ t ∈ T, μ (σ.symm t) := by
  rw [wedgeGain_def, ite_eq_left hT]

/-- Off the top block, the minima attached to `T` are the product of the `μ (σ.symm t)`. -/
@[simp]
theorem wedgeGain_of_not_forall_le {k : ℕ} {μ : ℕ → ℝ} {σ : Fin n ≃ κ} {T : Finset κ}
    (hT : ¬∀ t ∈ T, k ≤ (σ.symm t : ℕ)) :
    wedgeGain k μ σ T = ∏ t ∈ T, μ (σ.symm t) := by
  rw [wedgeGain_def, ite_eq_right hT, one_mul]

/-- The minima attached to a nonempty set of forms, with the gain, are nonnegative when the first
`n` minima are. -/
theorem wedgeGain_nonneg {k : ℕ} {μ : ℕ → ℝ} (hμ : ∀ l < n, 0 ≤ μ l) (σ : Fin n ≃ κ)
    {T : Finset κ} (hT : T.Nonempty) : 0 ≤ wedgeGain k μ σ T := by
  have hP : 0 ≤ ∏ t ∈ T, μ (σ.symm t) := prod_nonneg fun t _ ↦ hμ _ (σ.symm t).isLt
  by_cases h : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)
  · obtain ⟨t, ht⟩ := hT
    have hk : k < n := (h t ht).trans_lt (σ.symm t).isLt
    rw [wedgeGain_of_forall_le h]
    exact mul_nonneg (div_nonneg (hμ _ (by omega)) (hμ _ hk)) hP
  · rwa [wedgeGain_of_not_forall_le h]

/-- The minima attached to a nonempty set of forms, with the gain, are positive when the first
`n` minima are. -/
theorem wedgeGain_pos {k : ℕ} {μ : ℕ → ℝ} (hμ : ∀ l < n, 0 < μ l) (σ : Fin n ≃ κ)
    {T : Finset κ} (hT : T.Nonempty) : 0 < wedgeGain k μ σ T := by
  have hP : 0 < ∏ t ∈ T, μ (σ.symm t) := prod_pos fun t _ ↦ hμ _ (σ.symm t).isLt
  by_cases h : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)
  · obtain ⟨t, ht⟩ := hT
    have hk : k < n := (h t ht).trans_lt (σ.symm t).isLt
    rw [wedgeGain_of_forall_le h]
    exact mul_pos (div_pos (hμ _ (by omega)) (hμ _ hk)) hP
  · rwa [wedgeGain_of_not_forall_le h]

/-- For constant nonzero minima `b` the gain `b / b` is `1`, so the minima attached to `T` are
`b ^ #T`. -/
@[simp]
theorem wedgeGain_const {k : ℕ} {b : ℝ} (hb : b ≠ 0) (σ : Fin n ≃ κ) (T : Finset κ) :
    wedgeGain k (fun _ ↦ b) σ T = b ^ T.card := by
  rw [wedgeGain_def, div_self hb, ite_self, one_mul, prod_const]

/-- The minima attached to a nonempty set of forms, with the gain, depend only on the first `n`
minima: every `σ.symm t` is below `n`, and so are `k` and `k - 1` when `T` lies in the top
block. -/
theorem wedgeGain_congr {k : ℕ} {μ μ' : ℕ → ℝ} (h : ∀ l < n, μ l = μ' l) (σ : Fin n ≃ κ)
    {T : Finset κ} (hT : T.Nonempty) : wedgeGain k μ σ T = wedgeGain k μ' σ T := by
  have hP : ∏ t ∈ T, μ (σ.symm t) = ∏ t ∈ T, μ' (σ.symm t) :=
    prod_congr rfl fun t _ ↦ h _ (σ.symm t).isLt
  by_cases hk : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)
  · obtain ⟨t, ht⟩ := hT
    have hkn : k < n := (hk t ht).trans_lt (σ.symm t).isLt
    rw [wedgeGain_of_forall_le hk, wedgeGain_of_forall_le hk, hP, h k hkn, h (k - 1) (by omega)]
  · rw [wedgeGain_of_not_forall_le hk, wedgeGain_of_not_forall_le hk, hP]

/-- Replacing minima `f`, nonnegative below `n`, by `b · f ^ a`, for `b ≠ 0`, turns the minima
attached to a nonempty `T`, with the gain on the top block, into `b ^ #T` times their `a`-th
power. -/
theorem wedgeGain_const_mul_rpow {k : ℕ} {b : ℝ} (hb : b ≠ 0) {f : ℕ → ℝ}
    (hf : ∀ l < n, 0 ≤ f l) {a : ℝ} (σ : Fin n ≃ κ) {T : Finset κ} (hT : T.Nonempty) :
    wedgeGain k (fun l ↦ b * f l ^ a) σ T = b ^ T.card * wedgeGain k f σ T ^ a := by
  have hf' (t : κ) : 0 ≤ f (σ.symm t) := hf _ (σ.symm t).isLt
  have hP : 0 ≤ ∏ t ∈ T, f (σ.symm t) := prod_nonneg fun t _ ↦ hf' t
  by_cases h : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)
  · obtain ⟨t, ht⟩ := hT
    have hk : k < n := (h t ht).trans_lt (σ.symm t).isLt
    rw [wedgeGain_of_forall_le h, wedgeGain_of_forall_le h, prod_mul_distrib, prod_const,
      mul_div_mul_left _ _ hb, Real.mul_rpow (div_nonneg (hf _ (by omega)) (hf _ hk)) hP,
      Real.finsetProd_rpow _ _ fun t _ ↦ hf' t, Real.div_rpow (hf _ (by omega)) (hf _ hk)]
    ring
  · rw [wedgeGain_of_not_forall_le h, wedgeGain_of_not_forall_le h, prod_mul_distrib,
      prod_const, Real.finsetProd_rpow _ _ fun t _ ↦ hf' t]

/-- **The minima attached to the top block, without the quotient.** Let `k < n` and `μ k ≠ 0`.
For a set `T` of forms in the top block of `σ` that contains the form `σ k`, the gain
`μ (k - 1) / μ k` cancels the minimum `μ k`: the minima attached to `T` with the gain are the
product of the minima attached to `T` with `μ k` replaced by `μ (k - 1)`. -/
theorem wedgeGain_eq_prod_update {k : ℕ} {μ : ℕ → ℝ} (hμ : μ k ≠ 0) (σ : Fin n ≃ κ)
    (hk : k < n) {T : Finset κ} (hkT : σ ⟨k, hk⟩ ∈ T) (hT : ∀ t ∈ T, k ≤ (σ.symm t : ℕ)) :
    wedgeGain k μ σ T = ∏ t ∈ T, Function.update μ k (μ (k - 1)) (σ.symm t) := by
  classical
  have hcomp : (fun t ↦ Function.update μ k (μ (k - 1)) (σ.symm t)) =
      Function.update (fun t ↦ μ (σ.symm t)) (σ ⟨k, hk⟩) (μ (k - 1)) := by
    have h := Function.update_comp_eq_of_injective μ (f := fun t ↦ (σ.symm t : ℕ))
      (Fin.val_injective.comp σ.symm.injective) (σ ⟨k, hk⟩) (μ (k - 1))
    simp only [Equiv.symm_apply_apply] at h
    exact h
  rw [hcomp, prod_update_of_mem hkT, sdiff_singleton_eq_erase, wedgeGain_of_forall_le hT,
    ← mul_prod_erase _ (fun t ↦ μ (σ.symm t)) hkT, Equiv.symm_apply_apply, ← mul_assoc,
    div_mul_cancel₀ _ hμ]

/-- The product over the `p`-subsets `T` of the constant times the minima attached to `T` is
`C ^ M · (∏ l, μ l) ^ e · μ (k - 1) / μ k`, for `0 < p` and `k + p = card κ`, with
`M = (card κ).choose p` and `e = (card κ - 1).choose (p - 1)`: each index lies in `e` subsets and
exactly one subset is the top block. -/
theorem prod_wedgeGain [Fintype κ] (σ : Fin (Fintype.card κ) ≃ κ) {k p : ℕ} (hp : 0 < p)
    (hkp : k + p = Fintype.card κ) (μ : ℕ → ℝ) (C : ℝ) :
    ∏ T : Set.powersetCard κ p, C * wedgeGain k μ σ T =
      C ^ (Fintype.card κ).choose p *
        (∏ l : Fin (Fintype.card κ), μ l) ^ (Fintype.card κ - 1).choose (p - 1) *
          (μ (k - 1) / μ k) := by
  simp only [wedgeGain_def]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Set.powersetCard.fintypeCard,
    Set.powersetCard.prod_prod hp fun t ↦ μ (σ.symm t), Equiv.prod_comp σ.symm fun l ↦ μ l]
  have hite : ∏ T : Set.powersetCard κ p, (if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then
      μ (k - 1) / μ k else 1) = μ (k - 1) / μ k := by
    classical
    simp_rw [forall_le_symm_iff_eq_map_topBlock σ hkp]
    simp
  rw [hite]
  ring

end TauCeti

namespace AbsoluteValue

variable {R : Type*} [CommRing R]
  {ι κ : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder κ]

omit [Fintype ι] [LinearOrder ι] in
/-- Evertse's entrywise estimate passes to each permutation product in the wedge determinant,
retaining the gain on the top block and the nonnegativity of the common bound. -/
private theorem prod_apply_le_ite_div_mul_prod [Fintype κ] (v : AbsoluteValue R ℝ)
    (l : κ → Dual R (ι → R)) (σ : Fin (Fintype.card κ) ≃ κ)
    {μ : ℕ → ℝ} (hμm : MonotoneOn μ (Set.Iio (Fintype.card κ)))
    (hμp : ∀ j < Fintype.card κ, 0 < μ j) {ν : κ → ℝ} (hν : ∀ i, 0 ≤ ν i)
    {C : ℝ} (hC : 0 ≤ C) {y : Fin (Fintype.card κ) → ι → R}
    (hy : ∀ i j, v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j))
    {k p : ℕ} (J : powersetCard (Fin (Fintype.card κ)) p)
    (hJ : ∃ j ∈ J, (j : ℕ) < k) (T : powersetCard κ p) (τ : Equiv.Perm (Fin p)) :
    0 ≤ (∏ t ∈ (T : Finset κ), ν t) * wedgeGain k μ σ T ∧
    ∏ b, v (l (ofFinEmbEquiv.symm T (τ b)) (y (ofFinEmbEquiv.symm J b))) ≤
      C ^ p * ((∏ t ∈ (T : Finset κ), ν t) * wedgeGain k μ σ T) := by
  classical
  let eT := ofFinEmbEquiv.symm T
  let eJ := ofFinEmbEquiv.symm J
  have hperm (g : κ → ℝ) : ∏ b, g (eT (τ b)) = ∏ t ∈ (T : Finset κ), g t :=
    (Equiv.prod_comp τ fun a ↦ g (eT a)).trans (prod_comp_ofFinEmbEquiv_symm T g)
  obtain ⟨j₀, hj₀J, hj₀k⟩ := hJ
  obtain ⟨b₀, hb₀⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem J j₀).2 hj₀J
  have hm0 (b) : 0 ≤ min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) :=
    le_min (hμp _ (Fin.is_lt _)).le (hμp _ (Fin.is_lt _)).le
  have hmin : ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) ≤ wedgeGain k μ σ T := by
    by_cases hT : ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ)
    · rw [wedgeGain_of_forall_le hT, ← hperm (fun t ↦ μ (σ.symm t))]
      exact prod_min_le_div_mul_prod hμm hμp
        (fun _ ↦ Fin.is_lt _) (fun _ ↦ Fin.is_lt _)
        (fun b ↦ hT _ ((mem_range_ofFinEmbEquiv_symm_iff_mem T _).1 ⟨τ b, rfl⟩))
        ⟨b₀, by simpa [eJ, hb₀] using hj₀k⟩
    · rw [wedgeGain_of_not_forall_le hT, ← hperm (fun t ↦ μ (σ.symm t))]
      exact prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _
  have hmin0 : 0 ≤ ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) :=
    prod_nonneg fun b _ ↦ hm0 b
  refine ⟨mul_nonneg (prod_nonneg fun t _ ↦ hν t) (hmin0.trans hmin), ?_⟩
  calc
    _ ≤ ∏ b, C * ν (eT (τ b)) * min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) := by
      refine prod_le_prod₀ (fun _ _ ↦ v.nonneg _) fun b _ ↦ ?_
      simpa only [Equiv.apply_symm_apply] using hy (σ.symm (eT (τ b))) (eJ b)
    _ = C ^ p * (∏ t ∈ (T : Finset κ), ν t) *
        ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, hperm]
    _ ≤ C ^ p * (∏ t ∈ (T : Finset κ), ν t) * wedgeGain k μ σ T :=
      mul_le_mul_of_nonneg_left hmin (mul_nonneg (pow_nonneg hC _) (prod_nonneg fun t _ ↦ hν t))
    _ = _ := mul_assoc _ _ _

/-- **The refined local wedge bound** (Bombieri–Gubler (7.44)–(7.45)). Suppose Evertse's bounds
hold with nonnegative row weights `ν` and positive increasing minima `μ`. For a vector subset
`J` meeting the first `k` indices, the wedge bound gains `μ (k - 1) / μ k` whenever all the form
indices, read through `σ`, lie in the top block. The constant is uniform in the exterior degree.
No number-field hypothesis is needed. -/
theorem apply_wedgeForms_plucker_le [Fintype κ] (v : AbsoluteValue R ℝ)
    (l : κ → Dual R (ι → R)) (σ : Fin (Fintype.card κ) ≃ κ) {μ : ℕ → ℝ}
    (hμm : MonotoneOn μ (Set.Iio (Fintype.card κ))) (hμp : ∀ j < Fintype.card κ, 0 < μ j)
    {ν : κ → ℝ} (hν : ∀ i, 0 ≤ ν i) {C : ℝ} (hC : 0 ≤ C)
    {y : Fin (Fintype.card κ) → ι → R}
    (hy : ∀ i j, v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j))
    {k p : ℕ} (J : powersetCard (Fin (Fintype.card κ)) p)
    (hJ : ∃ j ∈ J, (j : ℕ) < k) (T : powersetCard κ p) :
    v (wedgeForms l p T (plucker (y ∘ ofFinEmbEquiv.symm J))) ≤
      (Fintype.card κ).factorial * max 1 C ^ Fintype.card κ *
        ((∏ t ∈ (T : Finset κ), ν t) * wedgeGain k μ σ T) := by
  classical
  rw [wedgeForms_plucker]
  have hterm := prod_apply_le_ite_div_mul_prod v l σ hμm hμp hν hC hy J hJ T
  have hdet := Matrix.abv_det_le_factorial_mul_of_forall_perm
    (Matrix.of fun a b ↦ l (ofFinEmbEquiv.symm T a) ((y ∘ ofFinEmbEquiv.symm J) b)) v
    (fun τ ↦ (hterm τ).2)
  rw [Fintype.card_fin] at hdet
  have hpN : p ≤ Fintype.card κ := by
    simpa using (Finset.card_le_univ (T : Finset κ))
  have hfac : (p.factorial : ℝ) * C ^ p ≤
      (Fintype.card κ).factorial * max 1 C ^ Fintype.card κ := by
    refine mul_le_mul (by exact_mod_cast Nat.factorial_le hpN) ?_ (pow_nonneg hC _) (by positivity)
    exact (pow_le_pow_left₀ hC (le_max_right _ _) p).trans
      (pow_le_pow_right₀ (le_max_left _ _) hpN)
  have hB := (hterm (Equiv.refl _)).1
  exact hdet.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfac hB)

/-- At a nonarchimedean absolute value, row bounds pass to the wedge forms with no factorial
loss. In particular, wedge-form evaluations are integral at a finite place whenever every
entry `l i (y j)` is integral there. -/
theorem apply_wedgeForms_plucker_le_prod (v : AbsoluteValue R ℝ) (hv : IsNonarchimedean v)
    (l : κ → Dual R (ι → R)) {p : ℕ} (y : Fin p → ι → R) {ν : κ → ℝ}
    (hy : ∀ i j, v (l i (y j)) ≤ ν i) (T : powersetCard κ p) :
    v (wedgeForms l p T (plucker y)) ≤ ∏ t ∈ (T : Finset κ), ν t := by
  rw [wedgeForms_plucker, ← prod_comp_ofFinEmbEquiv_symm T ν]
  exact Matrix.abv_det_le_prod_of_le _ hv fun i j ↦ hy _ _

end AbsoluteValue
