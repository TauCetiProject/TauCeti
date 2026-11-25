/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormPow
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The derivative of the radial stretch

For `a > 0` the **radial stretch** `x ↦ ‖x‖ ^ (a - 1) • x` of a real inner product space `E`
multiplies distances from the origin by the power `r ↦ r ^ a` and fixes every ray. Away from the
origin its derivative at `x` is

    D v = ‖x‖ ^ (a - 1) • (v + ((a - 1) ⟪x, v⟫ / ‖x‖²) • x),

which stretches the radial direction `x` by `a ‖x‖ ^ (a - 1)` and every direction orthogonal to
`x` by `‖x‖ ^ (a - 1)`. This file computes the quantities of linear distortion of `D`:

* the operator norm `‖D‖ = max a 1 · ‖x‖ ^ (a - 1)` when `dim E ≥ 2`
  (`TauCeti.norm_fderiv_norm_rpow_smul_self`);
* the minimal stretch `ℓ(D) = min a 1 · ‖x‖ ^ (a - 1)` when `dim E ≥ 2`
  (`TauCeti.minimalStretch_fderiv_norm_rpow_smul_self`);
* the determinant `det D = a · (‖x‖ ^ (a - 1)) ^ n` with `n = dim E`
  (`TauCeti.det_fderiv_norm_rpow_smul_self`), by the Weinstein–Aronszajn identity for the rank-one
  perturbation of the identity.

Hence the pointwise outer and inner distortions of the radial stretch are `a ^ (n - 1)` and `a`
for `a ≥ 1`, and `1 / a` and `a ^ (1 - n)` for `0 < a ≤ 1`
(`TauCeti.norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le`, and the three companion lemmas). These
are the pointwise parts of the radial-stretch Checks of QuasiregularMaps §2.9 and §3.2.
-/

public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin, the derivative of the radial stretch `y ↦ ‖y‖ ^ (a - 1) • y` at `x` is
`v ↦ ‖x‖ ^ (a - 1) • (v + ((a - 1) ⟪x, v⟫ / ‖x‖²) • x)`. -/
theorem fderiv_norm_rpow_smul_self_apply (a : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x v =
      ‖x‖ ^ (a - 1) • (v + ((a - 1) * ⟪x, v⟫ / ‖x‖ ^ 2) • x) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [(hasFDerivAt_norm_rpow_smul_self_of_ne (a - 1) hx).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul, smul_add, smul_smul]
  congr 2
  rw [Real.rpow_sub hx', Real.rpow_two]
  field_simp

/-- The squared length of the image of `v` under the derivative of the radial stretch at `x ≠ 0`:
`‖D v‖² = ‖x‖ ^ (2 (a - 1)) (‖v‖² + (a² - 1) ⟪x, v⟫² / ‖x‖²)`. -/
theorem norm_sq_fderiv_norm_rpow_smul_self_apply (a : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x v‖ ^ 2 =
      (‖x‖ ^ (a - 1)) ^ 2 * (‖v‖ ^ 2 + (a ^ 2 - 1) * (⟪x, v⟫ ^ 2 / ‖x‖ ^ 2)) := by
  rw [fderiv_norm_rpow_smul_self_apply a hx, norm_smul, mul_pow, Real.norm_of_nonneg
    (by positivity), ← real_inner_self_eq_norm_sq (v + _)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm x v]
  congr 1
  field_simp
  ring

/-- The image of `x` itself: the radial direction is stretched by `a ‖x‖ ^ (a - 1)`. -/
theorem fderiv_norm_rpow_smul_self_apply_self (a : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x x = (a * ‖x‖ ^ (a - 1)) • x := by
  have h : (a - 1) * ‖x‖ ^ 2 / ‖x‖ ^ 2 = a - 1 := by field_simp
  rw [fderiv_norm_rpow_smul_self_apply a hx, real_inner_self_eq_norm_sq, h]
  module

/-- A direction `w` orthogonal to `x` is stretched by `‖x‖ ^ (a - 1)`. -/
theorem fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero (a : ℝ) {x w : E} (hx : x ≠ 0)
    (hw : ⟪x, w⟫ = 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x w = ‖x‖ ^ (a - 1) • w := by
  rw [fderiv_norm_rpow_smul_self_apply a hx, hw]
  simp

/-- In dimension at least `2`, every nonzero `x` has a nonzero orthogonal vector. -/
private theorem exists_ne_zero_inner_eq_zero [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E)
    {x : E} (hx : x ≠ 0) : ∃ w : E, w ≠ 0 ∧ ⟪x, w⟫ = 0 := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ x)
  rw [finrank_span_singleton hx] at h
  have : Nontrivial (ℝ ∙ x)ᗮ := (Module.finrank_pos_iff (R := ℝ)).mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : (ℝ ∙ x)ᗮ)
  exact ⟨w, by simpa using hw,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property⟩

/-- **Operator norm of the derivative of the radial stretch.** For `a > 0`, `x ≠ 0` and
`dim E ≥ 2`, `‖D‖ = max a 1 · ‖x‖ ^ (a - 1)`. -/
theorem norm_fderiv_norm_rpow_smul_self [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E) {a : ℝ}
    (ha : 0 < a) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ = max a 1 * ‖x‖ ^ (a - 1) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set D := fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x
  set S := ‖x‖ ^ (a - 1)
  have hS : 0 < S := Real.rpow_pos_of_pos hx' _
  refine le_antisymm (D.opNorm_le_bound (by positivity) fun v ↦ ?_) ?_
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [norm_sq_fderiv_norm_rpow_smul_self_apply a hx, mul_pow, mul_pow]
    have ht : ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [div_le_iff₀ (by positivity), ← mul_pow, ← sq_abs ⟪x, v⟫]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm x v).trans_eq (mul_comm _ _))
        2
    have ht0 : 0 ≤ ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 := by positivity
    rcases le_total 1 a with h1 | h1
    · rw [max_eq_left h1]
      have : 0 ≤ a ^ 2 - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht this, sq_nonneg S]
    · rw [max_eq_right h1]
      have : a ^ 2 - 1 ≤ 0 := by nlinarith
      nlinarith [mul_nonpos_of_nonpos_of_nonneg this ht0, sq_nonneg S]
  · rcases le_total 1 a with h1 | h1
    · rw [max_eq_left h1]
      have h := D.le_opNorm x
      rw [fderiv_norm_rpow_smul_self_apply_self a hx, norm_smul,
        Real.norm_of_nonneg (by positivity)] at h
      exact le_of_mul_le_mul_right h hx'
    · rw [max_eq_right h1, one_mul]
      obtain ⟨w, hw0, hw⟩ := exists_ne_zero_inner_eq_zero hE hx
      have h := D.le_opNorm w
      rw [fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero a hx hw, norm_smul,
        Real.norm_of_nonneg hS.le] at h
      exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hw0)

/-- **Minimal stretch of the derivative of the radial stretch.** For `a > 0`, `x ≠ 0` and
`dim E ≥ 2`, `ℓ(D) = min a 1 · ‖x‖ ^ (a - 1)`. -/
theorem minimalStretch_fderiv_norm_rpow_smul_self [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E)
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch =
      min a 1 * ‖x‖ ^ (a - 1) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set D := fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x
  set S := ‖x‖ ^ (a - 1)
  have hS : 0 < S := Real.rpow_pos_of_pos hx' _
  refine le_antisymm ?_ (((D : E →ₗ[ℝ] E).le_minimalStretch_iff).mpr fun v ↦ ?_)
  · rcases le_total a 1 with h1 | h1
    · rw [min_eq_left h1]
      have h := (D : E →ₗ[ℝ] E).minimalStretch_mul_norm_le_norm_apply x
      rw [ContinuousLinearMap.coe_coe, fderiv_norm_rpow_smul_self_apply_self a hx, norm_smul,
        Real.norm_of_nonneg (by positivity)] at h
      exact le_of_mul_le_mul_right h hx'
    · rw [min_eq_right h1, one_mul]
      obtain ⟨w, hw0, hw⟩ := exists_ne_zero_inner_eq_zero hE hx
      have h := (D : E →ₗ[ℝ] E).minimalStretch_mul_norm_le_norm_apply w
      rw [ContinuousLinearMap.coe_coe, fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero a hx hw,
        norm_smul, Real.norm_of_nonneg hS.le] at h
      exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hw0)
  · rw [ContinuousLinearMap.coe_coe]
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [norm_sq_fderiv_norm_rpow_smul_self_apply a hx, mul_pow, mul_pow]
    have ht : ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [div_le_iff₀ (by positivity), ← mul_pow, ← sq_abs ⟪x, v⟫]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm x v).trans_eq (mul_comm _ _))
        2
    have ht0 : 0 ≤ ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 := by positivity
    rcases le_total a 1 with h1 | h1
    · rw [min_eq_left h1]
      have : a ^ 2 - 1 ≤ 0 := by nlinarith
      nlinarith [mul_le_mul_of_nonpos_left ht this, sq_nonneg S]
    · rw [min_eq_right h1]
      have : 0 ≤ a ^ 2 - 1 := by nlinarith
      nlinarith [mul_nonneg this ht0, sq_nonneg S]

/-- **Determinant of the derivative of the radial stretch.** For `x ≠ 0`,
`det D = a · (‖x‖ ^ (a - 1)) ^ n` with `n = dim E`: `D` is `‖x‖ ^ (a - 1)` times a rank-one
perturbation of the identity, whose determinant is `1 + (a - 1) = a`. -/
theorem det_fderiv_norm_rpow_smul_self [FiniteDimensional ℝ E] (a : ℝ) {x : E} (hx : x ≠ 0) :
    LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      a * (‖x‖ ^ (a - 1)) ^ finrank ℝ E := by
  -- `D = S • (1 + X ∘ Y)` with `Y = ((a - 1) / ‖x‖²) ⟪x, ·⟫` and `X t = t • x`.
  set Y : E →ₗ[ℝ] ℝ := ((a - 1) / ‖x‖ ^ 2) • (innerSL ℝ x : E →L[ℝ] ℝ).toLinearMap
  set X : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E x
  have hD : (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      ‖x‖ ^ (a - 1) • (1 + X ∘ₗ Y) := by
    ext v
    simp only [ContinuousLinearMap.coe_coe, fderiv_norm_rpow_smul_self_apply a hx,
      LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, X, Y, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply, smul_eq_mul]
    congr 3
    ring
  have hYX : (1 : ℝ →ₗ[ℝ] ℝ) + Y ∘ₗ X = a • LinearMap.id := by
    refine LinearMap.ext_ring ?_
    simp only [LinearMap.add_apply, one_apply_eq_self, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul, X, Y, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul,
      LinearMap.id_apply]
    field_simp
    ring
  rw [hD, LinearMap.det_smul, LinearMap.det_one_add_comp_comm, hYX, LinearMap.det_smul,
    LinearMap.det_id, Module.finrank_self, pow_one, mul_one, mul_comm]

/-! ### Pointwise distortion of the radial stretch -/

variable [FiniteDimensional ℝ E]

/-- For `a ≥ 1` the pointwise outer distortion of the radial stretch is `a ^ (n - 1)`:
`‖D‖ⁿ = a ^ (n - 1) det D`. -/
theorem norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le (hE : 2 ≤ finrank ℝ E) {a : ℝ}
    (ha : 1 ≤ a) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E =
      a ^ (finrank ℝ E - 1) *
        LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) := by
  rw [norm_fderiv_norm_rpow_smul_self hE (by linarith) hx, det_fderiv_norm_rpow_smul_self a hx,
    max_eq_left ha, mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]

/-- For `0 < a ≤ 1` the pointwise outer distortion of the radial stretch is `1 / a`:
`a ‖D‖ⁿ = det D`. -/
theorem mul_norm_fderiv_norm_rpow_smul_self_pow_eq_of_le_one (hE : 2 ≤ finrank ℝ E) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) {x : E} (hx : x ≠ 0) :
    a * ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E =
      LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) := by
  rw [norm_fderiv_norm_rpow_smul_self hE ha hx, det_fderiv_norm_rpow_smul_self a hx,
    max_eq_right ha₁, one_mul]

/-- For `a ≥ 1` the pointwise inner distortion of the radial stretch is `a`:
`det D = a ℓ(D)ⁿ`. -/
theorem det_fderiv_norm_rpow_smul_self_eq_of_one_le (hE : 2 ≤ finrank ℝ E) {a : ℝ} (ha : 1 ≤ a)
    {x : E} (hx : x ≠ 0) :
    LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      a * (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ^
        finrank ℝ E := by
  rw [minimalStretch_fderiv_norm_rpow_smul_self hE (by linarith) hx,
    det_fderiv_norm_rpow_smul_self a hx, min_eq_right ha, one_mul]

/-- For `0 < a ≤ 1` the pointwise inner distortion of the radial stretch is `a ^ (1 - n)`:
`a ^ (n - 1) det D = ℓ(D)ⁿ`. -/
theorem pow_mul_det_fderiv_norm_rpow_smul_self_eq_of_le_one (hE : 2 ≤ finrank ℝ E) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) {x : E} (hx : x ≠ 0) :
    a ^ (finrank ℝ E - 1) *
        LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ^
        finrank ℝ E := by
  rw [minimalStretch_fderiv_norm_rpow_smul_self hE ha hx, det_fderiv_norm_rpow_smul_self a hx,
    min_eq_left ha₁, mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]

end TauCeti
