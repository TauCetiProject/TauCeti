/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormPow
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Radial.Rescale

/-!
# The derivative of the radial stretch

For `a > 0` the **radial stretch** `x ↦ ‖x‖ ^ (a - 1) • x` of a real inner product space `E`
sends a point at distance `r` from the origin to distance `r ^ a` along the same ray. Away from the
origin its derivative at `x` is

    D v = ‖x‖ ^ (a - 1) • (v + ((a - 1) ⟪x, v⟫ / ‖x‖²) • x),

which stretches the radial direction `x` by `a ‖x‖ ^ (a - 1)` and every direction orthogonal to
`x` by `‖x‖ ^ (a - 1)`. It is the radial rescaling `TauCeti.radialRescale` with profile
`r ↦ r ^ (a - 1)`. This file computes the quantities of linear distortion of `D`:

* the operator norm `‖D‖ = max |a| 1 · ‖x‖ ^ (a - 1)` when `dim E ≥ 2`
  (`TauCeti.norm_fderiv_norm_rpow_smul_self`), and `‖D‖ = |a| ‖x‖ ^ (a - 1)` in every dimension
  when `|a| ≥ 1`;
* the minimal stretch `ℓ(D) = min |a| 1 · ‖x‖ ^ (a - 1)` when `dim E ≥ 2`
  (`TauCeti.minimalStretch_fderiv_norm_rpow_smul_self`), and `ℓ(D) = |a| ‖x‖ ^ (a - 1)` in every
  dimension when `|a| ≤ 1`;
* the determinant `det D = a · (‖x‖ ^ (a - 1)) ^ n` with `n = dim E`
  (`TauCeti.det_fderiv_norm_rpow_smul_self`), from the Jacobian of a radial rescaling.

Hence, when `dim E ≥ 2`, the pointwise outer and inner distortions of the radial stretch are
`a ^ (n - 1)` and `a` for `a ≥ 1`, and `1 / a` and `a ^ (1 - n)` for `0 < a ≤ 1`
(`TauCeti.norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le`, and the three companion lemmas); the
outer distortion `a ^ (n - 1)` for `a ≥ 1` and the inner distortion `a ^ (1 - n)` for `0 < a ≤ 1`
hold in every dimension. These identities give the pointwise distortion of the radial stretch, a
standard example of a quasiregular map.
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

/-- The length of the image of `x` itself: `‖D x‖ = |a| ‖x‖ ^ (a - 1) ‖x‖`. -/
theorem norm_fderiv_norm_rpow_smul_self_apply_self (a : ℝ) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x x‖ = |a| * ‖x‖ ^ (a - 1) * ‖x‖ := by
  rw [fderiv_norm_rpow_smul_self_apply_self a hx, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]

/-- The length of the image of a direction `w` orthogonal to `x`: `‖D w‖ = ‖x‖ ^ (a - 1) ‖w‖`. -/
theorem norm_fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero (a : ℝ) {x w : E} (hx : x ≠ 0)
    (hw : ⟪x, w⟫ = 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x w‖ = ‖x‖ ^ (a - 1) * ‖w‖ := by
  rw [fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero a hx hw, norm_smul,
    Real.norm_of_nonneg (by positivity)]

/-- The derivative of the radial stretch at `x ≠ 0` stretches every vector by a factor between
`min |a| 1 · ‖x‖ ^ (a - 1)` and `max |a| 1 · ‖x‖ ^ (a - 1)`. -/
theorem norm_fderiv_norm_rpow_smul_self_apply_mem_Icc (a : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x v‖ ∈
      Set.Icc (min |a| 1 * ‖x‖ ^ (a - 1) * ‖v‖) (max |a| 1 * ‖x‖ ^ (a - 1) * ‖v‖) := by
  have ht : ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity), ← mul_pow, ← sq_abs ⟪x, v⟫]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm x v).trans_eq (mul_comm _ _)) 2
  have ht0 : 0 ≤ ⟪x, v⟫ ^ 2 / ‖x‖ ^ 2 := by positivity
  have ha : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  constructor
  · refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [norm_sq_fderiv_norm_rpow_smul_self_apply a hx, mul_pow, mul_pow, ha]
    rcases le_total 1 |a| with h1 | h1
    · rw [min_eq_right h1]
      nlinarith [mul_nonneg (sub_nonneg.2 (one_le_pow₀ (n := 2) h1)) ht0, sq_nonneg (‖x‖ ^ (a - 1))]
    · rw [min_eq_left h1]
      have : |a| ^ 2 - 1 ≤ 0 := by nlinarith [abs_nonneg a]
      nlinarith [mul_le_mul_of_nonpos_left ht this, sq_nonneg (‖x‖ ^ (a - 1))]
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [norm_sq_fderiv_norm_rpow_smul_self_apply a hx, mul_pow, mul_pow, ha]
    rcases le_total 1 |a| with h1 | h1
    · rw [max_eq_left h1]
      have : 0 ≤ |a| ^ 2 - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht this, sq_nonneg (‖x‖ ^ (a - 1))]
    · rw [max_eq_right h1]
      have : |a| ^ 2 - 1 ≤ 0 := by nlinarith [abs_nonneg a]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg this ht0, sq_nonneg (‖x‖ ^ (a - 1))]

/-- The radial direction gives the lower bound `|a| · ‖x‖ ^ (a - 1) ≤ ‖D‖` on the operator norm of
the derivative of the radial stretch at `x ≠ 0`. -/
theorem abs_mul_norm_rpow_le_norm_fderiv_norm_rpow_smul_self (a : ℝ) {x : E} (hx : x ≠ 0) :
    |a| * ‖x‖ ^ (a - 1) ≤ ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ := by
  have h := (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x).le_opNorm x
  rw [norm_fderiv_norm_rpow_smul_self_apply_self a hx] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hx)

/-- When `dim E ≥ 2`, a direction orthogonal to `x ≠ 0` gives the lower bound
`‖x‖ ^ (a - 1) ≤ ‖D‖` on the operator norm of the derivative of the radial stretch. -/
theorem norm_rpow_le_norm_fderiv_norm_rpow_smul_self (hE : 2 ≤ finrank ℝ E) (a : ℝ) {x : E}
    (hx : x ≠ 0) : ‖x‖ ^ (a - 1) ≤ ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ := by
  obtain ⟨w, hw0, hw⟩ :=
    exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ) {x} (by simp; omega)
  have h := (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x).le_opNorm w
  rw [norm_fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero a hx (hw x (by simp))] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hw0)

/-- The radial direction gives the upper bound `ℓ(D) ≤ |a| · ‖x‖ ^ (a - 1)` on the minimal stretch
of the derivative of the radial stretch at `x ≠ 0`. -/
theorem minimalStretch_fderiv_norm_rpow_smul_self_le_abs_mul_norm_rpow [FiniteDimensional ℝ E]
    (a : ℝ) {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ≤
      |a| * ‖x‖ ^ (a - 1) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have h := LinearMap.minimalStretch_mul_norm_le_norm_apply
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) x
  rw [ContinuousLinearMap.coe_coe, norm_fderiv_norm_rpow_smul_self_apply_self a hx] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hx)

/-- When `dim E ≥ 2`, a direction orthogonal to `x ≠ 0` gives the upper bound
`ℓ(D) ≤ ‖x‖ ^ (a - 1)` on the minimal stretch of the derivative of the radial stretch. -/
theorem minimalStretch_fderiv_norm_rpow_smul_self_le_norm_rpow [FiniteDimensional ℝ E]
    (hE : 2 ≤ finrank ℝ E) (a : ℝ) {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ≤ ‖x‖ ^ (a - 1) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨w, hw0, hw⟩ :=
    exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ) {x} (by simp; omega)
  have h := LinearMap.minimalStretch_mul_norm_le_norm_apply
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) w
  rw [ContinuousLinearMap.coe_coe,
    norm_fderiv_norm_rpow_smul_self_apply_of_inner_eq_zero a hx (hw x (by simp))] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hw0)

/-- For `|a| ≥ 1` and `x ≠ 0`, in every dimension, `‖D‖ = |a| · ‖x‖ ^ (a - 1)`: the norm is
attained in the radial direction. -/
theorem norm_fderiv_norm_rpow_smul_self_of_one_le_abs {a : ℝ} (ha : 1 ≤ |a|) {x : E}
    (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ = |a| * ‖x‖ ^ (a - 1) := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_)
    (abs_mul_norm_rpow_le_norm_fderiv_norm_rpow_smul_self a hx)
  simpa [max_eq_left ha] using (norm_fderiv_norm_rpow_smul_self_apply_mem_Icc a hx v).2

/-- **Operator norm of the derivative of the radial stretch.** For `x ≠ 0` and `dim E ≥ 2`,
`‖D‖ = max |a| 1 · ‖x‖ ^ (a - 1)`. -/
theorem norm_fderiv_norm_rpow_smul_self (hE : 2 ≤ finrank ℝ E) (a : ℝ) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ = max |a| 1 * ‖x‖ ^ (a - 1) := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦
    (norm_fderiv_norm_rpow_smul_self_apply_mem_Icc a hx v).2) ?_
  rw [max_mul_of_nonneg _ _ (by positivity), one_mul]
  exact max_le (abs_mul_norm_rpow_le_norm_fderiv_norm_rpow_smul_self a hx)
    (norm_rpow_le_norm_fderiv_norm_rpow_smul_self hE a hx)

/-- For `|a| ≤ 1` and `x ≠ 0`, in every dimension, `ℓ(D) = |a| · ‖x‖ ^ (a - 1)`: the minimal
stretch is attained in the radial direction. -/
theorem minimalStretch_fderiv_norm_rpow_smul_self_of_abs_le_one [FiniteDimensional ℝ E] {a : ℝ}
    (ha : |a| ≤ 1) {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch =
      |a| * ‖x‖ ^ (a - 1) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  refine le_antisymm (minimalStretch_fderiv_norm_rpow_smul_self_le_abs_mul_norm_rpow a hx)
    ((LinearMap.le_minimalStretch_iff _).mpr fun v ↦ ?_)
  simpa [min_eq_left ha] using (norm_fderiv_norm_rpow_smul_self_apply_mem_Icc a hx v).1

/-- **Minimal stretch of the derivative of the radial stretch.** For `x ≠ 0` and `dim E ≥ 2`,
`ℓ(D) = min |a| 1 · ‖x‖ ^ (a - 1)`. -/
theorem minimalStretch_fderiv_norm_rpow_smul_self [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E)
    (a : ℝ) {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch =
      min |a| 1 * ‖x‖ ^ (a - 1) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  refine le_antisymm ?_ ((LinearMap.le_minimalStretch_iff _).mpr fun v ↦
    (norm_fderiv_norm_rpow_smul_self_apply_mem_Icc a hx v).1)
  rw [min_mul_of_nonneg _ _ (by positivity), one_mul]
  exact le_min (minimalStretch_fderiv_norm_rpow_smul_self_le_abs_mul_norm_rpow a hx)
    (minimalStretch_fderiv_norm_rpow_smul_self_le_norm_rpow hE a hx)

/-- **Determinant of the derivative of the radial stretch.** For `x ≠ 0`,
`det D = a · (‖x‖ ^ (a - 1)) ^ n` with `n = dim E`: this is the Jacobian of the radial rescaling
with profile `r ↦ r ^ (a - 1)`. -/
theorem det_fderiv_norm_rpow_smul_self [FiniteDimensional ℝ E] (a : ℝ) {x : E} (hx : x ≠ 0) :
    LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      a * (‖x‖ ^ (a - 1)) ^ finrank ℝ E := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := det_fderiv_radialRescale hx
    (Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl hx'.ne'))
  rw [ContinuousLinearMap.det, funext (radialRescale_apply (fun r : ℝ ↦ r ^ (a - 1)))] at h
  rw [h, ← Nat.sub_add_cancel (finrank_pos (R := ℝ) (M := E)), pow_succ, Nat.add_sub_cancel]
  have : ‖x‖ * ((a - 1) * ‖x‖ ^ (a - 1 - 1)) = (a - 1) * ‖x‖ ^ (a - 1) := by
    rw [Real.rpow_sub_one hx'.ne']
    field_simp
  rw [this]
  ring

/-! ### Pointwise distortion of the radial stretch -/

variable [FiniteDimensional ℝ E]

/-- For `a ≥ 1` the pointwise outer distortion of the radial stretch is `a ^ (n - 1)`:
`‖D‖ⁿ = a ^ (n - 1) det D`. -/
theorem norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le {a : ℝ} (ha : 1 ≤ a) {x : E}
    (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E =
      a ^ (finrank ℝ E - 1) *
        LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  rw [norm_fderiv_norm_rpow_smul_self_of_one_le_abs (ha.trans (le_abs_self a)) hx,
    abs_of_pos (by linarith), det_fderiv_norm_rpow_smul_self a hx, mul_pow, ← mul_assoc,
    ← pow_succ, Nat.sub_add_cancel finrank_pos]

/-- For `0 < a ≤ 1` the pointwise outer distortion of the radial stretch is `1 / a`:
`a ‖D‖ⁿ = det D`. -/
theorem mul_norm_fderiv_norm_rpow_smul_self_pow_eq_of_le_one (hE : 2 ≤ finrank ℝ E) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) {x : E} (hx : x ≠ 0) :
    a * ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E =
      LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) := by
  rw [norm_fderiv_norm_rpow_smul_self hE a hx, det_fderiv_norm_rpow_smul_self a hx,
    abs_of_pos ha, max_eq_right ha₁, one_mul]

/-- For `a ≥ 1` the pointwise inner distortion of the radial stretch is `a`:
`det D = a ℓ(D)ⁿ`. -/
theorem det_fderiv_norm_rpow_smul_self_eq_of_one_le (hE : 2 ≤ finrank ℝ E) {a : ℝ} (ha : 1 ≤ a)
    {x : E} (hx : x ≠ 0) :
    LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      a * (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ^
        finrank ℝ E := by
  rw [minimalStretch_fderiv_norm_rpow_smul_self hE a hx, det_fderiv_norm_rpow_smul_self a hx,
    abs_of_pos (by linarith), min_eq_right ha, one_mul]

/-- For `0 < a ≤ 1` the pointwise inner distortion of the radial stretch is `a ^ (1 - n)`:
`a ^ (n - 1) det D = ℓ(D)ⁿ`. -/
theorem pow_mul_det_fderiv_norm_rpow_smul_self_eq_of_le_one {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {x : E} (hx : x ≠ 0) :
    a ^ (finrank ℝ E - 1) *
        LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) =
      (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E).minimalStretch ^
        finrank ℝ E := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  rw [minimalStretch_fderiv_norm_rpow_smul_self_of_abs_le_one ((abs_of_pos ha).trans_le ha₁) hx,
    abs_of_pos ha, det_fderiv_norm_rpow_smul_self a hx, mul_pow, ← mul_assoc, ← pow_succ,
    Nat.sub_add_cancel finrank_pos]

end TauCeti
