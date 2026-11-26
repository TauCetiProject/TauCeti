/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Complex.Orientation
import TauCeti.Analysis.InnerProductSpace.LinearDistortion.Comparison
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Planar linear maps: norm, minimal stretch, Jacobian and distortion

Every real-linear map of the plane `ℂ` has the form `A z = z a + conj z b` for unique `a b : ℂ`: it
is `TauCeti.wirtingerPartsCLM a b`, with `a` and `b` its two Wirtinger parts
(`TauCeti.exists_eq_wirtingerPartsCLM`, `TauCeti.wirtingerPartsCLM_inj`). This file computes the
three quantities of linear distortion of `A`, and its outer and inner distortion, in terms of `a`
and `b`:

* the operator norm `‖A‖ = |a| + |b|` (`TauCeti.norm_wirtingerPartsCLM`);
* the minimal stretch `ℓ(A) = ||a| - |b||` (`TauCeti.minimalStretch_wirtingerPartsCLM`);
* the Jacobian `J(A) = det A = |a|² - |b|²` (`TauCeti.det_wirtingerPartsCLM`), read off from the
  real matrix of `A` in the basis `(1, i)` (`TauCeti.toMatrix_wirtingerPartsCLM`); for any
  orientation `o` of `ℂ` used on both sides, the oriented Jacobian of `A` is this determinant
  (`Orientation.orientedJacobian_wirtingerPartsCLM`), positive exactly when `|b| < |a|`
  (`Orientation.orientedJacobian_wirtingerPartsCLM_pos_iff`,
  `Orientation.orientedJacobian_wirtingerPartsCLM_nonpos_iff`).

The extremal directions are explicit. Writing `a = |a| e^{iα}` and `b = |b| e^{iβ}`, the image of
the unit vector `e^{i((β - α)/2 + t)}` is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`
(`TauCeti.wirtingerPartsCLM_apply_exp`, `TauCeti.norm_wirtingerPartsCLM_apply_exp`); `t = 0`
stretches by `|a| + |b|` (`TauCeti.norm_wirtingerPartsCLM_apply_exp_zero`) and `t = π/2` by
`||a| - |b||` (`TauCeti.norm_wirtingerPartsCLM_apply_exp_pi_div_two`).

The sign of the Jacobian distinguishes maps close to complex multiplications from maps close to
conjugate ones: `‖A - (z ↦ z c)‖ < ‖c‖` forces `J(A) > 0`
(`TauCeti.det_pos_of_norm_sub_smulRight_lt`) and `‖A - (z ↦ conj z c)‖ < ‖c‖` forces `J(A) < 0`
(`TauCeti.det_neg_of_norm_sub_smulRight_conjCLE_lt`); conversely each sign of `J(A)` is realized
by such a `c`, the Wirtinger part `a` or `b` (`TauCeti.exists_norm_sub_smulRight_lt_of_det_pos`,
`TauCeti.exists_norm_sub_smulRight_conjCLE_lt_of_det_neg`). This is how the sign of a transverse
zero of a section of a complex line bundle is read from the real derivative of its chart reading.

For any orientation `o` of `ℂ` used on both sides, the formulas above give the outer distortion
`q_O(A) = ‖A‖² / J(A)` and the inner distortion `q_I(A) = J(A) / ℓ(A)²`:

* if `|b| < |a|` then `q_O(A) = q_I(A) = (|a| + |b|) / (|a| - |b|)`
  (`Orientation.outerDistortion_wirtingerPartsCLM_of_lt`,
  `Orientation.innerDistortion_wirtingerPartsCLM_of_lt`);
* if `|a| ≤ |b|` and `b ≠ 0` then `q_O(A) = ∞` and `q_I(A) = 0`
  (`Orientation.outerDistortion_wirtingerPartsCLM_of_le`,
  `Orientation.innerDistortion_wirtingerPartsCLM_of_le`);
* for `k < 1`, `q_O(A) ≤ (1 + k) / (1 - k)` exactly when `|b| ≤ k |a|`
  (`Orientation.outerDistortion_wirtingerPartsCLM_le_iff`): the Beltrami coefficient `b / a` of a
  `K`-quasiconformal planar map has modulus at most `k = (K - 1) / (K + 1)`.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter I.
-/

public section

noncomputable section

open Complex Module
open scoped ComplexConjugate

namespace TauCeti

/-- The image of the unit vector `e^{i((β - α)/2 + t)}` under `z ↦ z a + conj z b`, where
`α = arg a` and `β = arg b`: it is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`. -/
theorem wirtingerPartsCLM_apply_exp (a b : ℂ) (t : ℝ) :
    wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + t) * I)) =
      (‖a‖ * exp (t * I) + ‖b‖ * exp (-t * I)) * exp (↑((arg a + arg b) / 2) * I) := by
  have hconj : conj (exp (↑((arg b - arg a) / 2 + t) * I)) =
      exp (-↑((arg b - arg a) / 2 + t) * I) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, neg_mul]
  have key : ∀ r s α β : ℝ,
      r * exp (α * I) * exp (↑((β - α) / 2 + t) * I) +
          s * exp (β * I) * exp (-↑((β - α) / 2 + t) * I) =
        (r * exp (t * I) + s * exp (-t * I)) * exp (↑((α + β) / 2) * I) := by
    intro r s α β
    simp only [add_mul, mul_assoc, ← exp_add]
    congr 3 <;> push_cast <;> ring
  have h := key ‖a‖ ‖b‖ (arg a) (arg b)
  rw [norm_mul_exp_arg_mul_I, norm_mul_exp_arg_mul_I] at h
  rw [wirtingerPartsCLM_apply, smul_eq_mul, smul_eq_mul, mul_comm _ a, mul_comm _ b, hconj, h]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i((β - α)/2 + t)}`, where
`α = arg a` and `β = arg b`, is `||a| e^{it} + |b| e^{-it}|`. -/
theorem norm_wirtingerPartsCLM_apply_exp (a b : ℂ) (t : ℝ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + t) * I))‖ =
      ‖‖a‖ * exp (t * I) + ‖b‖ * exp (-t * I)‖ := by
  rw [wirtingerPartsCLM_apply_exp, norm_mul, norm_exp_ofReal_mul_I, mul_one]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i(β - α)/2}`, where `α = arg a`
and `β = arg b`, is `|a| + |b|`. -/
theorem norm_wirtingerPartsCLM_apply_exp_zero (a b : ℂ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2) * I))‖ = ‖a‖ + ‖b‖ := by
  have h := norm_wirtingerPartsCLM_apply_exp a b 0
  rw [add_zero] at h
  rw [h]
  simp [← ofReal_add, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i((β - α)/2 + π/2)}`, where
`α = arg a` and `β = arg b`, is `||a| - |b||`. -/
theorem norm_wirtingerPartsCLM_apply_exp_pi_div_two (a b : ℂ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))‖ = |‖a‖ - ‖b‖| := by
  have e1 : exp (↑(Real.pi / 2) * I) = I := by push_cast; exact exp_pi_div_two_mul_I
  have e2 : exp (-↑(Real.pi / 2) * I) = -I := by
    push_cast; rw [← neg_div]; exact exp_neg_pi_div_two_mul_I
  have h : (‖a‖ : ℂ) * I + ‖b‖ * -I = ↑(‖a‖ - ‖b‖) * I := by push_cast; ring
  rw [norm_wirtingerPartsCLM_apply_exp, e1, e2, h]
  simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]

/-- The operator norm of `z ↦ z a + conj z b` is `|a| + |b|`. -/
@[simp]
theorem norm_wirtingerPartsCLM (a b : ℂ) : ‖wirtingerPartsCLM a b‖ = ‖a‖ + ‖b‖ := by
  refine le_antisymm (norm_wirtingerPartsCLM_le a b) ?_
  have h := (wirtingerPartsCLM a b).le_opNorm (exp (↑((arg b - arg a) / 2) * I))
  rwa [norm_wirtingerPartsCLM_apply_exp_zero, norm_exp_ofReal_mul_I, mul_one] at h

/-- The minimal stretch of `z ↦ z a + conj z b` is `||a| - |b||`. -/
@[simp]
theorem minimalStretch_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch = |‖a‖ - ‖b‖| := by
  refine le_antisymm ?_ ((LinearMap.le_minimalStretch_iff _).mpr fun z ↦ ?_)
  · have h := (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch_mul_norm_le_norm_apply
      (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))
    rwa [ContinuousLinearMap.coe_coe, norm_wirtingerPartsCLM_apply_exp_pi_div_two,
      norm_exp_ofReal_mul_I, mul_one] at h
  · calc |‖a‖ - ‖b‖| * ‖z‖ = |‖z * a‖ - ‖conj z * b‖| := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, mul_comm ‖z‖, mul_comm ‖z‖, ← sub_mul,
            abs_mul, abs_norm]
      _ ≤ ‖(wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) z‖ := by
          simpa [sub_neg_eq_add] using abs_norm_sub_norm_le (z * a) (-(conj z * b))

/-- The real matrix of `z ↦ z a + conj z b` in the basis `(1, i)` of `ℂ`. -/
theorem toMatrix_wirtingerPartsCLM (a b : ℂ) :
    LinearMap.toMatrix basisOneI basisOneI (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) =
      !![a.re + b.re, b.im - a.im; a.im + b.im, a.re - b.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply] <;> ring

/-- The determinant of `z ↦ z a + conj z b` is `|a|² - |b|²`. -/
@[simp]
theorem det_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).det = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_wirtingerPartsCLM, Matrix.det_fin_two_of,
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
  ring

/-! ### The sign of the Jacobian near complex linear and antilinear maps -/

/-- **A real-linear map close to a complex multiplication preserves orientation.** If
`‖D - (z ↦ z c)‖ < ‖c‖`, then `det D > 0`: writing `D z = z a + conj z b`, the hypothesis is
`|a - c| + |b| < |c|`, so `|b| < |a|` and `det D = |a|² - |b|²` is positive. -/
theorem det_pos_of_norm_sub_smulRight_lt {D : ℂ →L[ℝ] ℂ} {c : ℂ}
    (h : ‖D - (ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖) : 0 < D.det := by
  obtain ⟨a, b, rfl⟩ := exists_eq_wirtingerPartsCLM D
  rw [smulRight_id_eq_wirtingerPartsCLM, ← wirtingerPartsCLM_sub, sub_zero,
    norm_wirtingerPartsCLM] at h
  rw [ContinuousLinearMap.det, det_wirtingerPartsCLM, sub_pos]
  have hc : ‖c‖ ≤ ‖a‖ + ‖a - c‖ := (norm_le_insert' c a).trans_eq (by rw [norm_sub_rev])
  exact pow_lt_pow_left₀ (by linarith) (norm_nonneg b) two_ne_zero

/-- **A real-linear map close to a conjugate complex multiplication reverses orientation.** If
`‖D - (z ↦ conj z c)‖ < ‖c‖`, then `det D < 0`: writing `D z = z a + conj z b`, the hypothesis is
`|a| + |b - c| < |c|`, so `|a| < |b|` and `det D = |a|² - |b|²` is negative. -/
theorem det_neg_of_norm_sub_smulRight_conjCLE_lt {D : ℂ →L[ℝ] ℂ} {c : ℂ}
    (h : ‖D - conjCLE.toContinuousLinearMap.smulRight c‖ < ‖c‖) : D.det < 0 := by
  obtain ⟨a, b, rfl⟩ := exists_eq_wirtingerPartsCLM D
  rw [smulRight_conjCLE_eq_wirtingerPartsCLM, ← wirtingerPartsCLM_sub, sub_zero,
    norm_wirtingerPartsCLM] at h
  rw [ContinuousLinearMap.det, det_wirtingerPartsCLM, sub_neg]
  have hc : ‖c‖ ≤ ‖b‖ + ‖b - c‖ := (norm_le_insert' c b).trans_eq (by rw [norm_sub_rev])
  exact pow_lt_pow_left₀ (by linarith) (norm_nonneg a) two_ne_zero

/-- **An orientation-preserving real-linear map is close to a complex multiplication.** If
`det D > 0`, then `‖D - (z ↦ z a)‖ < ‖a‖` for the complex linear Wirtinger part `a` of `D`: the
difference is `z ↦ conj z b`, of norm `|b| < |a|`. -/
theorem exists_norm_sub_smulRight_lt_of_det_pos {D : ℂ →L[ℝ] ℂ} (h : 0 < D.det) :
    ∃ c : ℂ, ‖D - (ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖ := by
  obtain ⟨a, b, rfl⟩ := exists_eq_wirtingerPartsCLM D
  rw [ContinuousLinearMap.det, det_wirtingerPartsCLM, sub_pos] at h
  refine ⟨a, ?_⟩
  rw [smulRight_id_eq_wirtingerPartsCLM, ← wirtingerPartsCLM_sub, sub_self, sub_zero,
    norm_wirtingerPartsCLM, norm_zero, zero_add]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg a) h

/-- **An orientation-reversing real-linear map is close to a conjugate complex multiplication.** If
`det D < 0`, then `‖D - (z ↦ conj z b)‖ < ‖b‖` for the complex antilinear Wirtinger part `b` of
`D`: the difference is `z ↦ z a`, of norm `|a| < |b|`. -/
theorem exists_norm_sub_smulRight_conjCLE_lt_of_det_neg {D : ℂ →L[ℝ] ℂ} (h : D.det < 0) :
    ∃ c : ℂ, ‖D - conjCLE.toContinuousLinearMap.smulRight c‖ < ‖c‖ := by
  obtain ⟨a, b, rfl⟩ := exists_eq_wirtingerPartsCLM D
  rw [ContinuousLinearMap.det, det_wirtingerPartsCLM, sub_neg] at h
  refine ⟨b, ?_⟩
  rw [smulRight_conjCLE_eq_wirtingerPartsCLM, ← wirtingerPartsCLM_sub, sub_self, sub_zero,
    norm_wirtingerPartsCLM, norm_zero, add_zero]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg b) h

end TauCeti

namespace Orientation

open TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-- For any orientation of `ℂ` used on both sides, the oriented Jacobian of
`z ↦ z a + conj z b` is `|a|² - |b|²`. -/
@[simp]
theorem orientedJacobian_wirtingerPartsCLM (o : Orientation ℝ ℂ (Fin 2)) (a b : ℂ) :
    o.orientedJacobian o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [orientedJacobian_self, det_wirtingerPartsCLM]

/-- For any orientation of `ℂ` used on both sides, `z ↦ z a + conj z b` preserves orientation
strictly, that is its oriented Jacobian is positive, exactly when `|b| < |a|`. -/
theorem orientedJacobian_wirtingerPartsCLM_pos_iff (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ} :
    0 < o.orientedJacobian o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) ↔ ‖b‖ < ‖a‖ := by
  rw [orientedJacobian_wirtingerPartsCLM, sub_pos, sq_lt_sq₀ (norm_nonneg b) (norm_nonneg a)]

/-- For any orientation of `ℂ` used on both sides, the oriented Jacobian of
`z ↦ z a + conj z b` is nonpositive exactly when `|a| ≤ |b|`. -/
theorem orientedJacobian_wirtingerPartsCLM_nonpos_iff (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ} :
    o.orientedJacobian o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) ≤ 0 ↔ ‖a‖ ≤ ‖b‖ := by
  rw [← not_lt, orientedJacobian_wirtingerPartsCLM_pos_iff, not_lt]

/-- If `|b| < |a|`, the inner distortion of `z ↦ z a + conj z b` is
`(|a| + |b|) / (|a| - |b|)`. -/
theorem innerDistortion_wirtingerPartsCLM_of_lt (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ}
    (h : ‖b‖ < ‖a‖) :
    o.innerDistortion o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) := by
  have hs : 0 < ‖a‖ - ‖b‖ := sub_pos.mpr h
  rw [innerDistortion_of_pos _ _ ((orientedJacobian_wirtingerPartsCLM_pos_iff o).mpr h),
    orientedJacobian_wirtingerPartsCLM, minimalStretch_wirtingerPartsCLM, abs_of_pos hs,
    div_eq_div_iff (pow_pos hs 2).ne' hs.ne']
  ring

/-- If `|b| < |a|`, the outer distortion of `z ↦ z a + conj z b` is
`(|a| + |b|) / (|a| - |b|)`, the same as its inner distortion, since `q_O = q_I` in dimension `2`
(`Orientation.outerDistortion_eq_ofReal_innerDistortion_of_fin_two`). -/
theorem outerDistortion_wirtingerPartsCLM_of_lt (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ}
    (h : ‖b‖ < ‖a‖) :
    o.outerDistortion o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) =
      ENNReal.ofReal ((‖a‖ + ‖b‖) / (‖a‖ - ‖b‖)) := by
  rw [o.outerDistortion_eq_ofReal_innerDistortion_of_fin_two o
      ((orientedJacobian_wirtingerPartsCLM_pos_iff o).mpr h),
    innerDistortion_wirtingerPartsCLM_of_lt o h]

/-- If `|a| ≤ |b|` and `b ≠ 0`, the map `z ↦ z a + conj z b` is nonzero and does not preserve
orientation strictly, so its outer distortion is `∞`. -/
theorem outerDistortion_wirtingerPartsCLM_of_le (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ}
    (h : ‖a‖ ≤ ‖b‖) (hb : b ≠ 0) :
    o.outerDistortion o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
  refine outerDistortion_of_nonpos _ _
    ((orientedJacobian_wirtingerPartsCLM_nonpos_iff o).mpr h) fun h0 ↦ ?_
  have := norm_wirtingerPartsCLM a b
  rw [← LinearMap.toContinuousLinearMap_coe (wirtingerPartsCLM a b), h0, map_zero,
    norm_zero] at this
  linarith [norm_nonneg a, norm_pos_iff.mpr hb]

/-- If `|a| ≤ |b|`, the inner distortion of `z ↦ z a + conj z b` is `0`. -/
theorem innerDistortion_wirtingerPartsCLM_of_le (o : Orientation ℝ ℂ (Fin 2)) {a b : ℂ}
    (h : ‖a‖ ≤ ‖b‖) :
    o.innerDistortion o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = 0 :=
  innerDistortion_of_nonpos _ _
    ((orientedJacobian_wirtingerPartsCLM_nonpos_iff o).mpr h)

/-- For `k < 1`, the outer distortion of `z ↦ z a + conj z b` is at most `(1 + k) / (1 - k)`
exactly when `|b| ≤ k |a|`. -/
theorem outerDistortion_wirtingerPartsCLM_le_iff (o : Orientation ℝ ℂ (Fin 2)) {k : ℝ}
    (hk : k < 1) (a b : ℂ) :
    o.outerDistortion o (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) ≤
        ENNReal.ofReal ((1 + k) / (1 - k)) ↔
      ‖b‖ ≤ k * ‖a‖ := by
  have h1k : 0 < 1 - k := sub_pos.mpr hk
  -- `ENNReal.ofReal` sends a negative bound to `0`, so clamp it below at `0`.
  rw [show ENNReal.ofReal ((1 + k) / (1 - k)) = ENNReal.ofReal (max ((1 + k) / (1 - k)) 0) by
      simp, outerDistortion_le_ofReal_iff _ _ two_pos (le_max_right _ _),
    orientedJacobian_wirtingerPartsCLM, LinearMap.toContinuousLinearMap_coe,
    norm_wirtingerPartsCLM]
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  rcases (add_nonneg ha hb).eq_or_lt with h0 | h0
  · have ha0 : ‖a‖ = 0 := by linarith
    have hb0 : ‖b‖ = 0 := by linarith
    simp [ha0, hb0]
  rcases le_or_gt 0 k with hk₀ | hk₀
  · -- `(1 + k) (s² - t²) - (1 - k) (s + t)² = 2 (s + t) (k s - t)`.
    rw [max_eq_left (by positivity), div_mul_eq_mul_div, le_div_iff₀ h1k]
    constructor <;> intro h
    · by_contra! h'
      nlinarith [mul_pos h0 (sub_pos.mpr h')]
    · nlinarith [mul_nonneg h0.le (sub_nonneg.mpr h)]
  · -- The clamped bound `K` lies in `[0, 1)`, so both sides force `a = b = 0`.
    have hK : max ((1 + k) / (1 - k)) 0 < 1 :=
      max_lt ((div_lt_one h1k).mpr (by linarith)) one_pos
    have hK₀ : 0 ≤ max ((1 + k) / (1 - k)) 0 := le_max_right _ _
    constructor <;> intro h
    · nlinarith [mul_nonneg hK₀ (mul_nonneg hb h0.le), mul_pos (sub_pos.mpr hK) (pow_pos h0 2)]
    · have : k * ‖a‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk₀.le ha
      nlinarith [mul_neg_of_neg_of_pos hk₀ (show 0 < ‖a‖ by linarith)]

end Orientation

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### Checks -/

/-- Check: `z ↦ z + conj z / 2` has `‖A‖ = 3/2`, `ℓ(A) = 1/2`, `J(A) = 3/4` and
`q_O(A) = (9/4) / (3/4) = 3`. -/
example :
    ‖wirtingerPartsCLM (1 : ℂ) (1 / 2)‖ = 3 / 2 ∧
      (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ).minimalStretch = 1 / 2 ∧
      (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ).det = 3 / 4 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ) = 3 := by
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_wirtingerPartsCLM, h, norm_one]
    norm_num
  · rw [minimalStretch_wirtingerPartsCLM, h, norm_one]
    norm_num [abs_of_pos]
  · rw [det_wirtingerPartsCLM, h, norm_one]
    norm_num
  · rw [Complex.orientation.outerDistortion_wirtingerPartsCLM_of_lt (by rw [h, norm_one]; norm_num),
      h, norm_one]
    norm_num

/-- Check: complex conjugation `z ↦ conj z` reverses orientation, `J(A) = -1`, so
`q_O(A) = ∞`. -/
example :
    (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ).det = -1 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
  refine ⟨?_, Complex.orientation.outerDistortion_wirtingerPartsCLM_of_le (by simp) one_ne_zero⟩
  rw [det_wirtingerPartsCLM]
  norm_num

/-- Check: `z ↦ 2 i z` stretches every direction by `2`, `‖A‖ = ℓ(A) = 2`, so `q_O(A) = 1`. -/
example :
    ‖wirtingerPartsCLM (2 * I) (0 : ℂ)‖ = 2 ∧
      (wirtingerPartsCLM (2 * I) (0 : ℂ) : ℂ →ₗ[ℝ] ℂ).minimalStretch = 2 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (2 * I) (0 : ℂ) : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have h : ‖(2 * I : ℂ)‖ = 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_wirtingerPartsCLM, h, norm_zero, add_zero]
  · rw [minimalStretch_wirtingerPartsCLM, h, norm_zero, sub_zero, abs_two]
  · rw [Complex.orientation.outerDistortion_wirtingerPartsCLM_of_lt
      (by rw [h, norm_zero]; norm_num), h, norm_zero]
    norm_num

/-- Check: `K = 2` corresponds to `k = 1/3`, and `z ↦ z + conj z / 3` has
`q_O = (4/3) / (2/3) = 2`. -/
example :
    (1 + 1 / 3 : ℝ) / (1 - 1 / 3) = 2 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (1 : ℂ) (1 / 3) : ℂ →ₗ[ℝ] ℂ) = 2 := by
  have h : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  refine ⟨by norm_num, ?_⟩
  rw [Complex.orientation.outerDistortion_wirtingerPartsCLM_of_lt (by rw [h, norm_one]; norm_num),
    h, norm_one]
  norm_num

end TauCeti
