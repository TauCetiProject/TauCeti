/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Regularization

/-!
# Regularized norm powers and their first two derivatives

Let `E` be a real inner product space. For `t > 0` the regularized norm power
`(‖x‖ ^ 2 + t) ^ (s / 2)` is smooth on all of `E`, and as `t → 0` it tends to `‖x‖ ^ s`. This file
records its gradient

`s (‖x‖ ^ 2 + t) ^ (s / 2 - 1) x`

(`TauCeti.regularizedNormRpowGradient`) and the derivative of that gradient, the regularized
Hessian

`v ↦ s (‖x‖ ^ 2 + t) ^ (s / 2 - 1) v + s (s - 2) (‖x‖ ^ 2 + t) ^ (s / 2 - 2) ⟪x, v⟫ x`

(`TauCeti.regularizedNormRpowHessian`). At `t = 0` and away from the origin they are the gradient
and the Hessian of `‖x‖ ^ s`. For `s ≤ 2` and `t ≥ 0` both are dominated by their values at `t = 0`:
the gradient by `|s| ‖x‖ ^ (s - 1)` and the Hessian by `|s| (3 - s) ‖x‖ ^ (s - 2)`. These bounds
are uniform in `t`, which is what dominated convergence arguments for singular norm powers need.

## Main declarations

* `TauCeti.hasGradientAt_norm_sq_add_rpow`: the gradient of the regularized power.
* `TauCeti.regularizedNormRpowGradient`: that gradient, with its continuity, measurability and
  domination lemmas; `TauCeti.gradient_norm_rpow_eq_regularizedNormRpowGradient`: at `t = 0` it
  is the gradient of `‖x‖ ^ s` away from the origin.
* `TauCeti.regularizedNormRpowHessian`, `TauCeti.hasFDerivAt_regularizedNormRpowGradient`: the
  derivative of the regularized gradient;
  `TauCeti.iteratedGradientChain_one_norm_rpow_eq_regularizedNormRpowHessian`: at `t = 0` it is the
  Hessian of `‖x‖ ^ s` away from the origin; `TauCeti.norm_regularizedNormRpowHessian_le`: its
  domination for `s ≤ 2`.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology

open scoped RealInnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℝ}

/-! ### The regularized gradient -/

/-- The field `s (‖x‖ ^ 2 + t) ^ (s / 2 - 1) x`: for `t > 0` the gradient of the regularized norm
power `(‖x‖ ^ 2 + t) ^ (s / 2)` (`TauCeti.hasGradientAt_norm_sq_add_rpow`), and for `t = 0` the
gradient of `‖x‖ ^ s` away from the origin
(`TauCeti.gradient_norm_rpow_eq_regularizedNormRpowGradient`). -/
def regularizedNormRpowGradient (s t : ℝ) (x : E) : E :=
  (s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1)) • x

/-- Unfolding `TauCeti.regularizedNormRpowGradient`. -/
theorem regularizedNormRpowGradient_apply (s t : ℝ) (x : E) :
    regularizedNormRpowGradient s t x = (s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1)) • x :=
  (rfl)

/-- The regularized gradient vanishes at the origin. -/
@[simp]
theorem regularizedNormRpowGradient_zero (s t : ℝ) :
    regularizedNormRpowGradient s t (0 : E) = 0 := by
  rw [regularizedNormRpowGradient_apply, smul_zero]

/-- The regularized gradient of the power `0` vanishes. -/
@[simp]
theorem regularizedNormRpowGradient_zero_left (t : ℝ) (x : E) :
    regularizedNormRpowGradient 0 t x = 0 := by
  rw [regularizedNormRpowGradient_apply, zero_mul, zero_smul]

/-- Without regularization, the field is `s ‖x‖ ^ (s - 2) x`, the gradient of `‖x‖ ^ s` away from
the origin (`TauCeti.gradient_norm_rpow_eq_regularizedNormRpowGradient`). -/
@[simp]
theorem regularizedNormRpowGradient_zero_right (s : ℝ) (x : E) :
    regularizedNormRpowGradient s 0 x = (s * ‖x‖ ^ (s - 2)) • x := by
  rw [regularizedNormRpowGradient_apply, add_zero, show s / 2 - 1 = (s - 2) / 2 by ring,
    Real.sq_rpow_div_two (norm_nonneg x)]

/-- Where `‖x‖ ^ 2 + t ≠ 0`, in particular everywhere for `t > 0`, the gradient of the regularized
norm power `(‖y‖ ^ 2 + t) ^ (s / 2)` is `TauCeti.regularizedNormRpowGradient s t x`. -/
theorem hasGradientAt_norm_sq_add_rpow [CompleteSpace E] (s t : ℝ) {x : E}
    (hx : ‖x‖ ^ 2 + t ≠ 0) :
    HasGradientAt (fun y : E => (‖y‖ ^ 2 + t) ^ (s / 2)) (regularizedNormRpowGradient s t x) x := by
  refine hasGradientAt_iff_hasFDerivAt.2 ?_
  convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const (p := s / 2)
    (Or.inl hx) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, regularizedNormRpowGradient_apply,
    real_inner_smul_left, smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

/-- For `t > 0` the regularized gradient `TauCeti.regularizedNormRpowGradient s t` is
continuous. -/
theorem continuous_regularizedNormRpowGradient (s : ℝ) {t : ℝ} (ht : 0 < t) :
    Continuous (regularizedNormRpowGradient (E := E) s t) :=
  (continuous_const.mul (continuous_norm_sq_add_rpow ht _)).smul continuous_id

/-- The field `TauCeti.regularizedNormRpowGradient s t` is measurable. -/
@[fun_prop]
theorem measurable_regularizedNormRpowGradient [MeasurableSpace E] [BorelSpace E] (s t : ℝ) :
    Measurable (regularizedNormRpowGradient (E := E) s t) := by
  simp only [funext (regularizedNormRpowGradient_apply s t)]
  fun_prop

/-- For `s ≤ 2` and `t ≥ 0`, every component of the regularized gradient
`TauCeti.regularizedNormRpowGradient s t` is dominated by the corresponding component at
`t = 0`. -/
theorem abs_inner_regularizedNormRpowGradient_le (hs : s ≤ 2) {t : ℝ} (ht : 0 ≤ t) (x v : E) :
    |⟪regularizedNormRpowGradient s t x, v⟫| ≤ |⟪regularizedNormRpowGradient s 0 x, v⟫| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp only [regularizedNormRpowGradient, real_inner_smul_left, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) le_rfl) _)]
  gcongr ?_ * _
  exact mul_le_mul_of_nonneg_left (sq_add_rpow_le (norm_ne_zero_iff.mpr hx) ht (by linarith))
    (abs_nonneg s)

/-- For `s ≤ 2` and `t ≥ 0`, the regularized gradient `TauCeti.regularizedNormRpowGradient s t`
is dominated in norm by its value at `t = 0`. -/
theorem norm_regularizedNormRpowGradient_le (hs : s ≤ 2) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖regularizedNormRpowGradient s t x‖ ≤ ‖regularizedNormRpowGradient s 0 x‖ := by
  set y := regularizedNormRpowGradient s t x
  have h : ‖y‖ * ‖y‖ ≤ ‖regularizedNormRpowGradient s 0 x‖ * ‖y‖ := by
    rw [← real_inner_self_eq_norm_mul_norm, ← abs_of_nonneg (real_inner_self_nonneg (x := y))]
    exact (abs_inner_regularizedNormRpowGradient_le hs ht x y).trans
      (abs_real_inner_le_norm _ _)
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right h h0

/-- For `s ≤ 2` and `t ≥ 0`, the regularized gradient `TauCeti.regularizedNormRpowGradient s t` is
bounded by `|s| ‖x‖ ^ (s - 1)`, the norm of the gradient of `‖x‖ ^ s` away from the origin. -/
theorem norm_regularizedNormRpowGradient_le_mul_rpow (hs : s ≤ 2) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖regularizedNormRpowGradient s t x‖ ≤ |s| * ‖x‖ ^ (s - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [regularizedNormRpowGradient_zero, norm_zero]
    exact mul_nonneg (abs_nonneg s) (Real.rpow_nonneg le_rfl _)
  have hN := norm_pos_iff.2 hx
  refine (norm_regularizedNormRpowGradient_le hs ht x).trans_eq ?_
  rw [regularizedNormRpowGradient_zero_right, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hN _), mul_assoc, ← Real.rpow_add_one hN.ne',
    show s - 2 + 1 = s - 1 by ring]

/-- The regularized gradient `TauCeti.regularizedNormRpowGradient s t x` depends continuously on
the regularization parameter `t` at `t = 0`. -/
theorem continuousAt_regularizedNormRpowGradient_apply_zero (x : E) :
    ContinuousAt (fun t : ℝ => regularizedNormRpowGradient s t x) 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa only [regularizedNormRpowGradient_zero] using continuousAt_const
  exact ((continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx) _).const_mul s).smul continuousAt_const

/-- Away from the origin, the gradient of `‖x‖ ^ s` is the unregularized field
`TauCeti.regularizedNormRpowGradient s 0`. -/
theorem gradient_norm_rpow_eq_regularizedNormRpowGradient [CompleteSpace E] {x : E}
    (hx : x ≠ 0) : ∇ (fun y : E => ‖y‖ ^ s) x = regularizedNormRpowGradient s 0 x := by
  rw [gradient_norm_rpow_of_ne hx, regularizedNormRpowGradient_zero_right]

/-! ### The regularized Hessian -/

/-- The derivative `v ↦ s (‖x‖ ^ 2 + t) ^ (s / 2 - 1) v + s (s - 2) (‖x‖ ^ 2 + t) ^ (s / 2 - 2)
⟪x, v⟫ x` of the regularized gradient `TauCeti.regularizedNormRpowGradient s t` at `x`
(`TauCeti.hasFDerivAt_regularizedNormRpowGradient`). At `t = 0` and away from the origin it is the
Hessian of `‖x‖ ^ s`
(`TauCeti.iteratedGradientChain_one_norm_rpow_eq_regularizedNormRpowHessian`). -/
def regularizedNormRpowHessian (s t : ℝ) (x : E) : E →L[ℝ] E :=
  (s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1)) • ContinuousLinearMap.id ℝ E +
    (s * (s - 2) * (‖x‖ ^ 2 + t) ^ (s / 2 - 2)) • (innerSL ℝ x).smulRight x

/-- Evaluating `TauCeti.regularizedNormRpowHessian s t x` at a vector. -/
theorem regularizedNormRpowHessian_apply (s t : ℝ) (x v : E) :
    regularizedNormRpowHessian s t x v = (s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1)) • v +
      (s * (s - 2) * (‖x‖ ^ 2 + t) ^ (s / 2 - 2) * ⟪x, v⟫) • x := by
  simp only [regularizedNormRpowHessian, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

/-- Without regularization, the regularized Hessian is
`v ↦ s ‖x‖ ^ (s - 2) v + s (s - 2) ‖x‖ ^ (s - 4) ⟪x, v⟫ x`. -/
theorem regularizedNormRpowHessian_zero_apply (s : ℝ) (x v : E) :
    regularizedNormRpowHessian s 0 x v = (s * ‖x‖ ^ (s - 2)) • v +
      (s * (s - 2) * ‖x‖ ^ (s - 4) * ⟪x, v⟫) • x := by
  rw [regularizedNormRpowHessian_apply, add_zero, show s / 2 - 1 = (s - 2) / 2 by ring,
    show s / 2 - 2 = (s - 4) / 2 by ring, Real.sq_rpow_div_two (norm_nonneg x),
    Real.sq_rpow_div_two (norm_nonneg x)]

/-- Where `‖x‖ ^ 2 + t ≠ 0`, the regularized gradient `TauCeti.regularizedNormRpowGradient s t`
has derivative `TauCeti.regularizedNormRpowHessian s t x`. -/
theorem hasFDerivAt_regularizedNormRpowGradient (s t : ℝ) {x : E} (hx : ‖x‖ ^ 2 + t ≠ 0) :
    HasFDerivAt (regularizedNormRpowGradient s t) (regularizedNormRpowHessian s t x) x := by
  have hs : HasFDerivAt (fun y : E => ‖y‖ ^ 2 + t) (2 • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).add_const t
  have hc := ((hs.rpow_const (p := s / 2 - 1) (Or.inl hx)).const_mul s).smul
    (hasFDerivAt_id x)
  refine hc.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    regularizedNormRpowHessian_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, id_eq]
  rw [show s / 2 - 1 - 1 = s / 2 - 2 by ring, add_right_inj]
  congr 1
  ring

/-- For `s ≤ 2` and `t ≥ 0`, away from the origin, the regularized Hessian
`TauCeti.regularizedNormRpowHessian s t x` has operator norm at most
`|s| (3 - s) ‖x‖ ^ (s - 2)`. -/
theorem norm_regularizedNormRpowHessian_le (hs : s ≤ 2) {t : ℝ} (ht : 0 ≤ t) {x : E}
    (hx : x ≠ 0) : ‖regularizedNormRpowHessian s t x‖ ≤ |s| * (3 - s) * ‖x‖ ^ (s - 2) := by
  have hpos : 0 < ‖x‖ ^ 2 + t := by positivity
  set q := ‖x‖ ^ 2 + t
  -- `q ^ (s / 2 - 2) ‖x‖² ≤ q ^ (s / 2 - 1)`, since `‖x‖² ≤ q`.
  have hpow : q ^ (s / 2 - 2) * ‖x‖ ^ 2 ≤ q ^ (s / 2 - 1) := by
    calc q ^ (s / 2 - 2) * ‖x‖ ^ 2 ≤ q ^ (s / 2 - 2) * q := by
          gcongr
          exact le_add_of_nonneg_right ht
      _ = q ^ (s / 2 - 1) := by
          rw [← Real.rpow_add_one hpos.ne']
          congr 1
          ring
  have hK : ‖(innerSL ℝ x).smulRight x‖ = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, sq]
  calc ‖regularizedNormRpowHessian s t x‖
      ≤ |s| * q ^ (s / 2 - 1) * ‖ContinuousLinearMap.id ℝ E‖ +
          |s| * (2 - s) * q ^ (s / 2 - 2) * ‖(innerSL ℝ x).smulRight x‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        · rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
        · rw [abs_mul, abs_of_nonpos (by linarith : s - 2 ≤ 0),
            abs_of_pos (Real.rpow_pos_of_pos hpos _), neg_sub]
    _ ≤ |s| * q ^ (s / 2 - 1) * 1 + |s| * (2 - s) * q ^ (s / 2 - 1) := by
        rw [hK, mul_assoc (|s| * (2 - s))]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = |s| * (3 - s) * q ^ (s / 2 - 1) := by ring
    _ ≤ |s| * (3 - s) * ‖x‖ ^ (s - 2) := by
        have : 0 ≤ |s| * (3 - s) := mul_nonneg (abs_nonneg s) (by linarith)
        gcongr
        refine (sq_add_rpow_le (e := s / 2 - 1) (norm_ne_zero_iff.2 hx) ht
          (by linarith)).trans_eq ?_
        rw [add_zero, show s / 2 - 1 = (s - 2) / 2 by ring, Real.sq_rpow_div_two (norm_nonneg x)]

/-- For `t > 0` the regularized Hessian `TauCeti.regularizedNormRpowHessian s t` is
continuous. -/
theorem continuous_regularizedNormRpowHessian {t : ℝ} (ht : 0 < t) :
    Continuous (regularizedNormRpowHessian (E := E) s t) := by
  have h := continuous_norm_sq_add_rpow (E := E) ht
  have hK : Continuous fun x : E => (innerSL ℝ x).smulRight x :=
    (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      ((innerSL ℝ).continuous.prodMk continuous_id)
  exact ((continuous_const.mul (h _)).smul continuous_const).add
    ((continuous_const.mul (h _)).smul hK)

/-- Away from the origin, the regularized Hessian `TauCeti.regularizedNormRpowHessian s t x`
depends continuously on the regularization parameter `t` at `t = 0`. -/
theorem continuousAt_regularizedNormRpowHessian_apply_zero {x : E} (hx : x ≠ 0) :
    ContinuousAt (fun t : ℝ => regularizedNormRpowHessian s t x) 0 := by
  have h := continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx)
  exact (((h _).const_mul s).smul continuousAt_const).add
    (((h _).const_mul (s * (s - 2))).smul continuousAt_const)

/-- Away from the origin, the Hessian of `‖x‖ ^ s` is the unregularized field
`TauCeti.regularizedNormRpowHessian s 0`. -/
theorem iteratedGradientChain_one_norm_rpow_eq_regularizedNormRpowHessian [CompleteSpace E]
    {x : E} (hx : x ≠ 0) :
    iteratedGradientChain (fun y : E => ‖y‖ ^ s) 1 x = regularizedNormRpowHessian s 0 x := by
  ext v
  rw [iteratedGradientChain_one_norm_rpow_apply hx, regularizedNormRpowHessian_zero_apply]

end TauCeti
