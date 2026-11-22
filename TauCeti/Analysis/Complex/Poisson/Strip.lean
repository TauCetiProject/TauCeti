/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Integral
public import TauCeti.Analysis.Complex.VerticalStrip.Basic
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.Circle.Integral

/-!
# Conformal map and Poisson kernels of the vertical strip

For `0 < θ < 1`, `stripToUnitDisc θ z = (exp (i π z) - exp (i π θ)) / (exp (i π z) - exp (-i π θ))`
maps `verticalStrip 0 1` bijectively onto `ball 0 1` (`bijOn_stripToUnitDisc`) with `θ ↦ 0` and
sends `t ↦ i t` and `t ↦ 1 + i t` onto complementary open arcs of `sphere 0 1`
(`range_stripToUnitDisc_mul_I`, `range_stripToUnitDisc_one_add_mul_I`). Continuous boundary
functions sharing common limits at `±∞` glue to a continuous function on `sphere 0 1`
(`exists_continuousOn_sphere_comp_stripToUnitDisc`), and pulling normalized arc length back gives
`stripPoissonKernel₀ θ` (mass `1 - θ`), `stripPoissonKernel₁ θ` (mass `θ`), the probability
measures `stripPoissonMeasure₀ θ` and `stripPoissonMeasure₁ θ`, and
`circleAverage_eq_stripPoissonKernel`.

## Main declarations

* `TauCeti.stripToUnitDisc`, `TauCeti.unitDiscToStrip`, `TauCeti.injOn_stripToUnitDisc`,
  `TauCeti.surjOn_stripToUnitDisc`, `TauCeti.bijOn_stripToUnitDisc`,
  `TauCeti.range_stripToUnitDisc_mul_I`, `TauCeti.range_stripToUnitDisc_one_add_mul_I`.
* `TauCeti.stripPoissonKernel₀`, `TauCeti.stripPoissonKernel₁`,
  `TauCeti.stripPoissonMeasure₀`, `TauCeti.stripPoissonMeasure₁`,
  `TauCeti.stripPoissonMeasure₀_apply`, `TauCeti.stripPoissonMeasure₁_apply`,
  `TauCeti.integrable_stripPoissonMeasure₀_iff`, `TauCeti.integrable_stripPoissonMeasure₁_iff`,
  `TauCeti.integral_stripPoissonMeasure₀`, `TauCeti.integral_stripPoissonMeasure₁`.
* `TauCeti.exists_continuousOn_sphere_comp_stripToUnitDisc` and
  `TauCeti.circleAverage_eq_stripPoissonKernel`.

## References

* I. I. Hirschman, *A convexity theorem for certain groups of transformations*, J. Analyse Math.
  **2** (1952), 209–218.
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §9.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, Lemma 4.3.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set
open scoped ENNReal Topology

namespace TauCeti

/-! ### Conformal map from the strip to the unit disc -/

/-- The conformal map `(exp (i π z) - exp (i π θ)) / (exp (i π z) - exp (-i π θ))` sending the
open strip `0 < re z < 1` onto `ball 0 1` and the real point `θ ∈ (0, 1)` to `0`. -/
def stripToUnitDisc (θ : ℝ) (z : ℂ) : ℂ :=
  (exp (I * π * z) - exp (I * π * θ)) / (exp (I * π * z) - exp (-I * π * θ))

/-- Explicit formula for `stripToUnitDisc`. -/
theorem stripToUnitDisc_def (θ : ℝ) (z : ℂ) : stripToUnitDisc θ z =
    (exp (I * π * z) - exp (I * π * θ)) / (exp (I * π * z) - exp (-I * π * θ)) := (rfl)

/-- At `z = θ`, `stripToUnitDisc θ` vanishes. -/
@[simp]
theorem stripToUnitDisc_self (θ : ℝ) : stripToUnitDisc θ θ = 0 := by simp [stripToUnitDisc]

private theorem sin_pi_mul_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) : 0 < Real.sin (π * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])

private theorem im_exp_I_mul_pi_mul (z : ℂ) :
    (exp (I * π * z)).im = Real.exp (-π * z.im) * Real.sin (π * z.re) := by
  rw [Complex.exp_im]; simp [mul_assoc]

private theorem star_exp_I_mul_pi (θ : ℝ) : star (exp (I * π * θ)) = exp (-I * π * θ) := by
  rw [RCLike.star_def, ← exp_conj]; congr 1; simp

private theorem im_exp_nonneg_of_mem {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    0 ≤ (exp (I * π * z)).im :=
  let ⟨h0, h1⟩ := mem_verticalClosedStrip_iff.1 hz
  im_exp_I_mul_pi_mul z ▸ mul_nonneg (Real.exp_nonneg _)
    (Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩)

private theorem sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ} (hw : 0 ≤ w.im) :
    w - exp (-I * π * θ) ≠ 0 := fun h ↦ by
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have hθ' : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    rw [← star_exp_I_mul_pi, RCLike.star_def, conj_im, im_exp_I_mul_pi_mul]; simp
  linarith [sin_pi_mul_pos hθ]

/-- For `0 < θ < 1`, `stripToUnitDisc θ` is complex-differentiable at every point of the closed
strip. -/
theorem differentiableAt_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : DifferentiableAt ℂ (stripToUnitDisc θ) z :=
  DifferentiableAt.div (by fun_prop) (by fun_prop)
    (sub_exp_neg_I_pi_ne_zero hθ (im_exp_nonneg_of_mem hz))

/-- `stripToUnitDisc θ` is complex-differentiable on the closed strip `0 ≤ re z ≤ 1`. -/
theorem differentiableOn_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    DifferentiableOn ℂ (stripToUnitDisc θ) (verticalClosedStrip 0 1) :=
  fun _ hz ↦ (differentiableAt_stripToUnitDisc hθ hz).differentiableWithinAt

/-- `stripToUnitDisc θ` is holomorphic on `verticalStrip 0 1` and continuous on its closure. -/
theorem diffContOnCl_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    DiffContOnCl ℂ (stripToUnitDisc θ) (verticalStrip 0 1) :=
  ⟨(differentiableOn_stripToUnitDisc hθ).mono (verticalStrip_subset_verticalClosedStrip 0 1),
    (differentiableOn_stripToUnitDisc hθ).continuousOn.mono (closure_verticalStrip_subset 0 1)⟩

private theorem normSq_exp_sub_neg_sub_normSq (θ : ℝ) (z : ℂ) :
    normSq (exp (I * π * z) - exp (-I * π * θ)) - normSq (exp (I * π * z) - exp (I * π * θ)) =
      4 * (exp (I * π * z)).im * Real.sin (π * θ) := by
  have hdiff (w ζ : ℂ) : normSq (w - star ζ) - normSq (w - ζ) = 4 * w.im * ζ.im := by
    simp only [RCLike.star_def, normSq_apply, sub_re, sub_im, conj_re, conj_im]; ring
  rw [← star_exp_I_mul_pi, hdiff, im_exp_I_mul_pi_mul, im_exp_I_mul_pi_mul]; simp

private theorem normSq_sub_mul_one_sub_norm_sq {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : 0 ≤ (exp (I * π * z)).im) :
    normSq (exp (I * π * z) - exp (-I * π * θ)) * (1 - ‖stripToUnitDisc θ z‖ ^ 2) =
      4 * (exp (I * π * z)).im * Real.sin (π * θ) := by
  have hden : normSq (exp (I * π * z) - exp (-I * π * θ)) ≠ 0 :=
    (normSq_pos.2 (sub_exp_neg_I_pi_ne_zero hθ hz)).ne'
  rw [← normSq_eq_norm_sq, stripToUnitDisc, map_div₀, mul_sub, mul_one, mul_div_cancel₀ _ hden]
  exact normSq_exp_sub_neg_sub_normSq θ z

/-- On the open strip `0 < re z < 1`, `stripToUnitDisc θ` takes values in the open unit disc. -/
theorem stripToUnitDisc_mem_ball {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : stripToUnitDisc θ z ∈ ball 0 1 := by
  have ⟨h0, h1⟩ := mem_verticalStrip_iff.1 hz
  have hwim : 0 < (exp (I * π * z)).im := im_exp_I_mul_pi_mul z ▸ mul_pos (Real.exp_pos _)
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos h0) (by nlinarith [pi_pos]))
  have hpos : 0 < 1 - ‖stripToUnitDisc θ z‖ ^ 2 := by
    nlinarith [normSq_sub_mul_one_sub_norm_sq hθ hwim.le, sin_pi_mul_pos hθ,
      normSq_pos.2 (sub_exp_neg_I_pi_ne_zero hθ hwim.le)]
  exact mem_ball_zero_iff.2 ((sq_lt_one_iff₀ (norm_nonneg _)).1 (by linarith))

/-- On the closed strip `0 ≤ re z ≤ 1`, `stripToUnitDisc θ` has norm at most `1`. -/
theorem norm_stripToUnitDisc_le_one {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖stripToUnitDisc θ z‖ ≤ 1 := by
  have hwim := im_exp_nonneg_of_mem hz
  have hnonneg : 0 ≤ 1 - ‖stripToUnitDisc θ z‖ ^ 2 := by
    nlinarith [normSq_sub_mul_one_sub_norm_sq hθ hwim, sin_pi_mul_pos hθ,
      normSq_pos.2 (sub_exp_neg_I_pi_ne_zero hθ hwim)]
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 (by linarith)

private theorem exp_I_mul_pi_mul_I (t : ℝ) : exp (I * π * (t * I)) = Real.exp (-π * t) := by
  have harg : I * ↑π * (↑t * I) = ((-π * t : ℝ) : ℂ) := by
    push_cast; linear_combination (π * t : ℂ) * I_mul_I
  rw [harg, ofReal_exp]

private theorem exp_I_mul_pi_one_add_mul_I (t : ℝ) :
    exp (I * π * (1 + t * I)) = -(Real.exp (-π * t) : ℂ) := by
  have harg : I * ↑π * (1 + ↑t * I) = ((-π * t : ℝ) : ℂ) + ↑π * I := by
    push_cast; linear_combination (π * t : ℂ) * I_mul_I
  rw [harg, Complex.exp_add, exp_pi_mul_I, ofReal_exp, mul_neg_one]

/-- Conjugation exchanges the two boundary lines of `stripToUnitDisc` under `θ ↔ 1 - θ`. -/
theorem star_stripToUnitDisc_one_sub_one_add_mul_I (θ t : ℝ) :
    star (stripToUnitDisc (1 - θ) (1 + t * I)) = stripToUnitDisc θ (t * I) := by
  have harg : I * ↑π * ↑(1 - θ) = -I * ↑π * ↑θ + ↑π * I := by push_cast; ring
  have he : (starRingEnd ℂ) (exp (I * ↑π * ↑(1 - θ))) = -exp (I * ↑π * ↑θ) := by
    rw [harg, Complex.exp_add, exp_pi_mul_I, mul_neg_one, map_neg, ← exp_conj]
    congr 2; simp
  rw [stripToUnitDisc, stripToUnitDisc, exp_I_mul_pi_one_add_mul_I, exp_I_mul_pi_mul_I]
  simp only [RCLike.star_def, neg_mul, Complex.exp_neg, map_div₀, map_sub, map_neg, map_inv₀,
    conj_ofReal, he, inv_neg]
  rw [← neg_div_neg_eq]; congr 1 <;> ring

/-- The right boundary line `re z = 1` maps into the unit circle. -/
theorem stripToUnitDisc_one_add_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (1 + t * I) ∈ sphere 0 1 := by
  have him : (exp (I * π * (1 + t * I))).im = 0 := by
    rw [exp_I_mul_pi_one_add_mul_I, neg_im, ofReal_im, neg_zero]
  have hsq := normSq_sub_mul_one_sub_norm_sq hθ him.ge
  rw [him, mul_zero, zero_mul, mul_eq_zero] at hsq
  have h1 : ‖stripToUnitDisc θ (1 + t * I)‖ ^ 2 = 1 := by
    linarith [hsq.resolve_left (normSq_pos.2 (sub_exp_neg_I_pi_ne_zero hθ him.ge)).ne']
  rw [mem_sphere_zero_iff_norm, ← Real.sqrt_sq (norm_nonneg _), h1, Real.sqrt_one]

/-- The left boundary line `re z = 0` maps into the unit circle. -/
theorem stripToUnitDisc_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (t * I) ∈ sphere 0 1 := by
  rw [← star_stripToUnitDisc_one_sub_one_add_mul_I, mem_sphere_zero_iff_norm, norm_star,
    ← mem_sphere_zero_iff_norm]
  exact stripToUnitDisc_one_add_mul_I_mem_sphere (sub_mem_Ioo_zero_iff_right.2 hθ) t

/-! ### Strip Poisson kernels and probability measures -/

/-- The left-boundary Poisson kernel of the vertical strip `0 ≤ re z ≤ 1` at `z = θ ∈ (0, 1)`. -/
def stripPoissonKernel₀ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- Explicit formula for `stripPoissonKernel₀`. -/
theorem stripPoissonKernel₀_def (θ t : ℝ) : stripPoissonKernel₀ θ t =
    Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ))) := (rfl)

/-- The right-boundary Poisson kernel of the vertical strip `0 ≤ re z ≤ 1` at `z = θ ∈ (0, 1)`. -/
def stripPoissonKernel₁ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ)))

/-- Explicit formula for `stripPoissonKernel₁`. -/
theorem stripPoissonKernel₁_def (θ t : ℝ) : stripPoissonKernel₁ θ t =
    Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ))) := (rfl)

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub (θ t : ℝ) :
    stripPoissonKernel₀ θ t = stripPoissonKernel₁ (1 - θ) t := by
  rw [stripPoissonKernel₀, stripPoissonKernel₁, mul_sub π 1 θ, mul_one,
    Real.sin_pi_sub, Real.cos_pi_sub]; ring

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoissonKernel₁_eq_stripPoissonKernel₀_one_sub (θ t : ℝ) :
    stripPoissonKernel₁ θ t = stripPoissonKernel₀ (1 - θ) t := by
  rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub, sub_sub_cancel]

/-- `stripPoissonKernel₀ θ` is an even function of `t`. -/
@[simp]
theorem stripPoissonKernel₀_neg (θ t : ℝ) : stripPoissonKernel₀ θ (-t) = stripPoissonKernel₀ θ t :=
  by simp [stripPoissonKernel₀, mul_neg, Real.cosh_neg]

/-- `stripPoissonKernel₁ θ` is an even function of `t`. -/
@[simp]
theorem stripPoissonKernel₁_neg (θ t : ℝ) : stripPoissonKernel₁ θ (-t) = stripPoissonKernel₁ θ t :=
  by simp [stripPoissonKernel₁, mul_neg, Real.cosh_neg]

private theorem cosh_add_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < Real.cosh (π * t) + Real.cos (π * θ) :=
  have hcos : -1 < Real.cos (π * θ) := Real.cos_pi ▸ Real.strictAntiOn_cos
    ⟨by nlinarith [pi_pos, hθ.1], by nlinarith [pi_pos, hθ.2]⟩ ⟨pi_pos.le, le_rfl⟩
    (by nlinarith [pi_pos, hθ.2])
  by linarith [Real.one_le_cosh (π * t)]

/-- For `0 < θ < 1`, `stripPoissonKernel₁ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₁_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoissonKernel₁ θ t :=
  div_pos (sin_pi_mul_pos hθ) (mul_pos two_pos (cosh_add_cos_pos hθ t))

/-- For `0 < θ < 1`, `stripPoissonKernel₀ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoissonKernel₀ θ t :=
  stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ t ▸
    stripPoissonKernel₁_pos (sub_mem_Ioo_zero_iff_right.2 hθ) t

/-- For `0 < θ < 1`, `stripPoissonKernel₁ θ` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Continuous (stripPoissonKernel₁ θ) :=
  continuous_const.div (by fun_prop) fun t ↦ (mul_pos two_pos (cosh_add_cos_pos hθ t)).ne'

/-- For `0 < θ < 1`, `stripPoissonKernel₀ θ` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Continuous (stripPoissonKernel₀ θ) :=
  funext (stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ) ▸
    continuous_stripPoissonKernel₁ (sub_mem_Ioo_zero_iff_right.2 hθ)

/-! ### Boundary angle parametrizations and total mass -/

private def rightBoundaryAngle (θ t : ℝ) : ℝ :=
  π - 2 * Real.arctan ((Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ))

private def leftBoundaryAngle (θ t : ℝ) : ℝ := 2 * π - rightBoundaryAngle (1 - θ) t

private theorem exp_I_mul_pi_ofReal (θ : ℝ) :
    exp (I * π * θ) = (Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I := by
  have harg : I * ↑π * ↑θ = ((π * θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg, exp_ofReal_mul_I]

private theorem circleMap_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (rightBoundaryAngle θ t) = stripToUnitDisc θ (1 + t * I) := by
  have hneg : exp (-I * π * θ) = (Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I := by
    rw [← star_exp_I_mul_pi, exp_I_mul_pi_ofReal, RCLike.star_def, map_add, map_mul,
      conj_ofReal, conj_ofReal, conj_I, mul_neg, ← sub_eq_add_neg]
  rw [rightBoundaryAngle, circleMap_pi_sub_two_arctan (sin_pi_mul_pos hθ).ne', stripToUnitDisc,
    exp_I_mul_pi_one_add_mul_I, exp_I_mul_pi_ofReal, hneg, ofReal_add, ← neg_div_neg_eq]
  congr 1 <;> ring

private theorem circleMap_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (leftBoundaryAngle θ t) = stripToUnitDisc θ (t * I) := by
  have harg : ((2 * π - rightBoundaryAngle (1 - θ) t : ℝ) : ℂ) * I =
      2 * ↑π * I + (-(rightBoundaryAngle (1 - θ) t) : ℝ) * I := by
    push_cast; ring
  rw [← star_stripToUnitDisc_one_sub_one_add_mul_I,
    ← circleMap_rightBoundaryAngle (sub_mem_Ioo_zero_iff_right.2 hθ)]
  simp only [leftBoundaryAngle, circleMap, zero_add, ofReal_one, one_mul]
  rw [harg, Complex.exp_add, exp_two_pi_mul_I, one_mul, RCLike.star_def, ← exp_conj]
  congr 1; simp

private theorem hasDerivAt_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (rightBoundaryAngle θ) (2 * π * stripPoissonKernel₁ θ t) t := by
  set s := Real.sin (π * θ); set c := Real.cos (π * θ)
  have hu : HasDerivAt (fun x ↦ (Real.exp (-(π * x)) + c) / s)
      (-(Real.exp (-(π * t)) * π) / s) t := by
    simpa [neg_mul] using (((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-π))).add_const c).div_const s
  refine ((((Real.hasDerivAt_arctan' _).comp t hu).const_mul (-2)
    |>.const_add π).congr_of_eventuallyEq (.of_forall fun x ↦ by
      simp [rightBoundaryAngle, s, c, sub_eq_add_neg, neg_mul])).congr_deriv ?_
  have hs : s ≠ 0 := (sin_pi_mul_pos hθ).ne'
  have hden : 0 < Real.cosh (π * t) + c := cosh_add_cos_pos hθ t
  have h1 : 1 + ((Real.exp (-(π * t)) + c) / s) ^ 2 ≠ 0 := by positivity
  rw [stripPoissonKernel₁]; dsimp only [s, c] at *
  field_simp [hs, hden.ne', h1]
  rw [Real.cosh_eq, Real.exp_neg, Real.sin_sq]; field_simp [Real.exp_ne_zero (π * t)]; ring

private theorem hasDerivAt_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (leftBoundaryAngle θ) (-(2 * π * stripPoissonKernel₀ θ t)) t := by
  rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]
  exact (hasDerivAt_rightBoundaryAngle (sub_mem_Ioo_zero_iff_right.2 hθ) t).const_sub (2 * π)

private theorem strictMono_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    StrictMono (rightBoundaryAngle θ) :=
  strictMono_of_deriv_pos fun t ↦ (hasDerivAt_rightBoundaryAngle hθ t).deriv.symm ▸
    mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)

private theorem strictAnti_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    StrictAnti (leftBoundaryAngle θ) := fun _ _ hab ↦
  sub_lt_sub_left (strictMono_rightBoundaryAngle (sub_mem_Ioo_zero_iff_right.2 hθ) hab) _

private theorem tendsto_rightBoundaryAngle_atBot {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Tendsto (rightBoundaryAngle θ) atBot (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atBot atTop := Real.tendsto_exp_atTop.comp
    ((tendsto_neg_atBot_atTop.const_mul_atTop pi_pos).congr fun _ ↦ by ring)
  exact ((by ring : π - 2 * (π / 2) = 0) ▸ (tendsto_const_nhds (x := π)).sub
    (((tendsto_nhdsWithin_iff.1 Real.tendsto_arctan_atTop).1.comp
      ((hexp.atTop_add (tendsto_const_nhds (x := Real.cos (π * θ)))).atTop_div_const
        (sin_pi_mul_pos hθ))).const_mul 2)).congr fun _ ↦ rfl

private theorem tendsto_rightBoundaryAngle_atTop {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Tendsto (rightBoundaryAngle θ) atTop (𝓝 (2 * π * θ)) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
    ((tendsto_neg_atTop_atBot.const_mul_atBot pi_pos).congr fun _ ↦ by ring)
  have hval : π - 2 * Real.arctan ((0 + Real.cos (π * θ)) / Real.sin (π * θ)) = 2 * π * θ := by
    rw [zero_add, ← Real.sin_pi_div_two_sub (π * θ), ← Real.cos_pi_div_two_sub (π * θ),
      ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by nlinarith [pi_pos, hθ.2])
        (by nlinarith [pi_pos, hθ.1])]; ring
  exact (hval ▸ ((by fun_prop : Continuous fun x : ℝ ↦
    π - 2 * Real.arctan ((x + Real.cos (π * θ)) / Real.sin (π * θ))).tendsto 0).comp hexp).congr
    fun _ ↦ rfl

private theorem range_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (rightBoundaryAngle θ) = Ioo 0 (2 * π * θ) := by
  have hmono := strictMono_rightBoundaryAngle hθ
  have hbot := tendsto_rightBoundaryAngle_atBot hθ
  have htop := tendsto_rightBoundaryAngle_atTop hθ
  refine Subset.antisymm ?_ fun y hy ↦ intermediate_value_univ₂_eventually₂
    (by unfold rightBoundaryAngle; fun_prop) continuous_const
    (hbot.eventually_le_const hy.1) (htop.eventually_const_le hy.2)
  rintro _ ⟨t, rfl⟩
  exact ⟨lt_of_le_of_lt (le_of_tendsto hbot ((eventually_le_atBot (t - 1)).mono fun _ hx ↦
      hmono.monotone hx)) (hmono (sub_one_lt t)),
    lt_of_lt_of_le (hmono (lt_add_one t)) (ge_of_tendsto htop ((eventually_ge_atTop (t + 1)).mono
      fun _ hx ↦ hmono.monotone hx))⟩

private theorem range_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (leftBoundaryAngle θ) = Ioo (2 * π * θ) (2 * π) := by
  ext y
  have h : y ∈ range (leftBoundaryAngle θ) ↔ 2 * π - y ∈ range (rightBoundaryAngle (1 - θ)) :=
    exists_congr fun _ ↦ by simp only [leftBoundaryAngle]; constructor <;> intro h <;> linarith
  have hsub : 2 * π - 2 * π * (1 - θ) = 2 * π * θ := by ring
  rw [h, range_rightBoundaryAngle (sub_mem_Ioo_zero_iff_right.2 hθ), sub_mem_Ioo_iff_right,
    sub_zero, hsub]

/-- For `0 < θ < 1`, `t ↦ stripToUnitDisc θ (1 + t * I)` parametrizes the open unit-circle arc
with angles `(0, 2πθ)`. -/
theorem range_stripToUnitDisc_one_add_mul_I {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (fun t : ℝ ↦ stripToUnitDisc θ (1 + t * I)) =
      circleMap 0 1 '' Ioo 0 (2 * π * θ) := by
  have h : (fun t : ℝ ↦ stripToUnitDisc θ (1 + t * I)) = circleMap 0 1 ∘ rightBoundaryAngle θ :=
    funext fun t ↦ (circleMap_rightBoundaryAngle hθ t).symm
  rw [h, Set.range_comp, range_rightBoundaryAngle hθ]

/-- For `0 < θ < 1`, `t ↦ stripToUnitDisc θ (t * I)` parametrizes the open unit-circle arc with
angles `(2πθ, 2π)`. -/
theorem range_stripToUnitDisc_mul_I {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (fun t : ℝ ↦ stripToUnitDisc θ (t * I)) =
      circleMap 0 1 '' Ioo (2 * π * θ) (2 * π) := by
  have h : (fun t : ℝ ↦ stripToUnitDisc θ (t * I)) = circleMap 0 1 ∘ leftBoundaryAngle θ :=
    funext fun t ↦ (circleMap_leftBoundaryAngle hθ t).symm
  rw [h, Set.range_comp, range_leftBoundaryAngle hθ]

private theorem boundary_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g d k : ℝ → ℝ} {b : ℝ → ℂ} {s : Set ℝ} (ψ : ℂ → E)
    (hrange : range g = s) (hinj : Function.Injective g) (hd : ∀ t, HasDerivAt g (d t) t)
    (habs : ∀ t, |d t| = 2 * π * k t) (hb : ∀ t, circleMap 0 1 (g t) = b t) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) s ↔ Integrable (fun t ↦ k t • ψ (b t))) ∧
      (∫ φ in s, ψ (circleMap 0 1 φ)) = (2 * π) • ∫ t, k t • ψ (b t) :=
  ⟨integrableOn_circleMap_iff_of_hasDerivAt hrange hinj hd habs hb,
    setIntegral_circleMap_eq_of_hasDerivAt hrange hinj hd habs hb⟩

private theorem rightBoundary_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (ψ : ℂ → E) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo 0 (2 * π * θ)) ↔
      Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)))) ∧
      (∫ φ in Ioo 0 (2 * π * θ), ψ (circleMap 0 1 φ)) =
        (2 * π) • ∫ t, stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)) :=
  boundary_pullback ψ (range_rightBoundaryAngle hθ)
    (strictMono_rightBoundaryAngle hθ).injective (hasDerivAt_rightBoundaryAngle hθ)
    (fun t ↦ abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)))
    (circleMap_rightBoundaryAngle hθ)

private theorem leftBoundary_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (ψ : ℂ → E) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo (2 * π * θ) (2 * π)) ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I)))) ∧
      (∫ φ in Ioo (2 * π * θ) (2 * π), ψ (circleMap 0 1 φ)) =
        (2 * π) • ∫ t, stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I)) :=
  boundary_pullback ψ (range_leftBoundaryAngle hθ)
    (strictAnti_leftBoundaryAngle hθ).injective (hasDerivAt_leftBoundaryAngle hθ)
    (fun t ↦ (abs_neg _).trans (abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₀_pos hθ t))))
    (circleMap_leftBoundaryAngle hθ)

/-- The right-boundary strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Integrable (stripPoissonKernel₁ θ) := by
  simpa using (rightBoundary_pullback hθ (fun _ ↦ (1 : ℝ))).1.1
    (integrableOn_const (hs := measure_Ioo_lt_top.ne))

/-- The left-boundary strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Integrable (stripPoissonKernel₀ θ) :=
  funext (stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ) ▸
    integrable_stripPoissonKernel₁ (sub_mem_Ioo_zero_iff_right.2 hθ)

/-- The right-boundary strip Poisson kernel has total integral `θ` on `ℝ`. -/
@[simp]
theorem integral_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∫ t, stripPoissonKernel₁ θ t = θ := by
  have h := (rightBoundary_pullback hθ (fun _ ↦ (1 : ℝ))).2
  simp only [setIntegral_const, Real.volume_real_Ioo, sub_zero,
    max_eq_left (mul_nonneg two_pi_pos.le hθ.1.le), smul_eq_mul, mul_one] at h
  exact mul_left_cancel₀ two_pi_pos.ne' h.symm

/-- The left-boundary strip Poisson kernel has total integral `1 - θ` on `ℝ`. -/
@[simp]
theorem integral_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∫ t, stripPoissonKernel₀ θ t = 1 - θ := by
  simp_rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]
  exact integral_stripPoissonKernel₁ (sub_mem_Ioo_zero_iff_right.2 hθ)

/-- Normalized probability measure `(1 - θ)⁻¹ μ₀(θ, t) dt` on the left boundary of the strip. -/
def stripPoissonMeasure₀ (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal ((1 - θ)⁻¹ * stripPoissonKernel₀ θ t)

/-- Explicit formula for `stripPoissonMeasure₀`. -/
theorem stripPoissonMeasure₀_def (θ : ℝ) : stripPoissonMeasure₀ θ =
    volume.withDensity fun t ↦ ENNReal.ofReal ((1 - θ)⁻¹ * stripPoissonKernel₀ θ t) := (rfl)

/-- Evaluation of `stripPoissonMeasure₀ θ` on a measurable set. -/
theorem stripPoissonMeasure₀_apply (θ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    stripPoissonMeasure₀ θ s =
      ∫⁻ t in s, ENNReal.ofReal ((1 - θ)⁻¹ * stripPoissonKernel₀ θ t) :=
  withDensity_apply _ hs

/-- Normalized probability measure `θ⁻¹ μ₁(θ, t) dt` on the right boundary of the strip. -/
def stripPoissonMeasure₁ (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal (θ⁻¹ * stripPoissonKernel₁ θ t)

/-- Explicit formula for `stripPoissonMeasure₁`. -/
theorem stripPoissonMeasure₁_def (θ : ℝ) : stripPoissonMeasure₁ θ =
    volume.withDensity fun t ↦ ENNReal.ofReal (θ⁻¹ * stripPoissonKernel₁ θ t) := (rfl)

/-- Evaluation of `stripPoissonMeasure₁ θ` on a measurable set. -/
theorem stripPoissonMeasure₁_apply (θ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    stripPoissonMeasure₁ θ s =
      ∫⁻ t in s, ENNReal.ofReal (θ⁻¹ * stripPoissonKernel₁ θ t) :=
  withDensity_apply _ hs

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson probability measures. -/
theorem stripPoissonMeasure₀_eq_stripPoissonMeasure₁_one_sub (θ : ℝ) :
    stripPoissonMeasure₀ θ = stripPoissonMeasure₁ (1 - θ) := by
  simp_rw [stripPoissonMeasure₀, stripPoissonMeasure₁,
    stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson probability measures. -/
theorem stripPoissonMeasure₁_eq_stripPoissonMeasure₀_one_sub (θ : ℝ) :
    stripPoissonMeasure₁ θ = stripPoissonMeasure₀ (1 - θ) := by
  rw [stripPoissonMeasure₀_eq_stripPoissonMeasure₁_one_sub, sub_sub_cancel]

/-- For `0 < θ < 1`, `stripPoissonMeasure₁ θ` is a probability measure on `ℝ`. -/
theorem isProbabilityMeasure_stripPoissonMeasure₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    IsProbabilityMeasure (stripPoissonMeasure₁ θ) := ⟨by
  simp [stripPoissonMeasure₁, ← ofReal_integral_eq_lintegral_ofReal
    ((integrable_stripPoissonKernel₁ hθ).const_mul θ⁻¹) (.of_forall fun t ↦
      mul_nonneg (inv_nonneg.2 hθ.1.le) (stripPoissonKernel₁_pos hθ t).le),
    integral_const_mul, hθ, hθ.1.ne']⟩

/-- For `0 < θ < 1`, `stripPoissonMeasure₀ θ` is a probability measure on `ℝ`. -/
theorem isProbabilityMeasure_stripPoissonMeasure₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    IsProbabilityMeasure (stripPoissonMeasure₀ θ) :=
  stripPoissonMeasure₀_eq_stripPoissonMeasure₁_one_sub θ ▸
    isProbabilityMeasure_stripPoissonMeasure₁ (sub_mem_Ioo_zero_iff_right.2 hθ)

/-- Integrability against `stripPoissonMeasure₁ θ` is equivalent to integrability of the
`stripPoissonKernel₁ θ`-weighted function. -/
theorem integrable_stripPoissonMeasure₁_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    Integrable f (stripPoissonMeasure₁ θ) ↔
      Integrable (fun t ↦ stripPoissonKernel₁ θ t • f t) := by
  rw [stripPoissonMeasure₁, integrable_withDensity_iff_integrable_smul'
    ((continuous_stripPoissonKernel₁ hθ).const_mul _).measurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hθ.1.le)
    (stripPoissonKernel₁_pos hθ _).le), mul_smul]
  exact integrable_smul_iff (inv_ne_zero hθ.1.ne') _

/-- Integrability against `stripPoissonMeasure₀ θ` is equivalent to integrability of the
`stripPoissonKernel₀ θ`-weighted function. -/
theorem integrable_stripPoissonMeasure₀_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    Integrable f (stripPoissonMeasure₀ θ) ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • f t) := by
  rw [stripPoissonMeasure₀_eq_stripPoissonMeasure₁_one_sub,
    integrable_stripPoissonMeasure₁_iff (sub_mem_Ioo_zero_iff_right.2 hθ)]
  simp_rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]

/-- Bochner integration against `stripPoissonMeasure₁ θ` equals `θ⁻¹` times integration against
`stripPoissonKernel₁ θ`. -/
theorem integral_stripPoissonMeasure₁ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    ∫ t, f t ∂stripPoissonMeasure₁ θ = θ⁻¹ • ∫ t, stripPoissonKernel₁ θ t • f t := by
  rw [stripPoissonMeasure₁, integral_withDensity_eq_integral_toReal_smul
    ((continuous_stripPoissonKernel₁ hθ).const_mul _).measurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hθ.1.le)
    (stripPoissonKernel₁_pos hθ _).le), mul_smul, integral_smul]

/-- Bochner integration against `stripPoissonMeasure₀ θ` equals `(1 - θ)⁻¹` times integration
against `stripPoissonKernel₀ θ`. -/
theorem integral_stripPoissonMeasure₀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    ∫ t, f t ∂stripPoissonMeasure₀ θ = (1 - θ)⁻¹ • ∫ t, stripPoissonKernel₀ θ t • f t := by
  rw [stripPoissonMeasure₀_eq_stripPoissonMeasure₁_one_sub,
    integral_stripPoissonMeasure₁ (sub_mem_Ioo_zero_iff_right.2 hθ)]
  simp_rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]

/-! ### Circle averages pulled back to the strip boundary -/

/-- Circle-integrability on the unit circle is equivalent to integrability against both strip
Poisson kernels along the boundary lines of the strip. -/
theorem circleIntegrable_iff_stripPoissonKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {ψ : ℂ → E} :
    CircleIntegrable ψ 0 1 ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) ∧
        Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I))) := by
  rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le,
    ← Ioc_union_Ioc_eq_Ioc (mul_nonneg two_pi_pos.le hθ.1.le)
      (mul_le_of_le_one_right two_pi_pos.le hθ.2.le),
    integrableOn_union, integrableOn_Ioc_iff_integrableOn_Ioo,
    integrableOn_Ioc_iff_integrableOn_Ioo, and_comm,
    (rightBoundary_pullback hθ ψ).1, (leftBoundary_pullback hθ ψ).1]

/-- **Change of variables from the unit circle to the strip boundary.** For `0 < θ < 1` and
circle-integrable data `ψ` on `sphere 0 1`, `circleAverage ψ 0 1` equals the sum of the two
boundary integrals against `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem circleAverage_eq_stripPoissonKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {ψ : ℂ → E} (hψ : CircleIntegrable ψ 0 1) :
    circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) +
        ∫ t, stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)) := by
  have h0 : 0 ≤ 2 * π * θ := mul_nonneg two_pi_pos.le hθ.1.le
  have h1 : 2 * π * θ ≤ 2 * π := mul_le_of_le_one_right two_pi_pos.le hθ.2.le
  have hψ' := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
    ((circleIntegrable_def _ _ _).1 hψ)
  rw [circleAverage_def, ← intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h0).2 (hψ'.mono_set (Ioc_subset_Ioc_right h1)))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1).2 (hψ'.mono_set (Ioc_subset_Ioc_left h0))),
    intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h1,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    (rightBoundary_pullback hθ ψ).2, (leftBoundary_pullback hθ ψ).2,
    add_comm, ← smul_add, inv_smul_smul₀ two_pi_pos.ne']

/-! ### Gluing strip boundary data onto the unit circle -/

private def unitDiscToExpStrip (θ : ℝ) (w : ℂ) : ℂ :=
  (exp (I * π * θ) - w * exp (-I * π * θ)) / (1 - w)

private theorem im_unitDiscToExpStrip (θ : ℝ) (w : ℂ) :
    (unitDiscToExpStrip θ w).im = (1 - normSq w) * Real.sin (π * θ) / normSq (1 - w) := by
  have him : (exp (I * π * θ)).im = Real.sin (π * θ) := by
    rw [im_exp_I_mul_pi_mul]; simp
  rw [unitDiscToExpStrip, Complex.div_im]
  have h1 : (exp (I * π * θ) - w * exp (-I * π * θ)).im * (1 - w).re -
      (exp (I * π * θ) - w * exp (-I * π * θ)).re * (1 - w).im =
      (1 - normSq w) * Real.sin (π * θ) := by
    rw [← star_exp_I_mul_pi, ← him]
    simp only [RCLike.star_def, normSq_apply, sub_re, sub_im, mul_re, mul_im,
      conj_re, conj_im, one_re, one_im]
    ring
  rw [← h1]
  ring

private theorem exp_I_pi_sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    exp (I * π * θ) - exp (-I * π * θ) ≠ 0 :=
  sub_exp_neg_I_pi_ne_zero hθ (by rw [im_exp_I_mul_pi_mul]; simpa using (sin_pi_mul_pos hθ).le)

private theorem stripToUnitDisc_cayley {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ}
    (hw : w - exp (-I * π * θ) ≠ 0) :
    (w - exp (I * π * θ)) / (w - exp (-I * π * θ)) ≠ 1 ∧
      unitDiscToExpStrip θ ((w - exp (I * π * θ)) / (w - exp (-I * π * θ))) = w := by
  have hne1 : (w - exp (I * π * θ)) / (w - exp (-I * π * θ)) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hw, sub_right_inj]
    exact fun h ↦ exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ (sub_eq_zero.2 h)
  refine ⟨hne1, ?_⟩
  rw [unitDiscToExpStrip, div_eq_iff (sub_ne_zero.2 hne1.symm)]
  apply mul_right_cancel₀ hw
  rw [sub_mul, mul_right_comm (_ / _), div_mul_cancel₀ _ hw, mul_assoc w, sub_mul 1,
    one_mul, div_mul_cancel₀ _ hw]
  ring

private theorem stripToUnitDisc_cayley_symm {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {u : ℂ} (hu : u ≠ 1) :
    unitDiscToExpStrip θ u - exp (-I * π * θ) ≠ 0 ∧
      (unitDiscToExpStrip θ u - exp (I * π * θ)) /
        (unitDiscToExpStrip θ u - exp (-I * π * θ)) = u := by
  have h1u : 1 - u ≠ 0 := sub_ne_zero.2 hu.symm
  have hdiff : unitDiscToExpStrip θ u - exp (-I * π * θ) =
      (exp (I * π * θ) - exp (-I * π * θ)) / (1 - u) := by
    rw [unitDiscToExpStrip, div_sub' h1u]; congr 1; ring
  have hnum : unitDiscToExpStrip θ u - exp (I * π * θ) =
      u * (exp (I * π * θ) - exp (-I * π * θ)) / (1 - u) := by
    rw [unitDiscToExpStrip, div_sub' h1u]; congr 1; ring
  have hden_ne : unitDiscToExpStrip θ u - exp (-I * π * θ) ≠ 0 := by
    rw [hdiff]
    exact div_ne_zero (exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ) h1u
  refine ⟨hden_ne, ?_⟩
  rw [hnum, hdiff, div_div_div_cancel_right₀ h1u,
    mul_div_cancel_right₀ u (exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ)]

private theorem unitDiscToExpStrip_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    unitDiscToExpStrip θ (stripToUnitDisc θ z) = exp (I * π * z) :=
  (stripToUnitDisc_cayley hθ (sub_exp_neg_I_pi_ne_zero hθ (im_exp_nonneg_of_mem hz))).2

/-- The inverse conformal map `w ↦ log ((exp (i π θ) - w exp (-i π θ)) / (1 - w)) / (i π)`
sending `ball 0 1` onto `verticalStrip 0 1` for `0 < θ < 1`. -/
def unitDiscToStrip (θ : ℝ) (w : ℂ) : ℂ :=
  Complex.log ((exp (I * π * θ) - w * exp (-I * π * θ)) / (1 - w)) / (I * π)

/-- Explicit formula for `unitDiscToStrip`. -/
theorem unitDiscToStrip_def (θ : ℝ) (w : ℂ) : unitDiscToStrip θ w =
    Complex.log ((exp (I * π * θ) - w * exp (-I * π * θ)) / (1 - w)) / (I * π) := (rfl)

private theorem im_unitDiscToExpStrip_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ}
    (hw : w ∈ ball 0 1) : 0 < (unitDiscToExpStrip θ w).im := by
  have hu_lt : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have h1u : 1 - w ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [← h] at hu_lt
  have hnormSq : normSq w < 1 := by
    rw [normSq_eq_norm_sq, sq_lt_one_iff₀ (norm_nonneg _)]; exact hu_lt
  rw [im_unitDiscToExpStrip]
  exact div_pos (mul_pos (sub_pos.2 hnormSq) (sin_pi_mul_pos hθ)) (normSq_pos.2 h1u)

/-- For `0 < θ < 1`, `unitDiscToStrip θ` is complex-differentiable at every point of `ball 0 1`. -/
theorem differentiableAt_unitDiscToStrip {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ}
    (hw : w ∈ ball 0 1) : DifferentiableAt ℂ (unitDiscToStrip θ) w := by
  have hw1 : (1 - w : ℂ) ≠ 0 := sub_ne_zero.2 fun h ↦ by
    have := mem_ball_zero_iff.1 hw; simp [← h] at this
  have hlog : DifferentiableAt ℂ Complex.log (unitDiscToExpStrip θ w) :=
    Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.2 (Or.inr (im_unitDiscToExpStrip_pos hθ hw).ne'))
  have hnum : DifferentiableAt ℂ (fun u ↦ (exp (I * π * θ) - u * exp (-I * π * θ)) / (1 - u)) w :=
    ((differentiableAt_const _).sub (differentiableAt_id.mul_const _)).div
      ((differentiableAt_const _).sub differentiableAt_id) hw1
  exact (hlog.comp w hnum).div_const (I * π)

/-- `unitDiscToStrip θ` is complex-differentiable on the open unit disc `ball 0 1`. -/
theorem differentiableOn_unitDiscToStrip {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    DifferentiableOn ℂ (unitDiscToStrip θ) (ball 0 1) :=
  fun _ hw ↦ (differentiableAt_unitDiscToStrip hθ hw).differentiableWithinAt

/-- For `0 < θ < 1`, `unitDiscToStrip θ` maps `ball 0 1` into `verticalStrip 0 1`. -/
theorem unitDiscToStrip_mem_verticalStrip {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ}
    (hw : w ∈ ball 0 1) : unitDiscToStrip θ w ∈ verticalStrip 0 1 := by
  have hw_im := im_unitDiscToExpStrip_pos hθ hw
  have harg_pos : 0 < (unitDiscToExpStrip θ w).arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hw_im.le) fun h ↦
      hw_im.ne' (Complex.arg_eq_zero_iff.1 h.symm).2
  have harg_lt : (unitDiscToExpStrip θ w).arg < π :=
    Complex.arg_lt_pi_iff.2 (Or.inr hw_im.ne')
  have hz_re : (unitDiscToStrip θ w).re = (unitDiscToExpStrip θ w).arg / π := by
    rw [unitDiscToStrip_def, div_eq_mul_inv, mul_inv, Complex.inv_I, ← ofReal_inv]
    simp [unitDiscToExpStrip, Complex.log_im, div_eq_mul_inv]
  exact mem_verticalStrip_iff.2 (hz_re ▸ ⟨div_pos harg_pos pi_pos, (div_lt_one pi_pos).2 harg_lt⟩)

/-- `unitDiscToStrip θ` is a right inverse of `stripToUnitDisc θ` on `ball 0 1`. -/
@[simp]
theorem stripToUnitDisc_unitDiscToStrip {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ}
    (hw : w ∈ ball 0 1) : stripToUnitDisc θ (unitDiscToStrip θ w) = w := by
  have hw1 : w ≠ 1 := fun h ↦ by have := mem_ball_zero_iff.1 hw; simp [h] at this
  have hw_ne : unitDiscToExpStrip θ w ≠ 0 := fun h ↦ by
    have := im_unitDiscToExpStrip_pos hθ hw; simp [h] at this
  have hexp : exp (I * π * unitDiscToStrip θ w) = unitDiscToExpStrip θ w := by
    change exp (I * π * (Complex.log (unitDiscToExpStrip θ w) / (I * π))) = unitDiscToExpStrip θ w
    rw [mul_div_cancel₀ _ (mul_ne_zero I_ne_zero (ofReal_ne_zero.2 pi_pos.ne')),
      Complex.exp_log hw_ne]
  rw [stripToUnitDisc, hexp]
  exact (stripToUnitDisc_cayley_symm hθ hw1).2

private theorem im_I_pi_mul_mem_Ioo {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    -π < (I * π * z).im ∧ (I * π * z).im ≤ π := by
  have hz' := mem_verticalStrip_iff.1 hz
  have him : (I * π * z).im = π * z.re := by simp [mul_assoc]
  exact ⟨by nlinarith [pi_pos, hz'.1], by nlinarith [pi_pos, hz'.2]⟩

/-- `unitDiscToStrip θ` is a left inverse of `stripToUnitDisc θ` on `verticalStrip 0 1`. -/
@[simp]
theorem unitDiscToStrip_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : unitDiscToStrip θ (stripToUnitDisc θ z) = z := by
  have him := im_I_pi_mul_mem_Ioo hz
  change Complex.log (unitDiscToExpStrip θ (stripToUnitDisc θ z)) / (I * π) = z
  rw [unitDiscToExpStrip_stripToUnitDisc hθ (verticalStrip_subset_verticalClosedStrip 0 1 hz),
    Complex.log_exp him.1 him.2,
    mul_div_cancel_left₀ _ (mul_ne_zero I_ne_zero (ofReal_ne_zero.2 pi_pos.ne'))]

/-- For `0 < θ < 1`, `stripToUnitDisc θ` is injective on `verticalStrip 0 1`. -/
theorem injOn_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    InjOn (stripToUnitDisc θ) (verticalStrip 0 1) := by
  intro z₁ hz₁ z₂ hz₂ h
  have him₁ := im_I_pi_mul_mem_Ioo hz₁
  have him₂ := im_I_pi_mul_mem_Ioo hz₂
  have hexp : exp (I * π * z₁) = exp (I * π * z₂) := by
    rw [← unitDiscToExpStrip_stripToUnitDisc hθ (verticalStrip_subset_verticalClosedStrip 0 1 hz₁),
      ← unitDiscToExpStrip_stripToUnitDisc hθ (verticalStrip_subset_verticalClosedStrip 0 1 hz₂), h]
  exact mul_left_cancel₀ (mul_ne_zero I_ne_zero (ofReal_ne_zero.2 pi_pos.ne'))
    (Complex.exp_inj_of_neg_pi_lt_of_le_pi him₁.1 him₁.2 him₂.1 him₂.2 hexp)

/-- For `0 < θ < 1`, `stripToUnitDisc θ` maps `verticalStrip 0 1` onto `ball 0 1`. -/
theorem surjOn_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    SurjOn (stripToUnitDisc θ) (verticalStrip 0 1) (ball 0 1) :=
  fun u hu ↦ ⟨unitDiscToStrip θ u, unitDiscToStrip_mem_verticalStrip hθ hu,
    stripToUnitDisc_unitDiscToStrip hθ hu⟩

/-- For `0 < θ < 1`, `stripToUnitDisc θ` maps `verticalStrip 0 1` bijectively onto `ball 0 1`. -/
theorem bijOn_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    BijOn (stripToUnitDisc θ) (verticalStrip 0 1) (ball 0 1) :=
  ⟨fun _ hz ↦ stripToUnitDisc_mem_ball hθ hz, injOn_stripToUnitDisc hθ,
    surjOn_stripToUnitDisc hθ⟩

private theorem cayley_ofReal {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (r : ℝ) :
    ((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ)) ≠ 1 ∧
      (unitDiscToExpStrip θ (((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ)))).re =
        r := by
  have h := stripToUnitDisc_cayley hθ (sub_exp_neg_I_pi_ne_zero hθ (by simp : 0 ≤ (r : ℂ).im))
  exact ⟨h.1, by rw [h.2, ofReal_re]⟩

private theorem abs_re_unitDiscToExpStrip_of_mem_sphere (θ : ℝ) {w : ℂ} (hw : w ∈ sphere 0 1) :
    |(unitDiscToExpStrip θ w).re| = ‖unitDiscToExpStrip θ w‖ := by
  have hnormSq : normSq w = 1 := by
    rw [normSq_eq_norm_sq, mem_sphere_zero_iff_norm.1 hw, one_pow]
  have him : (unitDiscToExpStrip θ w).im = 0 := by
    rw [im_unitDiscToExpStrip, hnormSq, sub_self, zero_mul, zero_div]
  rw [← Complex.re_add_im (unitDiscToExpStrip θ w), him]; simp

private def glueBoundary {α : Type*} (θ : ℝ) (cBot cTop : α) (u₀ u₁ : ℝ → α) (w : ℂ) : α :=
  let x := (unitDiscToExpStrip θ w).re
  if w = 1 then cBot else if x = 0 then cTop
  else if 0 < x then u₀ (-Real.log x / π) else u₁ (-Real.log (-x) / π)

private theorem glueBoundary_stripToUnitDisc_mul_I {α : Type*} {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (cBot cTop : α) (u₀ u₁ : ℝ → α) (t : ℝ) :
    glueBoundary θ cBot cTop u₀ u₁ (stripToUnitDisc θ (t * I)) = u₀ t := by
  obtain ⟨hne1, hx⟩ := cayley_ofReal hθ (Real.exp (-π * t))
  rw [stripToUnitDisc_def, exp_I_mul_pi_mul_I]
  simp only [glueBoundary, hx, hne1, (Real.exp_pos _).ne', ↓reduceIte, Real.exp_pos, Real.log_exp]
  congr 1; field_simp [pi_pos.ne']

private theorem glueBoundary_stripToUnitDisc_one_add_mul_I {α : Type*} {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (cBot cTop : α) (u₀ u₁ : ℝ → α) (t : ℝ) :
    glueBoundary θ cBot cTop u₀ u₁ (stripToUnitDisc θ (1 + t * I)) = u₁ t := by
  obtain ⟨hne1, hx⟩ := cayley_ofReal hθ (-Real.exp (-π * t))
  have hneg : -Real.exp (-π * t) < 0 := neg_lt_zero.2 (Real.exp_pos _)
  rw [stripToUnitDisc_def, exp_I_mul_pi_one_add_mul_I, ← ofReal_neg]
  simp only [glueBoundary, hx, hne1, hneg.ne, ↓reduceIte, not_lt.2 hneg.le, neg_neg, Real.log_exp]
  congr 1; field_simp [pi_pos.ne']

private theorem glueBoundary_mem_of_ne {α : Type*} {θ : ℝ} {cBot cTop : α} {u₀ u₁ : ℝ → α}
    {s : Set α} {w : ℂ} (hw : w ≠ 1) (hx : (unitDiscToExpStrip θ w).re ≠ 0)
    (h₀ : u₀ (-Real.log |(unitDiscToExpStrip θ w).re| / π) ∈ s)
    (h₁ : u₁ (-Real.log |(unitDiscToExpStrip θ w).re| / π) ∈ s) :
    glueBoundary θ cBot cTop u₀ u₁ w ∈ s := by
  simp only [glueBoundary, hw, hx, ↓reduceIte]
  split_ifs with hpos
  · rwa [abs_of_pos hpos] at h₀
  · rwa [abs_of_neg (lt_of_le_of_ne (not_lt.1 hpos) hx)] at h₁

private theorem continuousWithinAt_glueBoundary_one {α : Type*} [TopologicalSpace α]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {cBot cTop : α} {u₀ u₁ : ℝ → α}
    (hu₀ : Tendsto u₀ atBot (𝓝 cBot)) (hu₁ : Tendsto u₁ atBot (𝓝 cBot)) :
    ContinuousWithinAt (glueBoundary θ cBot cTop u₀ u₁) (sphere 0 1) 1 := by
  rw [ContinuousWithinAt, Filter.tendsto_iff_forall_eventually_mem]
  simp only [glueBoundary, ↓reduceIte]
  intro s hs
  obtain ⟨T, hT⟩ := Filter.mem_atBot_sets.1 ((hu₀.eventually hs).and (hu₁.eventually hs))
  set B := max 1 (Real.exp (-π * T))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hpos : 0 < ‖exp (I * π * θ) - (1 : ℂ) * exp (-I * π * θ)‖ := by
    simpa using norm_pos_iff.2 (exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (((by fun_prop : Continuous fun w : ℂ ↦ ‖exp (I * π * θ) - w * exp (-I * π * θ)‖).tendsto
        1).eventually_const_lt (half_lt_self hpos)),
    eventually_nhdsWithin_of_eventually_nhds
      (((by fun_prop : Continuous fun w : ℂ ↦ ‖(1 : ℂ) - w‖).tendsto 1).eventually_lt_const
        (by simp only [sub_self, norm_zero]; exact div_pos (half_pos hpos) hB))] with w hw hnum hden
  by_cases hw1 : w = 1
  · simpa [hw1] using mem_of_mem_nhds hs
  have hgt : B < |(unitDiscToExpStrip θ w).re| := by
    rw [abs_re_unitDiscToExpStrip_of_mem_sphere θ hw, unitDiscToExpStrip, norm_div,
      lt_div_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw1)))]
    linarith [(lt_div_iff₀ hB).1 hden]
  have hlog : -Real.log |(unitDiscToExpStrip θ w).re| / π ≤ T := by
    have hle := Real.log_exp (-π * T) ▸ Real.log_le_log (Real.exp_pos _)
      ((le_max_right 1 _).trans hgt.le)
    rw [div_le_iff₀ pi_pos]; linarith
  exact glueBoundary_mem_of_ne hw1 (abs_pos.1 (hB.trans hgt)) (hT _ hlog).1 (hT _ hlog).2

private theorem continuousOn_glueBoundary {α : Type*} [TopologicalSpace α]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {cBot cTop : α} {u₀ u₁ : ℝ → α}
    (hu₀c : Continuous u₀) (hu₁c : Continuous u₁)
    (hu₀_bot : Tendsto u₀ atBot (𝓝 cBot)) (hu₁_bot : Tendsto u₁ atBot (𝓝 cBot))
    (hu₀_top : Tendsto u₀ atTop (𝓝 cTop)) (hu₁_top : Tendsto u₁ atTop (𝓝 cTop)) :
    ContinuousOn (glueBoundary θ cBot cTop u₀ u₁) (sphere 0 1) := by
  intro w₀ _
  by_cases hw₀1 : w₀ = 1
  · exact hw₀1 ▸ continuousWithinAt_glueBoundary_one hθ hu₀_bot hu₁_bot
  have hcx : ContinuousAt (fun w ↦ (unitDiscToExpStrip θ w).re) w₀ :=
    Complex.continuous_re.continuousAt.comp
      ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).div
        (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm hw₀1)))
  rcases lt_trichotomy ((unitDiscToExpStrip θ w₀).re) 0 with hneg | hzero | hpos
  · refine ((hu₁c.continuousAt.comp (f := fun w ↦ -Real.log (-(unitDiscToExpStrip θ w).re) / π)
      (((Real.continuousAt_log (neg_pos.2 hneg).ne').comp
        (f := fun w ↦ -(unitDiscToExpStrip θ w).re) hcx.neg).neg.div_const π)).congr_of_eventuallyEq
      ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_lt_const hneg] with w hw1 hlt
    simp [glueBoundary, hw1, hlt.ne, not_lt.2 hlt.le]
  · refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Filter.tendsto_iff_forall_eventually_mem]
    simp only [glueBoundary, hw₀1, hzero, ↓reduceIte]
    intro s hs
    obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.1 ((hu₀_top.eventually hs).and (hu₁_top.eventually hs))
    filter_upwards [eventually_ne_nhds hw₀1,
      (continuous_abs.continuousAt.comp hcx).eventually_lt_const
        (by simp [hzero, Real.exp_pos] : |(unitDiscToExpStrip θ w₀).re| < Real.exp (-π * T))]
      with w hw1 hw
    by_cases hx : (unitDiscToExpStrip θ w).re = 0
    · simpa [hw1, hx] using mem_of_mem_nhds hs
    have hlog : T ≤ -Real.log |(unitDiscToExpStrip θ w).re| / π := by
      have hle := Real.log_exp (-π * T) ▸ Real.log_le_log (abs_pos.2 hx) hw.le
      rw [le_div_iff₀ pi_pos]; linarith
    exact glueBoundary_mem_of_ne hw1 hx (hT _ hlog).1 (hT _ hlog).2
  · refine ((hu₀c.continuousAt.comp (f := fun w ↦ -Real.log ((unitDiscToExpStrip θ w).re) / π)
      (((Real.continuousAt_log hpos.ne').comp (f := fun w ↦ (unitDiscToExpStrip θ w).re)
        hcx).neg.div_const π)).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_const_lt hpos] with w hw1 hgt
    simp [glueBoundary, hw1, hgt.ne', hgt]

/-- Given continuous functions `u₀, u₁ : ℝ → α` on the two boundary lines of the strip that share
common limits at `-∞` and at `+∞`, there exists `ψ : ℂ → α` continuous on `sphere 0 1` whose
pullbacks along `t ↦ stripToUnitDisc θ (t * I)` and `t ↦ stripToUnitDisc θ (1 + t * I)` are `u₀`
and `u₁`. -/
theorem exists_continuousOn_sphere_comp_stripToUnitDisc {α : Type*} [TopologicalSpace α]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {cBot cTop : α} {u₀ u₁ : ℝ → α}
    (hu₀ : Continuous u₀) (hu₁ : Continuous u₁)
    (hu₀_bot : Tendsto u₀ atBot (𝓝 cBot)) (hu₁_bot : Tendsto u₁ atBot (𝓝 cBot))
    (hu₀_top : Tendsto u₀ atTop (𝓝 cTop)) (hu₁_top : Tendsto u₁ atTop (𝓝 cTop)) :
    ∃ ψ : ℂ → α, ContinuousOn ψ (sphere 0 1) ∧
      (∀ t : ℝ, ψ (stripToUnitDisc θ (t * I)) = u₀ t) ∧
      ∀ t : ℝ, ψ (stripToUnitDisc θ (1 + t * I)) = u₁ t :=
  ⟨glueBoundary θ cBot cTop u₀ u₁,
    continuousOn_glueBoundary hθ hu₀ hu₁ hu₀_bot hu₁_bot hu₀_top hu₁_top,
    glueBoundary_stripToUnitDisc_mul_I hθ cBot cTop u₀ u₁,
    glueBoundary_stripToUnitDisc_one_add_mul_I hθ cBot cTop u₀ u₁⟩

end TauCeti

end
