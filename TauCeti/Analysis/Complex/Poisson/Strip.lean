/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Integral
public import TauCeti.Analysis.Complex.VerticalStrip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Conformal map and Poisson kernels of the vertical strip

For `0 < θ < 1`, `stripToUnitDisc θ z = (exp (i π z) - exp (i π θ)) / (exp (i π z) - exp (-i π θ))`
maps `verticalStrip 0 1` into `ball 0 1` with `θ ↦ 0` and sends `t ↦ i t` and `t ↦ 1 + i t` onto
complementary open arcs of `sphere 0 1`. Pulling normalized arc length back gives
`stripPoissonKernel₀ θ` (mass `1 - θ`), `stripPoissonKernel₁ θ` (mass `θ`), the probability
measures `stripPoissonMeasure₀ θ` and `stripPoissonMeasure₁ θ`,
`circleAverage_eq_stripPoissonKernel`, and uniform radial boundary convergence
`tendstoUniformlyOn_planarPoissonIntegral_mul`.

## Main declarations

* `TauCeti.stripToUnitDisc`, `TauCeti.stripPoissonKernel₀`, `TauCeti.stripPoissonKernel₁`,
  `TauCeti.stripPoissonMeasure₀`, `TauCeti.stripPoissonMeasure₁`.
* `TauCeti.circleAverage_eq_stripPoissonKernel` and
  `TauCeti.tendstoUniformlyOn_planarPoissonIntegral_mul`.

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
  have hre : (I * π * z).re = -π * z.im := by simp [mul_assoc]
  have him : (I * π * z).im = π * z.re := by simp [mul_assoc]
  rw [Complex.exp_im, hre, him]

private theorem im_exp_nonneg_of_mem {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    0 ≤ (exp (I * π * z)).im := by
  have hz' := mem_verticalClosedStrip_iff.1 hz
  rw [im_exp_I_mul_pi_mul]
  exact mul_nonneg (Real.exp_nonneg _)
    (Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos, hz'.1], by nlinarith [pi_pos, hz'.2]⟩)

private theorem exp_I_mul_pi_sub_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : 0 ≤ (exp (I * π * z)).im) : exp (I * π * z) - exp (-I * π * θ) ≠ 0 := fun h ↦ by
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have hθ' : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    have : -I * ↑π * ↑θ = I * ↑π * ((-θ : ℝ) : ℂ) := by push_cast; ring
    rw [this, im_exp_I_mul_pi_mul]; simp [Real.sin_neg]
  linarith [sin_pi_mul_pos hθ]

/-- For `0 < θ < 1`, `stripToUnitDisc θ` is complex-differentiable on the closed strip. -/
theorem differentiableAt_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : DifferentiableAt ℂ (stripToUnitDisc θ) z := by
  unfold stripToUnitDisc
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (exp_I_mul_pi_sub_ne_zero hθ (im_exp_nonneg_of_mem hz))

/-- `stripToUnitDisc θ` is holomorphic on a neighborhood of every point of the closed strip. -/
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
  have hstar : star (exp (I * π * θ)) = exp (-I * π * θ) := by
    rw [RCLike.star_def, ← exp_conj]; congr 1; simp
  have hdiff (w ζ : ℂ) : normSq (w - star ζ) - normSq (w - ζ) = 4 * w.im * ζ.im := by
    simp only [RCLike.star_def, normSq_apply, sub_re, sub_im, conj_re, conj_im]; ring
  rw [← hstar, hdiff, im_exp_I_mul_pi_mul, im_exp_I_mul_pi_mul]; simp

/-- On the open strip `0 < re z < 1`, `stripToUnitDisc θ` takes values in the open unit disc. -/
theorem stripToUnitDisc_mem_ball {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : stripToUnitDisc θ z ∈ ball 0 1 := by
  have hz' := mem_verticalStrip_iff.1 hz
  have hwim : 0 < (exp (I * π * z)).im := by
    rw [im_exp_I_mul_pi_mul]
    exact mul_pos (Real.exp_pos _)
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hz'.1) (by nlinarith [pi_pos, hz'.2]))
  rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg _), ← normSq_eq_norm_sq, stripToUnitDisc,
    map_div₀, div_lt_one (normSq_pos.2 (exp_I_mul_pi_sub_ne_zero hθ hwim.le))]
  nlinarith [normSq_exp_sub_neg_sub_normSq θ z, sin_pi_mul_pos hθ]

/-- On the closed strip `0 ≤ re z ≤ 1`, `stripToUnitDisc θ` has norm at most `1`. -/
theorem norm_stripToUnitDisc_le_one {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖stripToUnitDisc θ z‖ ≤ 1 := by
  have hwim := im_exp_nonneg_of_mem hz
  rw [← sq_le_one_iff₀ (norm_nonneg _), ← normSq_eq_norm_sq, stripToUnitDisc, map_div₀,
    div_le_one (normSq_pos.2 (exp_I_mul_pi_sub_ne_zero hθ hwim))]
  nlinarith [normSq_exp_sub_neg_sub_normSq θ z, sin_pi_mul_pos hθ]

private theorem exp_I_mul_pi_mul_I (t : ℝ) : exp (I * π * (t * I)) = Real.exp (-π * t) := by
  have h : I * ↑π * (↑t * I) = ((-π * t : ℝ) : ℂ) := by
    push_cast; linear_combination (π * t : ℂ) * I_mul_I
  rw [h, ofReal_exp]

private theorem exp_I_mul_pi_one_add_mul_I (t : ℝ) :
    exp (I * π * (1 + t * I)) = -(Real.exp (-π * t) : ℂ) := by
  have h : I * ↑π * (1 + ↑t * I) = ((-π * t : ℝ) : ℂ) + ↑π * I := by
    push_cast; linear_combination (π * t : ℂ) * I_mul_I
  rw [h, Complex.exp_add, exp_pi_mul_I, ofReal_exp, mul_neg_one]

/-- Conjugation exchanges the two boundary lines of `stripToUnitDisc` under `θ ↔ 1 - θ`. -/
theorem star_stripToUnitDisc_one_sub_one_add_mul_I (θ t : ℝ) :
    star (stripToUnitDisc (1 - θ) (1 + t * I)) = stripToUnitDisc θ (t * I) := by
  have he₁ : star (exp (I * ↑π * ↑(1 - θ))) = -exp (I * ↑π * ↑θ) := by
    have : I * ↑π * ↑(1 - θ) = -I * ↑π * ↑θ + ↑π * I := by push_cast; ring
    rw [this, Complex.exp_add, exp_pi_mul_I, mul_neg_one, star_neg, RCLike.star_def, ← exp_conj]
    congr 2; simp
  have he₂ : star (exp (-I * ↑π * ↑(1 - θ))) = -exp (-I * ↑π * ↑θ) := by
    have : -I * ↑π * ↑(1 - θ) = -(I * ↑π * ↑(1 - θ)) := by ring
    rw [this, Complex.exp_neg, star_inv₀, he₁, inv_neg, ← Complex.exp_neg, neg_mul, neg_mul]
  rw [stripToUnitDisc, stripToUnitDisc, exp_I_mul_pi_one_add_mul_I, exp_I_mul_pi_mul_I,
    star_div₀, star_sub, star_sub, star_neg, RCLike.star_def, conj_ofReal, ← RCLike.star_def,
    he₁, he₂, ← neg_div_neg_eq]
  congr 1 <;> ring

/-- The right boundary line `re z = 1` maps into the unit circle. -/
theorem stripToUnitDisc_one_add_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (1 + t * I) ∈ sphere 0 1 := by
  have him : (exp (I * π * (1 + t * I))).im = 0 := by
    rw [exp_I_mul_pi_one_add_mul_I, neg_im, ofReal_im, neg_zero]
  have hsq := normSq_exp_sub_neg_sub_normSq θ (1 + t * I)
  rw [him, mul_zero, zero_mul] at hsq
  rw [mem_sphere_zero_iff_norm, Complex.norm_def, Real.sqrt_eq_one, stripToUnitDisc, map_div₀,
    div_eq_one_iff_eq (normSq_pos.2 (exp_I_mul_pi_sub_ne_zero hθ him.ge)).ne']
  linarith

/-- The left boundary line `re z = 0` maps into the unit circle. -/
theorem stripToUnitDisc_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (t * I) ∈ sphere 0 1 := by
  rw [← star_stripToUnitDisc_one_sub_one_add_mul_I, mem_sphere_zero_iff_norm, norm_star,
    ← mem_sphere_zero_iff_norm]
  exact stripToUnitDisc_one_add_mul_I_mem_sphere ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t

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
  have h : π * (1 - θ) = π - π * θ := by ring
  rw [stripPoissonKernel₀, stripPoissonKernel₁, h, Real.sin_pi_sub, Real.cos_pi_sub]; ring

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
    0 < Real.cosh (π * t) + Real.cos (π * θ) := by
  have hcos : -1 < Real.cos (π * θ) := by
    rw [← Real.cos_pi]
    exact Real.strictAntiOn_cos ⟨by nlinarith [pi_pos, hθ.1], by nlinarith [pi_pos, hθ.2]⟩
      ⟨pi_pos.le, le_rfl⟩ (by nlinarith [pi_pos, hθ.2])
  linarith [Real.one_le_cosh (π * t)]

/-- For `0 < θ < 1`, `stripPoissonKernel₁ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₁_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoissonKernel₁ θ t :=
  div_pos (sin_pi_mul_pos hθ) (mul_pos two_pos (cosh_add_cos_pos hθ t))

/-- For `0 < θ < 1`, `stripPoissonKernel₀ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) : 0 < stripPoissonKernel₀ θ t :=
  stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ t ▸
    stripPoissonKernel₁_pos ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t

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
    continuous_stripPoissonKernel₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-! ### Boundary angle parametrizations and total mass -/

private def rightBoundaryAngle (θ t : ℝ) : ℝ :=
  π - 2 * Real.arctan ((Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ))

private def leftBoundaryAngle (θ t : ℝ) : ℝ := 2 * π - rightBoundaryAngle (1 - θ) t

private theorem circleMap_pi_sub_two_arctan {a b : ℝ} (hb : b ≠ 0) :
    circleMap 0 1 (π - 2 * Real.arctan (a / b)) = ((a : ℂ) + b * I) / ((a : ℂ) - b * I) := by
  set β := Real.arctan (a / b)
  have hsin : b * Real.sin β = a * Real.cos β := by
    have htan := Real.tan_arctan (a / b)
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff (Real.cos_arctan_pos (a / b)).ne' hb] at htan
    linarith
  have hden₂ : (a : ℂ) - b * I ≠ 0 := fun h ↦ hb <| by
    simpa using (congrArg Complex.im (sub_eq_zero.1 h)).symm
  have hexp : circleMap 0 1 (π - 2 * β) = -exp (((-β : ℝ) : ℂ) * I) / exp ((β : ℂ) * I) := by
    simp only [circleMap, zero_add, ofReal_one, one_mul]
    have harg : ((π - 2 * β : ℝ) : ℂ) * I = ↑π * I + (((-β : ℝ) : ℂ) * I - (β : ℂ) * I) := by
      push_cast; ring
    rw [harg, Complex.exp_add, exp_pi_mul_I, Complex.exp_sub]; ring
  rw [hexp, div_eq_div_iff (Complex.exp_ne_zero _) hden₂, exp_ofReal_mul_I, exp_ofReal_mul_I]
  apply Complex.ext <;> simp [-ofReal_cos, -ofReal_sin] <;> [linear_combination 2 * hsin; ring]

private theorem circleMap_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (rightBoundaryAngle θ t) = stripToUnitDisc θ (1 + t * I) := by
  rw [rightBoundaryAngle, circleMap_pi_sub_two_arctan (sin_pi_mul_pos hθ).ne', stripToUnitDisc,
    exp_I_mul_pi_one_add_mul_I]
  have he₁ : exp (I * ↑π * ↑θ) = (Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I := by
    have : I * ↑π * ↑θ = ((π * θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I]
  have he₂ : exp (-I * ↑π * ↑θ) = (Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I := by
    have : -I * ↑π * ↑θ = ((-(π * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, ofReal_neg]; ring
  rw [he₁, he₂, ofReal_add, ← neg_div_neg_eq]
  congr 1 <;> ring

private theorem circleMap_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (leftBoundaryAngle θ t) = stripToUnitDisc θ (t * I) := by
  have hstar : circleMap 0 1 (leftBoundaryAngle θ t) =
      star (circleMap 0 1 (rightBoundaryAngle (1 - θ) t)) := by
    simp only [leftBoundaryAngle, circleMap, zero_add, ofReal_one, one_mul]
    have h : ((2 * π - rightBoundaryAngle (1 - θ) t : ℝ) : ℂ) * I =
        2 * ↑π * I + (-(rightBoundaryAngle (1 - θ) t) : ℝ) * I := by push_cast; ring
    rw [h, Complex.exp_add, exp_two_pi_mul_I, one_mul, RCLike.star_def, ← exp_conj]
    congr 1; simp
  rw [hstar, circleMap_rightBoundaryAngle ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩,
    star_stripToUnitDisc_one_sub_one_add_mul_I]

private theorem hasDerivAt_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (rightBoundaryAngle θ) (2 * π * stripPoissonKernel₁ θ t) t := by
  set s := Real.sin (π * θ); set c := Real.cos (π * θ)
  have hs : s ≠ 0 := (sin_pi_mul_pos hθ).ne'
  have hu : HasDerivAt (fun x ↦ (Real.exp (-(π * x)) + c) / s)
      (-(Real.exp (-(π * t)) * π) / s) t := by
    simpa [neg_mul] using (((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-π))).add_const c).div_const s
  have hφ := ((Real.hasDerivAt_arctan' _).comp t hu).const_mul (-2) |>.const_add π
  refine (hφ.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
  · simp [rightBoundaryAngle, s, c, sub_eq_add_neg, neg_mul]
  · have hden : 0 < Real.cosh (π * t) + c := cosh_add_cos_pos hθ t
    have h1 : 1 + ((Real.exp (-(π * t)) + c) / s) ^ 2 ≠ 0 := by positivity
    rw [stripPoissonKernel₁]; dsimp only [s, c] at *
    field_simp [hs, hden.ne', h1]
    rw [Real.cosh_eq, Real.exp_neg, Real.sin_sq]
    field_simp [Real.exp_ne_zero (π * t)]; ring

private theorem hasDerivAt_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (leftBoundaryAngle θ) (-(2 * π * stripPoissonKernel₀ θ t)) t := by
  have h := (hasDerivAt_const t (2 * π)).sub
    (hasDerivAt_rightBoundaryAngle ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t)
  rw [zero_sub, ← stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)

private theorem strictMono_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    StrictMono (rightBoundaryAngle θ) :=
  strictMono_of_deriv_pos fun t ↦ by
    rw [(hasDerivAt_rightBoundaryAngle hθ t).deriv]
    exact mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)

private theorem strictAnti_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    StrictAnti (leftBoundaryAngle θ) := fun _ _ hab ↦
  sub_lt_sub_left (strictMono_rightBoundaryAngle ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ hab) _

private theorem tendsto_rightBoundaryAngle_atBot {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Tendsto (rightBoundaryAngle θ) atBot (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atBot atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_neg_atBot_atTop.const_mul_atTop pi_pos).congr fun _ ↦ by ring)
  have hlim := (tendsto_const_nhds (x := π)).sub
    (((tendsto_nhdsWithin_iff.1 Real.tendsto_arctan_atTop).1.comp
      ((hexp.atTop_add (tendsto_const_nhds (x := Real.cos (π * θ)))).atTop_div_const
        (sin_pi_mul_pos hθ))).const_mul 2)
  exact ((by ring : π - 2 * (π / 2) = 0) ▸ hlim).congr fun _ ↦ rfl

private theorem tendsto_rightBoundaryAngle_atTop {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Tendsto (rightBoundaryAngle θ) atTop (𝓝 (2 * π * θ)) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_neg_atTop_atBot.const_mul_atBot pi_pos).congr fun _ ↦ by ring)
  have hcont : Continuous (fun x : ℝ ↦
      π - 2 * Real.arctan ((x + Real.cos (π * θ)) / Real.sin (π * θ))) := by fun_prop
  have hval : π - 2 * Real.arctan ((0 + Real.cos (π * θ)) / Real.sin (π * θ)) = 2 * π * θ := by
    rw [zero_add, ← Real.sin_pi_div_two_sub (π * θ), ← Real.cos_pi_div_two_sub (π * θ),
      ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by nlinarith [pi_pos, hθ.2])
        (by nlinarith [pi_pos, hθ.1])]
    ring
  exact (hval ▸ (hcont.tendsto 0).comp hexp).congr fun _ ↦ rfl

private theorem range_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (rightBoundaryAngle θ) = Ioo 0 (2 * π * θ) := by
  have hmono := strictMono_rightBoundaryAngle hθ
  have hbot := tendsto_rightBoundaryAngle_atBot hθ
  have htop := tendsto_rightBoundaryAngle_atTop hθ
  have hcont : Continuous (rightBoundaryAngle θ) := by unfold rightBoundaryAngle; fun_prop
  refine Subset.antisymm ?_ fun y hy ↦ intermediate_value_univ₂_eventually₂ hcont continuous_const
    (hbot.eventually_le_const hy.1) (htop.eventually_const_le hy.2)
  rintro _ ⟨t, rfl⟩
  exact ⟨lt_of_le_of_lt (le_of_tendsto hbot
      ((eventually_le_atBot (t - 1)).mono fun _ hx ↦ hmono.monotone hx)) (hmono (sub_one_lt t)),
    lt_of_lt_of_le (hmono (lt_add_one t)) (ge_of_tendsto htop
      ((eventually_ge_atTop (t + 1)).mono fun _ hx ↦ hmono.monotone hx))⟩

private theorem range_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (leftBoundaryAngle θ) = Ioo (2 * π * θ) (2 * π) := by
  have hr := range_rightBoundaryAngle (θ := 1 - θ) ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩
  ext y; simp only [leftBoundaryAngle, mem_range, mem_Ioo]
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun hy ↦ ?_⟩
  · have h : rightBoundaryAngle (1 - θ) t ∈ Ioo 0 (2 * π * (1 - θ)) := hr ▸ ⟨t, rfl⟩
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · obtain ⟨t, ht⟩ : 2 * π - y ∈ range (rightBoundaryAngle (1 - θ)) :=
      hr.symm ▸ ⟨by linarith [hy.2], by linarith [hy.1]⟩
    exact ⟨t, by linarith⟩

private theorem boundaryAngle_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g d k : ℝ → ℝ} {b : ℝ → ℂ} {s : Set ℝ} {ψ : ℂ → E}
    (hrange : range g = s) (hinj : Function.Injective g) (hd : ∀ t, HasDerivAt g (d t) t)
    (habs : ∀ t, |d t| = 2 * π * k t) (hb : ∀ t, circleMap 0 1 (g t) = b t) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) s ↔ Integrable (fun t ↦ k t • ψ (b t))) ∧
      (∫ φ in s, ψ (circleMap 0 1 φ)) = (2 * π) • ∫ t, k t • ψ (b t) := by
  have hfun : (fun t ↦ |d t| • ψ (circleMap 0 1 (g t))) = fun t ↦ (2 * π) • (k t • ψ (b t)) := by
    ext t; rw [habs, hb, mul_smul]
  constructor
  · rw [← hrange, ← image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
      (fun t _ ↦ (hd t).hasDerivWithinAt) hinj.injOn, integrableOn_univ, hfun]
    exact integrable_smul_iff two_pi_pos.ne' _
  · rw [← hrange, ← image_univ, integral_image_eq_integral_abs_deriv_smul .univ
      (fun t _ ↦ (hd t).hasDerivWithinAt) hinj.injOn, setIntegral_univ, ← integral_smul]
    exact integral_congr_ae (Eventually.of_forall (congr_fun hfun))

private theorem rightBoundary_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (ψ : ℂ → E) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo 0 (2 * π * θ)) ↔
      Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)))) ∧
      (∫ φ in Ioo 0 (2 * π * θ), ψ (circleMap 0 1 φ)) =
        (2 * π) • ∫ t, stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)) :=
  boundaryAngle_pullback (range_rightBoundaryAngle hθ)
    (strictMono_rightBoundaryAngle hθ).injective (hasDerivAt_rightBoundaryAngle hθ)
    (fun t ↦ abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)))
    (circleMap_rightBoundaryAngle hθ)

private theorem leftBoundary_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (ψ : ℂ → E) :
    (IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo (2 * π * θ) (2 * π)) ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I)))) ∧
      (∫ φ in Ioo (2 * π * θ) (2 * π), ψ (circleMap 0 1 φ)) =
        (2 * π) • ∫ t, stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I)) :=
  boundaryAngle_pullback (range_leftBoundaryAngle hθ)
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
    integrable_stripPoissonKernel₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-- The right-boundary strip Poisson kernel has total integral `θ` on `ℝ`. -/
@[simp]
theorem integral_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∫ t, stripPoissonKernel₁ θ t = θ := by
  have h := (rightBoundary_pullback hθ (fun _ ↦ (1 : ℝ))).2
  rw [setIntegral_const, Real.volume_real_Ioo, sub_zero,
    max_eq_left (mul_nonneg two_pi_pos.le hθ.1.le), smul_eq_mul, mul_one] at h
  simp only [smul_eq_mul, mul_one] at h
  exact mul_left_cancel₀ two_pi_pos.ne' h.symm

/-- The left-boundary strip Poisson kernel has total integral `1 - θ` on `ℝ`. -/
@[simp]
theorem integral_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∫ t, stripPoissonKernel₀ θ t = 1 - θ := by
  simp_rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]
  exact integral_stripPoissonKernel₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-- Normalized probability measure `(1 - θ)⁻¹ μ₀(θ, t) dt` on the left boundary of the strip. -/
def stripPoissonMeasure₀ (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal ((1 - θ)⁻¹ * stripPoissonKernel₀ θ t)

/-- Normalized probability measure `θ⁻¹ μ₁(θ, t) dt` on the right boundary of the strip. -/
def stripPoissonMeasure₁ (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal (θ⁻¹ * stripPoissonKernel₁ θ t)

private theorem stripPoissonMeasure₀_eq (θ : ℝ) :
    stripPoissonMeasure₀ θ = stripPoissonMeasure₁ (1 - θ) := by
  simp_rw [stripPoissonMeasure₀, stripPoissonMeasure₁,
    stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]

/-- For `0 < θ < 1`, `stripPoissonMeasure₁ θ` is a probability measure on `ℝ`. -/
theorem isProbabilityMeasure_stripPoissonMeasure₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    IsProbabilityMeasure (stripPoissonMeasure₁ θ) := by
  refine ⟨?_⟩
  rw [stripPoissonMeasure₁, withDensity_apply _ .univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_stripPoissonKernel₁ hθ).const_mul _)
      (Eventually.of_forall fun t ↦ mul_nonneg (inv_nonneg.2 hθ.1.le)
        (stripPoissonKernel₁_pos hθ t).le),
    integral_const_mul, integral_stripPoissonKernel₁ hθ, inv_mul_cancel₀ hθ.1.ne',
    ENNReal.ofReal_one]

/-- For `0 < θ < 1`, `stripPoissonMeasure₀ θ` is a probability measure on `ℝ`. -/
theorem isProbabilityMeasure_stripPoissonMeasure₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    IsProbabilityMeasure (stripPoissonMeasure₀ θ) :=
  stripPoissonMeasure₀_eq θ ▸
    isProbabilityMeasure_stripPoissonMeasure₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-- Bochner integration against `stripPoissonMeasure₁ θ` equals `θ⁻¹` times integration against
`stripPoissonKernel₁ θ`. -/
theorem integral_stripPoissonMeasure₁ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    ∫ t, f t ∂stripPoissonMeasure₁ θ = θ⁻¹ • ∫ t, stripPoissonKernel₁ θ t • f t := by
  have hm : Measurable fun t ↦ ENNReal.ofReal (θ⁻¹ * stripPoissonKernel₁ θ t) :=
    ((continuous_stripPoissonKernel₁ hθ).const_mul _).measurable.ennreal_ofReal
  rw [stripPoissonMeasure₁, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hθ.1.le)
    (stripPoissonKernel₁_pos hθ _).le), mul_smul, integral_smul]

/-- Bochner integration against `stripPoissonMeasure₀ θ` equals `(1 - θ)⁻¹` times integration
against `stripPoissonKernel₀ θ`. -/
theorem integral_stripPoissonMeasure₀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (f : ℝ → E) :
    ∫ t, f t ∂stripPoissonMeasure₀ θ = (1 - θ)⁻¹ • ∫ t, stripPoissonKernel₀ θ t • f t := by
  rw [stripPoissonMeasure₀_eq, integral_stripPoissonMeasure₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩]
  simp_rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]

/-! ### Circle averages pulled back to the strip boundary -/

/-- Circle-integrability on the unit circle is equivalent to integrability against both strip
Poisson kernels along the boundary lines of the strip. -/
theorem circleIntegrable_iff_stripPoissonKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {ψ : ℂ → E} :
    CircleIntegrable ψ 0 1 ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) ∧
        Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I))) := by
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le,
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
  have hψ' := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hψ
  have hi₀ : IntervalIntegrable (fun φ ↦ ψ (circleMap 0 1 φ)) volume 0 (2 * π * θ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).2 (hψ'.mono_set (Ioc_subset_Ioc_right h1))
  have hi₁ : IntervalIntegrable (fun φ ↦ ψ (circleMap 0 1 φ)) volume (2 * π * θ) (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h1).2 (hψ'.mono_set (Ioc_subset_Ioc_left h0))
  rw [circleAverage_def, ← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁,
    intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h1,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    (rightBoundary_pullback hθ ψ).2, (leftBoundary_pullback hθ ψ).2,
    add_comm, ← smul_add, inv_smul_smul₀ two_pi_pos.ne']

/-! ### Uniform radial boundary convergence of the planar Poisson integral -/

/-- Radial dilations `ζ ↦ planarPoissonIntegral g c R (c + r • (ζ - c))` of the planar Poisson
integral of continuous boundary data on a circle of nonzero radius converge uniformly on
`sphere c |R|` to `g` as `r → 1⁻`. -/
theorem tendstoUniformlyOn_planarPoissonIntegral_mul {g : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hg : ContinuousOn g (sphere c |R|)) :
    TendstoUniformlyOn (fun (r : ℝ) (ζ : ℂ) ↦ planarPoissonIntegral g c R (c + r • (ζ - c)))
      g (𝓝[<] 1) (sphere c |R|) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hloc : ∀ z : sphere c |R|, ∃ δ > 0,
      (∀ w ∈ ball c |R|, dist w z.1 < δ → dist (planarPoissonIntegral g c R w) (g z.1) < ε / 2) ∧
      (∀ ζ ∈ sphere c |R|, dist ζ z.1 < δ → dist (g ζ) (g z.1) < ε / 2) := fun ⟨z, hz⟩ ↦ by
    obtain ⟨δ₁, hδ₁, hp'⟩ := Metric.tendsto_nhdsWithin_nhds.1
      (tendsto_planarPoissonIntegral hg hz) (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hc'⟩ := Metric.continuousWithinAt_iff.1 (hg z hz) (ε / 2) (half_pos hε)
    exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
      fun w hw hd ↦ hp' hw (hd.trans_le (min_le_left _ _)),
      fun ζ hζ hd ↦ hc' hζ (hd.trans_le (min_le_right _ _))⟩
  choose δ hδ hp hc using hloc
  obtain ⟨s, hs⟩ := (isCompact_sphere c |R|).elim_nhds_subcover'
    (fun z hz ↦ ball z (δ ⟨z, hz⟩ / 2)) (fun z hz ↦ ball_mem_nhds z (half_pos (hδ ⟨z, hz⟩)))
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 fun he ↦ by
    simpa [he] using hs (by simp : c + |R| ∈ sphere c |R|)
  set η := s.inf' hsne fun z ↦ δ z / 2
  have hRpos : 0 < |R| := abs_pos.2 hR
  have hη : 0 < η := (Finset.lt_inf'_iff hsne).2 fun z _ ↦ half_pos (hδ z)
  filter_upwards [Ioo_mem_nhdsLT (max_lt zero_lt_one (sub_lt_self 1 (div_pos hη hRpos)))]
    with r hr ζ hζ
  obtain ⟨z, hzs, hζz⟩ := mem_iUnion₂.1 (hs hζ)
  have hr₀ : 0 < r := (le_max_left 0 _).trans_lt hr.1
  have hnorm : ‖ζ - c‖ = |R| := mem_sphere_iff_norm.1 hζ
  have hw_ball : c + r • (ζ - c) ∈ ball c |R| := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr₀.le, hnorm]
    nlinarith [hr.2]
  have hw_dist : dist (c + r • (ζ - c)) z.1 < δ z := by
    have hsub : c + r • (ζ - c) - ζ = -((1 - r) • (ζ - c)) := by rw [sub_smul, one_smul]; abel
    have hd₁ : dist (c + r • (ζ - c)) ζ = (1 - r) * |R| := by
      rw [dist_eq_norm, hsub, norm_neg, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.2 hr.2.le), hnorm]
    have hd₂ : (1 - r) * |R| < η :=
      (lt_div_iff₀ hRpos).1 (by linarith [(le_max_right 0 _).trans_lt hr.1])
    linarith [dist_triangle (c + r • (ζ - c)) ζ z.1, mem_ball.1 hζz,
      Finset.inf'_le (fun z : sphere c |R| ↦ δ z / 2) hzs]
  linarith [hp z _ hw_ball hw_dist,
    hc z ζ hζ ((mem_ball.1 hζz).trans (half_lt_self (hδ z))),
    dist_triangle_right (g ζ) (planarPoissonIntegral g c R (c + r • (ζ - c))) (g z.1)]

end TauCeti

end
