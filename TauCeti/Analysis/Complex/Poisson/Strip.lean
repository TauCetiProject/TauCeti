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

For `0 < θ < 1`, the holomorphic map

`stripToUnitDisc θ z = (exp (i π z) - exp (i π θ)) / (exp (i π z) - exp (-i π θ))`

maps the open vertical strip `0 < re z < 1` into the open unit disc `ball 0 1`, sends `θ` to `0`,
and maps the boundary lines `t ↦ i t` and `t ↦ 1 + i t` bijectively onto the complementary open
arcs of `sphere 0 1` separated by `1` and `exp (2 π i θ)`. Pulling normalized arc length on the
unit circle back along the two boundary lines produces the strip Poisson kernels

* `stripPoissonKernel₀ θ t = sin (π θ) / (2 (cosh (π t) - cos (π θ)))`, of total integral `1 - θ`;
* `stripPoissonKernel₁ θ t = sin (π θ) / (2 (cosh (π t) + cos (π θ)))`, of total integral `θ`,

and their normalized probability measures `stripPoissonMeasure₀ θ` and `stripPoissonMeasure₁ θ`.

This file also proves uniform radial boundary convergence
`tendstoUniformlyOn_planarPoissonIntegral_mul` for continuous data on a circle of nonzero radius by
combining pointwise boundary convergence (`TauCeti.tendsto_planarPoissonIntegral`) with compactness
of the sphere. Combined with `circleAverage_eq_stripPoissonKernel`, this underlies Calderón's
log-convexity inequality for the complex interpolation method.

## Main declarations

* `TauCeti.stripToUnitDisc`: conformal map from `verticalStrip 0 1` to `ball 0 1` sending `θ`
  to `0`.
* `TauCeti.stripPoissonKernel₀`, `TauCeti.stripPoissonKernel₁`: Poisson kernels of the vertical
  strip `0 ≤ re z ≤ 1` evaluated at a real interior point `θ ∈ (0, 1)`.
* `TauCeti.stripPoissonMeasure₀`, `TauCeti.stripPoissonMeasure₁`: the normalized probability
  measures `(1 - θ)⁻¹ μ₀(θ, t) dt` and `θ⁻¹ μ₁(θ, t) dt` on `ℝ`.
* `TauCeti.circleAverage_eq_stripPoissonKernel`: change of variables expressing
  `circleAverage ψ 0 1` as the sum of the two boundary strip Poisson integrals.
* `TauCeti.tendstoUniformlyOn_planarPoissonIntegral_mul`: radial dilations of the planar Poisson
  integral of continuous boundary data converge uniformly on the boundary circle.

## References

* I. I. Hirschman, *A convexity theorem for certain groups of transformations*, J. Analyse Math.
  **2** (1952), 209–218.
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §9.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, §4.3 (Lemma 4.3.2).
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
theorem stripToUnitDisc_def (θ : ℝ) (z : ℂ) :
    stripToUnitDisc θ z =
      (exp (I * π * z) - exp (I * π * θ)) / (exp (I * π * z) - exp (-I * π * θ)) := by
  rfl

/-- At `z = θ`, `stripToUnitDisc θ` vanishes. -/
@[simp]
theorem stripToUnitDisc_self (θ : ℝ) : stripToUnitDisc θ θ = 0 := by
  simp [stripToUnitDisc]

private theorem im_exp_I_mul_pi_mul (z : ℂ) :
    (exp (I * π * z)).im = Real.exp (-π * z.im) * Real.sin (π * z.re) := by
  have hre : (I * π * z).re = -π * z.im := by simp [mul_assoc]
  have him : (I * π * z).im = π * z.re := by simp [mul_assoc]
  rw [Complex.exp_im, hre, him]

private theorem exp_I_mul_pi_sub_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : 0 ≤ (exp (I * π * z)).im) :
    exp (I * π * z) - exp (-I * π * θ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have hθ' : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    have : -I * ↑π * ↑θ = I * ↑π * ((-θ : ℝ) : ℂ) := by push_cast; ring
    rw [this, im_exp_I_mul_pi_mul]
    simp [Real.sin_neg]
  have hsin : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  linarith

/-- For `0 < θ < 1`, `stripToUnitDisc θ` is complex-differentiable at every point of the closed
strip `0 ≤ re z ≤ 1`. -/
theorem differentiableAt_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    DifferentiableAt ℂ (stripToUnitDisc θ) z := by
  have hz' := mem_verticalClosedStrip_iff.1 hz
  have him : 0 ≤ (exp (I * π * z)).im := by
    rw [im_exp_I_mul_pi_mul]
    exact mul_nonneg (Real.exp_nonneg _)
      (Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos, hz'.1], by nlinarith [pi_pos, hz'.2]⟩)
  unfold stripToUnitDisc
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (exp_I_mul_pi_sub_ne_zero hθ him)

/-- `stripToUnitDisc θ` is holomorphic on a neighborhood of every point of the closed strip. -/
theorem differentiableOn_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    DifferentiableOn ℂ (stripToUnitDisc θ) (verticalClosedStrip 0 1) :=
  fun _ hz ↦ (differentiableAt_stripToUnitDisc hθ hz).differentiableWithinAt

/-- `stripToUnitDisc θ` is holomorphic on `verticalStrip 0 1` and continuous on its closure. -/
theorem diffContOnCl_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    DiffContOnCl ℂ (stripToUnitDisc θ) (verticalStrip 0 1) :=
  ⟨(differentiableOn_stripToUnitDisc hθ).mono (verticalStrip_subset_verticalClosedStrip 0 1),
    (differentiableOn_stripToUnitDisc hθ).continuousOn.mono (closure_verticalStrip_subset 0 1)⟩

private theorem normSq_sub_conj_sub_normSq_sub (w ζ : ℂ) :
    normSq (w - star ζ) - normSq (w - ζ) = 4 * w.im * ζ.im := by
  simp only [RCLike.star_def, normSq_apply, sub_re, sub_im, conj_re, conj_im]
  ring

private theorem star_exp_I_mul_pi (θ : ℝ) :
    star (exp (I * π * θ)) = exp (-I * π * θ) := by
  rw [RCLike.star_def, ← exp_conj]
  congr 1
  simp

/-- On the open strip `0 < re z < 1`, `stripToUnitDisc θ` takes values in the open unit disc. -/
theorem stripToUnitDisc_mem_ball {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) :
    stripToUnitDisc θ z ∈ ball 0 1 := by
  have hz' := mem_verticalStrip_iff.1 hz
  have hwim : 0 < (exp (I * π * z)).im := by
    rw [im_exp_I_mul_pi_mul]
    exact mul_pos (Real.exp_pos _)
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hz'.1) (by nlinarith [pi_pos, hz'.2]))
  have hζim : 0 < (exp (I * π * θ)).im := by
    simpa [im_exp_I_mul_pi_mul] using
      Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  have hden : exp (I * π * z) - exp (-I * π * θ) ≠ 0 := exp_I_mul_pi_sub_ne_zero hθ hwim.le
  have hdiff := normSq_sub_conj_sub_normSq_sub (exp (I * π * z)) (exp (I * π * θ))
  rw [star_exp_I_mul_pi] at hdiff
  have hlt : normSq (exp (I * π * z) - exp (I * π * θ)) <
      normSq (exp (I * π * z) - exp (-I * π * θ)) := by nlinarith
  have hpos : 0 < normSq (exp (I * π * z) - exp (-I * π * θ)) := normSq_pos.2 hden
  rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg _), ← normSq_eq_norm_sq,
    stripToUnitDisc, map_div₀, div_lt_one hpos]
  exact hlt

/-- On the closed strip `0 ≤ re z ≤ 1`, `stripToUnitDisc θ` has norm at most `1`. -/
theorem norm_stripToUnitDisc_le_one {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖stripToUnitDisc θ z‖ ≤ 1 := by
  have hz' := mem_verticalClosedStrip_iff.1 hz
  have hwim : 0 ≤ (exp (I * π * z)).im := by
    rw [im_exp_I_mul_pi_mul]
    exact mul_nonneg (Real.exp_nonneg _)
      (Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos, hz'.1], by nlinarith [pi_pos, hz'.2]⟩)
  have hζim : 0 < (exp (I * π * θ)).im := by
    simpa [im_exp_I_mul_pi_mul] using
      Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  have hden : exp (I * π * z) - exp (-I * π * θ) ≠ 0 := exp_I_mul_pi_sub_ne_zero hθ hwim
  have hdiff := normSq_sub_conj_sub_normSq_sub (exp (I * π * z)) (exp (I * π * θ))
  rw [star_exp_I_mul_pi] at hdiff
  have hpos : 0 < normSq (exp (I * π * z) - exp (-I * π * θ)) := normSq_pos.2 hden
  rw [← sq_le_one_iff₀ (norm_nonneg _), ← normSq_eq_norm_sq, stripToUnitDisc, map_div₀,
    div_le_one hpos]
  nlinarith

private theorem exp_I_mul_pi_mul_I (t : ℝ) :
    exp (I * π * (t * I)) = (Real.exp (-π * t) : ℂ) := by
  have h : I * ↑π * (↑t * I) = ((-π * t : ℝ) : ℂ) := by
    calc I * ↑π * (↑t * I) = ↑π * ↑t * (I * I) := by ring
      _ = ((-π * t : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  rw [h, ofReal_exp]

private theorem exp_I_mul_pi_one_add_mul_I (t : ℝ) :
    exp (I * π * (1 + t * I)) = -(Real.exp (-π * t) : ℂ) := by
  have h : I * ↑π * (1 + ↑t * I) = ((-π * t : ℝ) : ℂ) + ↑π * I := by
    calc I * ↑π * (1 + ↑t * I) = ↑π * ↑t * (I * I) + ↑π * I := by ring
      _ = ((-π * t : ℝ) : ℂ) + ↑π * I := by rw [I_mul_I]; push_cast; ring
  rw [h, Complex.exp_add, exp_pi_mul_I, ofReal_exp, mul_neg_one]

/-- The left boundary line `re z = 0` maps into the unit circle. -/
theorem stripToUnitDisc_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (t * I) ∈ sphere 0 1 := by
  have him : (exp (I * π * (t * I))).im = 0 := by rw [exp_I_mul_pi_mul_I, ofReal_im]
  have hden : exp (I * π * (t * I)) - exp (-I * π * θ) ≠ 0 :=
    exp_I_mul_pi_sub_ne_zero hθ him.ge
  have hdiff := normSq_sub_conj_sub_normSq_sub (exp (I * π * (t * I))) (exp (I * π * θ))
  rw [star_exp_I_mul_pi, him, mul_zero, zero_mul, sub_eq_zero] at hdiff
  rw [mem_sphere_zero_iff_norm, Complex.norm_def, Real.sqrt_eq_one,
    stripToUnitDisc, map_div₀, div_eq_one_iff_eq (normSq_pos.2 hden).ne']
  exact hdiff.symm

/-- The right boundary line `re z = 1` maps into the unit circle. -/
theorem stripToUnitDisc_one_add_mul_I_mem_sphere {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    stripToUnitDisc θ (1 + t * I) ∈ sphere 0 1 := by
  have him : (exp (I * π * (1 + t * I))).im = 0 := by
    rw [exp_I_mul_pi_one_add_mul_I, neg_im, ofReal_im, neg_zero]
  have hden : exp (I * π * (1 + t * I)) - exp (-I * π * θ) ≠ 0 :=
    exp_I_mul_pi_sub_ne_zero hθ him.ge
  have hdiff := normSq_sub_conj_sub_normSq_sub (exp (I * π * (1 + t * I))) (exp (I * π * θ))
  rw [star_exp_I_mul_pi, him, mul_zero, zero_mul, sub_eq_zero] at hdiff
  rw [mem_sphere_zero_iff_norm, Complex.norm_def, Real.sqrt_eq_one,
    stripToUnitDisc, map_div₀, div_eq_one_iff_eq (normSq_pos.2 hden).ne']
  exact hdiff.symm

/-- Conjugation exchanges the two boundary lines of `stripToUnitDisc` under `θ ↔ 1 - θ`. -/
theorem star_stripToUnitDisc_one_sub_one_add_mul_I (θ t : ℝ) :
    star (stripToUnitDisc (1 - θ) (1 + t * I)) = stripToUnitDisc θ (t * I) := by
  have he₁ : exp (I * ↑π * ↑(1 - θ)) = -exp (-I * ↑π * ↑θ) := by
    have : I * ↑π * ↑(1 - θ) = -I * ↑π * ↑θ + ↑π * I := by push_cast; ring
    rw [this, Complex.exp_add, exp_pi_mul_I, mul_neg_one]
  have he₂ : exp (-I * ↑π * ↑(1 - θ)) = -exp (I * ↑π * ↑θ) := by
    have : -I * ↑π * ↑(1 - θ) = I * ↑π * ↑θ - ↑π * I := by push_cast; ring
    rw [this, sub_eq_add_neg, Complex.exp_add,
      show -(↑π * I) = (-1 : ℂ) * (↑π * I) by ring,
      show (-1 : ℂ) * (↑π * I) = -(↑π * I) by ring, Complex.exp_neg, exp_pi_mul_I,
      inv_neg, inv_one, mul_neg_one]
  rw [RCLike.star_def, stripToUnitDisc, stripToUnitDisc, exp_I_mul_pi_one_add_mul_I,
    exp_I_mul_pi_mul_I, he₁, he₂, map_div₀, map_sub, map_sub, map_neg, map_neg, map_neg,
    conj_ofReal, ← exp_conj, ← exp_conj]
  have hc₁ : (starRingEnd ℂ) (-I * ↑π * ↑θ) = I * ↑π * ↑θ := by simp
  have hc₂ : (starRingEnd ℂ) (I * ↑π * ↑θ) = -(I * ↑π * ↑θ) := by simp
  have hc₃ : -I * ↑π * ↑θ = -(I * ↑π * ↑θ) := by ring
  rw [hc₁, hc₂, hc₃]
  rw [show (-(Real.exp (-π * t) : ℂ) - -exp (I * ↑π * ↑θ)) =
      -((Real.exp (-π * t) : ℂ) - exp (I * ↑π * ↑θ)) by ring,
    show (-(Real.exp (-π * t) : ℂ) - -exp (-(I * ↑π * ↑θ))) =
      -((Real.exp (-π * t) : ℂ) - exp (-(I * ↑π * ↑θ))) by ring,
    neg_div_neg_eq]

/-! ### Strip Poisson kernels and probability measures -/

/-- The left-boundary Poisson kernel of the vertical strip `0 ≤ re z ≤ 1` at `z = θ ∈ (0, 1)`. -/
def stripPoissonKernel₀ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- Explicit formula for `stripPoissonKernel₀`. -/
theorem stripPoissonKernel₀_def (θ t : ℝ) :
    stripPoissonKernel₀ θ t =
      Real.sin (π * θ) / (2 * (Real.cosh (π * t) - Real.cos (π * θ))) := by
  rfl

/-- The right-boundary Poisson kernel of the vertical strip `0 ≤ re z ≤ 1` at `z = θ ∈ (0, 1)`. -/
def stripPoissonKernel₁ (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ)))

/-- Explicit formula for `stripPoissonKernel₁`. -/
theorem stripPoissonKernel₁_def (θ t : ℝ) :
    stripPoissonKernel₁ θ t =
      Real.sin (π * θ) / (2 * (Real.cosh (π * t) + Real.cos (π * θ))) := by
  rfl

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub (θ t : ℝ) :
    stripPoissonKernel₀ θ t = stripPoissonKernel₁ (1 - θ) t := by
  have h : π * (1 - θ) = π - π * θ := by ring
  rw [stripPoissonKernel₀, stripPoissonKernel₁, h, Real.sin_pi_sub, Real.cos_pi_sub]
  ring

/-- Replacing `θ` by `1 - θ` exchanges the two strip Poisson kernels. -/
theorem stripPoissonKernel₁_eq_stripPoissonKernel₀_one_sub (θ t : ℝ) :
    stripPoissonKernel₁ θ t = stripPoissonKernel₀ (1 - θ) t := by
  rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub, sub_sub_cancel]

/-- `stripPoissonKernel₀ θ` is an even function of `t`. -/
@[simp]
theorem stripPoissonKernel₀_neg (θ t : ℝ) :
    stripPoissonKernel₀ θ (-t) = stripPoissonKernel₀ θ t := by
  simp [stripPoissonKernel₀, mul_neg, Real.cosh_neg]

/-- `stripPoissonKernel₁ θ` is an even function of `t`. -/
@[simp]
theorem stripPoissonKernel₁_neg (θ t : ℝ) :
    stripPoissonKernel₁ θ (-t) = stripPoissonKernel₁ θ t := by
  simp [stripPoissonKernel₁, mul_neg, Real.cosh_neg]

private theorem cosh_add_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < Real.cosh (π * t) + Real.cos (π * θ) := by
  have hcos : -1 < Real.cos (π * θ) := by
    rw [← Real.cos_pi]
    exact Real.strictAntiOn_cos ⟨by nlinarith [pi_pos, hθ.1], by nlinarith [pi_pos, hθ.2]⟩
      ⟨pi_pos.le, le_rfl⟩ (by nlinarith [pi_pos, hθ.2])
  linarith [Real.one_le_cosh (π * t)]

/-- For `0 < θ < 1`, `stripPoissonKernel₁ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₁_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < stripPoissonKernel₁ θ t :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2]))
    (mul_pos two_pos (cosh_add_cos_pos hθ t))

/-- For `0 < θ < 1`, `stripPoissonKernel₀ θ` is strictly positive everywhere. -/
theorem stripPoissonKernel₀_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    0 < stripPoissonKernel₀ θ t := by
  rw [stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub]
  exact stripPoissonKernel₁_pos ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ t

/-- For `0 < θ < 1`, `stripPoissonKernel₁ θ` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Continuous (stripPoissonKernel₁ θ) := by
  unfold stripPoissonKernel₁
  exact continuous_const.div (by fun_prop) fun t ↦ (mul_pos two_pos (cosh_add_cos_pos hθ t)).ne'

/-- For `0 < θ < 1`, `stripPoissonKernel₀ θ` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Continuous (stripPoissonKernel₀ θ) := by
  rw [funext (stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ)]
  exact continuous_stripPoissonKernel₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-! ### Boundary angle parametrizations and total mass -/

/-- The angle in `(0, 2 π θ)` parameterizing `t ↦ stripToUnitDisc θ (1 + t * I)` on the unit
circle. -/
private def rightBoundaryAngle (θ t : ℝ) : ℝ :=
  π - 2 * Real.arctan ((Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ))

/-- The angle in `(2 π θ, 2 π)` parameterizing `t ↦ stripToUnitDisc θ (t * I)` on `sphere 0 1`. -/
private def leftBoundaryAngle (θ t : ℝ) : ℝ :=
  2 * π - rightBoundaryAngle (1 - θ) t

private theorem circleMap_pi_sub_two_arctan {a b : ℝ} (hb : b ≠ 0) :
    circleMap 0 1 (π - 2 * Real.arctan (a / b)) = ((a : ℂ) + b * I) / ((a : ℂ) - b * I) := by
  set β := Real.arctan (a / b)
  have hcos : Real.cos β ≠ 0 := (Real.cos_arctan_pos (a / b)).ne'
  have hsin : b * Real.sin β = a * Real.cos β := by
    have htan := Real.tan_arctan (a / b)
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hcos hb] at htan
    linarith
  have hden₁ : exp ((β : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hden₂ : (a : ℂ) - b * I ≠ 0 := by
    intro h
    have := congrArg Complex.im (sub_eq_zero.1 h)
    simp only [ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero] at this
    exact hb this.symm
  have hexp : circleMap 0 1 (π - 2 * β) = -exp (-(β : ℂ) * I) / exp ((β : ℂ) * I) := by
    simp only [circleMap, zero_add, ofReal_one, one_mul]
    have harg : ((π - 2 * β : ℝ) : ℂ) * I = ↑π * I + (-(β : ℂ) * I - (β : ℂ) * I) := by
      push_cast; ring
    rw [harg, Complex.exp_add, exp_pi_mul_I, Complex.exp_sub]
    ring
  rw [hexp, div_eq_div_iff hden₁ hden₂]
  have hneg : (-(β : ℂ) * I) = ((-β : ℝ) : ℂ) * I := by push_cast; ring
  rw [hneg, exp_ofReal_mul_I, exp_ofReal_mul_I]
  apply Complex.ext <;> simp [-ofReal_cos, -ofReal_sin]
  · linear_combination 2 * hsin
  · ring

private theorem circleMap_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (rightBoundaryAngle θ t) = stripToUnitDisc θ (1 + t * I) := by
  have hb : Real.sin (π * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])).ne'
  rw [rightBoundaryAngle, circleMap_pi_sub_two_arctan hb, stripToUnitDisc,
    exp_I_mul_pi_one_add_mul_I]
  have he₁ : exp (I * ↑π * ↑θ) = (Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I := by
    have : I * ↑π * ↑θ = ((π * θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I]
  have he₂ : exp (-I * ↑π * ↑θ) = (Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I := by
    have : -I * ↑π * ↑θ = ((-(π * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, ofReal_neg]
    ring
  rw [he₁, he₂]
  have hnum : ((Real.exp (-π * t) + Real.cos (π * θ) : ℝ) : ℂ) + Real.sin (π * θ) * I =
      -(-(Real.exp (-π * t) : ℂ) - ((Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I)) := by
    rw [ofReal_add]; ring
  have hden : ((Real.exp (-π * t) + Real.cos (π * θ) : ℝ) : ℂ) - Real.sin (π * θ) * I =
      -(-(Real.exp (-π * t) : ℂ) - ((Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I)) := by
    rw [ofReal_add]; ring
  rw [hnum, hden, neg_div_neg_eq]

private theorem circleMap_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    circleMap 0 1 (leftBoundaryAngle θ t) = stripToUnitDisc θ (t * I) := by
  have hθ' : 1 - θ ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩
  have hstar : circleMap 0 1 (leftBoundaryAngle θ t) =
      star (circleMap 0 1 (rightBoundaryAngle (1 - θ) t)) := by
    simp only [leftBoundaryAngle, circleMap, zero_add, ofReal_one, one_mul]
    have h : ((2 * π - rightBoundaryAngle (1 - θ) t : ℝ) : ℂ) * I =
        2 * ↑π * I + (-(rightBoundaryAngle (1 - θ) t) : ℝ) * I := by push_cast; ring
    rw [h, Complex.exp_add, exp_two_pi_mul_I, one_mul, RCLike.star_def, ← exp_conj]
    congr 1
    simp
  rw [hstar, circleMap_rightBoundaryAngle hθ', star_stripToUnitDisc_one_sub_one_add_mul_I]

private theorem hasDerivAt_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (rightBoundaryAngle θ) (2 * π * stripPoissonKernel₁ θ t) t := by
  set s := Real.sin (π * θ)
  set c := Real.cos (π * θ)
  have hs : s ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])).ne'
  have hu : HasDerivAt (fun x ↦ (Real.exp (-(π * x)) + c) / s)
      (-(Real.exp (-(π * t)) * π) / s) t := by
    simpa [neg_mul] using (((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-π))).add_const c).div_const s
  have hφ := ((Real.hasDerivAt_arctan' _).comp t hu).const_mul (-2) |>.const_add π
  refine (hφ.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
  · simp [rightBoundaryAngle, s, c, sub_eq_add_neg, neg_mul]
  · have hden : 0 < Real.cosh (π * t) + c := cosh_add_cos_pos hθ t
    have h1 : 1 + ((Real.exp (-(π * t)) + c) / s) ^ 2 ≠ 0 := by positivity
    have he : Real.exp (π * t) ≠ 0 := Real.exp_ne_zero _
    rw [stripPoissonKernel₁]
    dsimp only [s, c] at *
    field_simp [hs, hden.ne', h1]
    rw [Real.cosh_eq, Real.exp_neg, Real.sin_sq]
    field_simp [he]
    ring

private theorem hasDerivAt_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (t : ℝ) :
    HasDerivAt (leftBoundaryAngle θ) (-(2 * π * stripPoissonKernel₀ θ t)) t := by
  have hθ' : 1 - θ ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩
  have h := (hasDerivAt_const t (2 * π)).sub (hasDerivAt_rightBoundaryAngle hθ' t)
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
  have hs : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atBot atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_neg_atBot_atTop.const_mul_atTop pi_pos).congr fun t ↦ by ring)
  have hu : Tendsto (fun t ↦ (Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ))
      atBot atTop :=
    (hexp.atTop_add tendsto_const_nhds).atTop_div_const hs
  have harc : Tendsto (fun t ↦ Real.arctan ((Real.exp (-π * t) + Real.cos (π * θ)) /
      Real.sin (π * θ))) atBot (𝓝 (π / 2)) :=
    (tendsto_nhdsWithin_iff.1 Real.tendsto_arctan_atTop).1.comp hu
  have hlim := (tendsto_const_nhds (x := π)).sub (harc.const_mul 2)
  have hzero : π - 2 * (π / 2) = 0 := by ring
  rw [hzero] at hlim
  exact hlim.congr fun _ ↦ rfl

private theorem tendsto_rightBoundaryAngle_atTop {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Tendsto (rightBoundaryAngle θ) atTop (𝓝 (2 * π * θ)) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_neg_atTop_atBot.const_mul_atBot pi_pos).congr fun t ↦ by ring)
  have hcont : Continuous (fun x : ℝ ↦
      π - 2 * Real.arctan ((x + Real.cos (π * θ)) / Real.sin (π * θ))) := by fun_prop
  have hlim := (hcont.tendsto 0).comp hexp
  have hval : π - 2 * Real.arctan ((0 + Real.cos (π * θ)) / Real.sin (π * θ)) = 2 * π * θ := by
    have htan : (0 + Real.cos (π * θ)) / Real.sin (π * θ) = Real.tan (π / 2 - π * θ) := by
      rw [zero_add, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [htan, Real.arctan_tan (by nlinarith [pi_pos, hθ.2]) (by nlinarith [pi_pos, hθ.1])]
    ring
  rw [hval] at hlim
  exact hlim.congr fun _ ↦ rfl

private theorem range_rightBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (rightBoundaryAngle θ) = Ioo 0 (2 * π * θ) := by
  have hmono := strictMono_rightBoundaryAngle hθ
  have hbot := tendsto_rightBoundaryAngle_atBot hθ
  have htop := tendsto_rightBoundaryAngle_atTop hθ
  have hcont : Continuous (rightBoundaryAngle θ) := by
    unfold rightBoundaryAngle
    fun_prop
  refine Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨t, rfl⟩
    refine ⟨lt_of_le_of_lt ?_ (hmono (sub_one_lt t)), lt_of_lt_of_le (hmono (lt_add_one t)) ?_⟩
    · exact le_of_tendsto hbot (eventually_le_atBot (t - 1) |>.mono fun x hx ↦ hmono.monotone hx)
    · exact ge_of_tendsto htop (eventually_ge_atTop (t + 1) |>.mono fun x hx ↦ hmono.monotone hx)
  · exact intermediate_value_univ₂_eventually₂ hcont continuous_const
      (hbot.eventually_le_const hy.1) (htop.eventually_const_le hy.2)

private theorem range_leftBoundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    range (leftBoundaryAngle θ) = Ioo (2 * π * θ) (2 * π) := by
  have hθ' : 1 - θ ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩
  ext y
  simp only [leftBoundaryAngle, mem_range, mem_Ioo]
  constructor
  · rintro ⟨t, rfl⟩
    have ht : rightBoundaryAngle (1 - θ) t ∈ Ioo 0 (2 * π * (1 - θ)) := by
      rw [← range_rightBoundaryAngle hθ']
      exact ⟨t, rfl⟩
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro hy
    have hmem : 2 * π - y ∈ range (rightBoundaryAngle (1 - θ)) := by
      rw [range_rightBoundaryAngle hθ']
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, by linarith⟩

/-- The right-boundary strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Integrable (stripPoissonKernel₁ θ) := by
  have hint : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (rightBoundaryAngle θ '' univ) := by
    rw [image_univ, range_rightBoundaryAngle hθ]
    exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
    (fun t _ ↦ (hasDerivAt_rightBoundaryAngle hθ t).hasDerivWithinAt)
    (strictMono_rightBoundaryAngle hθ).injective.injOn, integrableOn_univ] at hint
  refine (hint.const_mul (2 * π)⁻¹).congr (Eventually.of_forall fun t ↦ ?_)
  simp only [smul_eq_mul, mul_one]
  rw [abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)),
    inv_mul_cancel_left₀ two_pi_pos.ne']

/-- The left-boundary strip Poisson kernel is integrable on `ℝ`. -/
theorem integrable_stripPoissonKernel₀ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    Integrable (stripPoissonKernel₀ θ) := by
  rw [funext (stripPoissonKernel₀_eq_stripPoissonKernel₁_one_sub θ)]
  exact integrable_stripPoissonKernel₁ ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩

/-- The right-boundary strip Poisson kernel has total integral `θ` on `ℝ`. -/
@[simp]
theorem integral_stripPoissonKernel₁ {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∫ t, stripPoissonKernel₁ θ t = θ := by
  have h := integral_image_eq_integral_abs_deriv_smul .univ
    (fun t _ ↦ (hasDerivAt_rightBoundaryAngle hθ t).hasDerivWithinAt)
    (strictMono_rightBoundaryAngle hθ).injective.injOn (fun _ : ℝ ↦ (1 : ℝ))
  have hpos (t : ℝ) : |2 * π * stripPoissonKernel₁ θ t| = 2 * π * stripPoissonKernel₁ θ t :=
    abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t))
  rw [image_univ, range_rightBoundaryAngle hθ, setIntegral_const, Real.volume_real_Ioo,
    sub_zero, max_eq_left (mul_nonneg two_pi_pos.le hθ.1.le), smul_eq_mul, mul_one,
    setIntegral_univ] at h
  simp only [hpos, smul_eq_mul, mul_one, integral_const_mul] at h
  exact mul_left_cancel₀ two_pi_pos.ne' (by linarith)

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
    IsProbabilityMeasure (stripPoissonMeasure₀ θ) := by
  refine ⟨?_⟩
  have h1 : 0 < 1 - θ := sub_pos.2 hθ.2
  rw [stripPoissonMeasure₀, withDensity_apply _ .univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_stripPoissonKernel₀ hθ).const_mul _)
      (Eventually.of_forall fun t ↦ mul_nonneg (inv_nonneg.2 h1.le)
        (stripPoissonKernel₀_pos hθ t).le),
    integral_const_mul, integral_stripPoissonKernel₀ hθ, inv_mul_cancel₀ h1.ne',
    ENNReal.ofReal_one]

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
  have h1 : 0 < 1 - θ := sub_pos.2 hθ.2
  have hm : Measurable fun t ↦ ENNReal.ofReal ((1 - θ)⁻¹ * stripPoissonKernel₀ θ t) :=
    ((continuous_stripPoissonKernel₀ hθ).const_mul _).measurable.ennreal_ofReal
  rw [stripPoissonMeasure₀, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 h1.le)
    (stripPoissonKernel₀_pos hθ _).le), mul_smul, integral_smul]

/-! ### Circle averages pulled back to the strip boundary -/

private theorem Ioo_ae_eq_union_Ioo {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (Ioo 0 (2 * π) : Set ℝ) =ᵐ[volume] Ioo 0 (2 * π * θ) ∪ Ioo (2 * π * θ) (2 * π) := by
  have hsub : Ioo 0 (2 * π * θ) ∪ Ioo (2 * π * θ) (2 * π) ⊆ Ioo 0 (2 * π) := by
    rintro x (hx | hx)
    · exact ⟨hx.1, by nlinarith [hx.2, pi_pos, hθ.2]⟩
    · exact ⟨by nlinarith [hx.1, pi_pos, hθ.1], hx.2⟩
  have hdiff : Ioo 0 (2 * π) \ (Ioo 0 (2 * π * θ) ∪ Ioo (2 * π * θ) (2 * π)) = {2 * π * θ} := by
    ext x
    simp only [Set.mem_sdiff, mem_Ioo, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx₀, hx₁⟩, hnot⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnot (Or.inl ⟨hx₀, hlt⟩)
      · exact hnot (Or.inr ⟨hgt, hx₁⟩)
    · rintro rfl
      exact ⟨⟨mul_pos two_pi_pos hθ.1, by nlinarith [pi_pos, hθ.2]⟩, by simp⟩
  rw [ae_eq_set]
  refine ⟨by rw [hdiff, Real.volume_singleton], ?_⟩
  rw [sdiff_eq_empty.2 hsub]
  exact measure_empty

/-- Circle-integrability on the unit circle is equivalent to integrability against both strip
Poisson kernels along the boundary lines of the strip. -/
theorem circleIntegrable_iff_stripPoissonKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {ψ : ℂ → E} :
    CircleIntegrable ψ 0 1 ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) ∧
        Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I))) := by
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioo_of_le two_pi_pos.le,
    integrableOn_congr_set_ae (Ioo_ae_eq_union_Ioo hθ), integrableOn_union, and_comm]
  have h₁ : IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo 0 (2 * π * θ)) ↔
      Integrable (fun t ↦ stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I))) := by
    rw [← range_rightBoundaryAngle hθ, ← image_univ,
      integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
        (fun t _ ↦ (hasDerivAt_rightBoundaryAngle hθ t).hasDerivWithinAt)
        (strictMono_rightBoundaryAngle hθ).injective.injOn, integrableOn_univ]
    have heq : (fun t ↦ |2 * π * stripPoissonKernel₁ θ t| •
        ψ (circleMap 0 1 (rightBoundaryAngle θ t))) =
        fun t ↦ (2 * π) • (stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I))) := by
      ext t
      rw [abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)),
        circleMap_rightBoundaryAngle hθ, mul_smul]
    rw [heq]
    exact integrable_smul_iff two_pi_pos.ne' _
  have h₀ : IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ)) (Ioo (2 * π * θ) (2 * π)) ↔
      Integrable (fun t ↦ stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) := by
    rw [← range_leftBoundaryAngle hθ, ← image_univ,
      integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
        (fun t _ ↦ (hasDerivAt_leftBoundaryAngle hθ t).hasDerivWithinAt)
        (strictAnti_leftBoundaryAngle hθ).injective.injOn, integrableOn_univ]
    have heq : (fun t ↦ |-(2 * π * stripPoissonKernel₀ θ t)| •
        ψ (circleMap 0 1 (leftBoundaryAngle θ t))) =
        fun t ↦ (2 * π) • (stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) := by
      ext t
      rw [abs_neg, abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₀_pos hθ t)),
        circleMap_leftBoundaryAngle hθ, mul_smul]
    rw [heq]
    exact integrable_smul_iff two_pi_pos.ne' _
  rw [h₁, h₀]

/-- **Change of variables from the unit circle to the strip boundary.** For `0 < θ < 1` and
circle-integrable data `ψ` on `sphere 0 1`, the circle average `circleAverage ψ 0 1` equals the sum
of the two boundary integrals against `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem circleAverage_eq_stripPoissonKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {ψ : ℂ → E} (hψ : CircleIntegrable ψ 0 1) :
    circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I))) +
        ∫ t, stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)) := by
  have hi : IntegrableOn (fun φ ↦ ψ (circleMap 0 1 φ))
      (Ioo 0 (2 * π * θ) ∪ Ioo (2 * π * θ) (2 * π)) := by
    rwa [← integrableOn_congr_set_ae (Ioo_ae_eq_union_Ioo hθ),
      ← intervalIntegrable_iff_integrableOn_Ioo_of_le two_pi_pos.le]
  have hdisj : Disjoint (Ioo 0 (2 * π * θ)) (Ioo (2 * π * θ) (2 * π)) :=
    disjoint_left.2 fun _ hx₁ hx₂ ↦ not_lt.2 hx₁.2.le hx₂.1
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_set (Ioo_ae_eq_union_Ioo hθ),
    setIntegral_union hdisj measurableSet_Ioo hi.left_of_union hi.right_of_union]
  have h₁ : ∫ φ in Ioo 0 (2 * π * θ), ψ (circleMap 0 1 φ) =
      (2 * π) • ∫ t, stripPoissonKernel₁ θ t • ψ (stripToUnitDisc θ (1 + t * I)) := by
    rw [← range_rightBoundaryAngle hθ, ← image_univ,
      integral_image_eq_integral_abs_deriv_smul .univ
        (fun t _ ↦ (hasDerivAt_rightBoundaryAngle hθ t).hasDerivWithinAt)
        (strictMono_rightBoundaryAngle hθ).injective.injOn, setIntegral_univ, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₁_pos hθ t)),
      circleMap_rightBoundaryAngle hθ, mul_smul]
  have h₀ : ∫ φ in Ioo (2 * π * θ) (2 * π), ψ (circleMap 0 1 φ) =
      (2 * π) • ∫ t, stripPoissonKernel₀ θ t • ψ (stripToUnitDisc θ (t * I)) := by
    rw [← range_leftBoundaryAngle hθ, ← image_univ,
      integral_image_eq_integral_abs_deriv_smul .univ
        (fun t _ ↦ (hasDerivAt_leftBoundaryAngle hθ t).hasDerivWithinAt)
        (strictAnti_leftBoundaryAngle hθ).injective.injOn, setIntegral_univ, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [abs_neg, abs_of_pos (mul_pos two_pi_pos (stripPoissonKernel₀_pos hθ t)),
      circleMap_leftBoundaryAngle hθ, mul_smul]
  rw [h₁, h₀, add_comm, ← smul_add, inv_smul_smul₀ two_pi_pos.ne']

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
  -- At each boundary point `z`, pointwise Poisson recovery and continuity hold on a small ball.
  have hloc : ∀ z : sphere c |R|, ∃ δ > 0,
      (∀ w ∈ ball c |R|, dist w z.1 < δ → dist (planarPoissonIntegral g c R w) (g z.1) < ε / 2) ∧
      (∀ ζ ∈ sphere c |R|, dist ζ z.1 < δ → dist (g ζ) (g z.1) < ε / 2) := by
    intro ⟨z, hz⟩
    obtain ⟨δ₁, hδ₁, hp'⟩ := Metric.tendsto_nhdsWithin_nhds.1
      (tendsto_planarPoissonIntegral hg hz) (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hc'⟩ := Metric.continuousWithinAt_iff.1 (hg z hz) (ε / 2) (half_pos hε)
    exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
      fun w hw hd ↦ hp' hw (hd.trans_le (min_le_left _ _)),
      fun ζ hζ hd ↦ hc' hζ (hd.trans_le (min_le_right _ _))⟩
  choose δ hδ hp hc using hloc
  obtain ⟨s, hs⟩ := (isCompact_sphere c |R|).elim_nhds_subcover'
    (fun z hz ↦ ball z (δ ⟨z, hz⟩ / 2))
    (fun z hz ↦ ball_mem_nhds z (half_pos (hδ ⟨z, hz⟩)))
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exfalso
    have hmem : c + |R| ∈ sphere c |R| := by simp
    simpa using hs hmem
  set η := s.inf' hsne fun z ↦ δ z / 2
  have hη : 0 < η := (Finset.lt_inf'_iff hsne).2 fun z _ ↦ half_pos (hδ z)
  filter_upwards [Ioo_mem_nhdsLT (max_lt zero_lt_one (sub_lt_self 1 (div_pos hη (abs_pos.2 hR))))]
    with r hr ζ hζ
  obtain ⟨z, hzs, hζz⟩ := mem_iUnion₂.1 (hs hζ)
  have hr₀ : 0 < r := (le_max_left 0 _).trans_lt hr.1
  have hr₁ : r < 1 := hr.2
  have hRpos : 0 < |R| := abs_pos.2 hR
  have hnorm : ‖ζ - c‖ = |R| := mem_sphere_iff_norm.1 hζ
  have hw_ball : c + r • (ζ - c) ∈ ball c |R| := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr₀.le, hnorm]
    nlinarith
  have hw_dist : dist (c + r • (ζ - c)) z.1 < δ z := by
    have hd₁ : dist (c + r • (ζ - c)) ζ = (1 - r) * |R| := by
      rw [dist_eq_norm, show c + r • (ζ - c) - ζ = -((1 - r) • (ζ - c)) by
        simp [Complex.real_smul]; ring,
        norm_neg, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hr₁.le), hnorm]
    have hd₂ : (1 - r) * |R| < η := by
      have : 1 - η / |R| < r := (le_max_right 0 _).trans_lt hr.1
      exact (lt_div_iff₀ hRpos).1 (by linarith)
    have hηz : η ≤ δ z / 2 := Finset.inf'_le _ hzs
    linarith [dist_triangle (c + r • (ζ - c)) ζ z.1, mem_ball.1 hζz]
  have h₁ := hp z _ hw_ball hw_dist
  have h₂ := hc z ζ hζ ((mem_ball.1 hζz).trans (half_lt_self (hδ z)))
  linarith [dist_triangle_right (g ζ) (planarPoissonIntegral g c R (c + r • (ζ - c))) (g z.1)]

end TauCeti

end
