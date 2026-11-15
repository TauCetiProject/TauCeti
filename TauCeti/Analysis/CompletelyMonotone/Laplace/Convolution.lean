/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Laplace transforms of convolutions, dilations and translations

The Laplace transform `t ↦ ∫ e^{-tx} dμ(x)` of a measure on `ℝ≥0` turns the basic operations on
measures into operations on functions:

* the additive convolution `μ ∗ ν` goes to the pointwise product of the transforms;
* the pushforward of `μ` along the dilation `x ↦ c x` goes to the reparametrization
  `t ↦ L(c t)`;
* the pushforward of `μ` along the translation `x ↦ x + p` goes to the product with the
  exponential `t ↦ e^{-tp}`, the transform of the point mass at `p`.

Read through the predicate `TauCeti.RepresentsLaplace`, these say which finite measure represents
a product of represented functions, a rescaled one, and one multiplied by an exponential. Together
with the uniqueness of representing measures they identify the Bernstein measure of a product of
completely monotone functions as the convolution of the two Bernstein measures.

## Main declarations

* `TauCeti.laplaceTransform_conv`: the transform of `μ ∗ ν` is the product of the transforms.
* `TauCeti.laplaceTransform_map_const_mul`, `TauCeti.laplaceTransform_map_add_const`: the
  transforms of the dilated and translated measures.
* `TauCeti.RepresentsLaplace.conv`, `TauCeti.RepresentsLaplace.comp_const_mul`,
  `TauCeti.RepresentsLaplace.exp_neg_mul_mul`: the corresponding representation statements.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II
  (Wiley, 2nd ed. 1971), Chapter XIII, Section 2.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Corollary 1.6.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ## The Laplace transform of the basic measure operations -/

/-- **The Laplace transform turns convolution into multiplication.** The identity needs no
finiteness or integrability hypothesis: under the junk-value convention for non-integrable
Bochner integrals it holds for all s-finite measures and every real parameter `t`. -/
@[simp]
theorem laplaceTransform_conv (μ ν : Measure ℝ≥0) [SFinite μ] [SFinite ν] (t : ℝ) :
    laplaceTransform (μ ∗ ν) t = laplaceTransform μ t * laplaceTransform ν t := by
  simp only [laplaceTransform_apply]
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  simp only [NNReal.coe_add, mul_add, neg_add, Real.exp_add]
  exact integral_prod_mul (μ := μ) (ν := ν) (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
    (fun y : ℝ≥0 => Real.exp (-(t * (y : ℝ))))

/-- Dilating a measure by `c` reparametrizes its Laplace transform by `c`. -/
@[simp]
theorem laplaceTransform_map_const_mul (μ : Measure ℝ≥0) (c : ℝ≥0) (t : ℝ) :
    laplaceTransform (μ.map (c * ·)) t = laplaceTransform μ (c * t) := by
  rw [laplaceTransform_apply, laplaceTransform_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [NNReal.coe_mul, mul_assoc, mul_left_comm (t : ℝ)]

/-- Translating a measure by `p` multiplies its Laplace transform by the exponential
`e^{-tp}`. -/
@[simp]
theorem laplaceTransform_map_add_const (μ : Measure ℝ≥0) (p : ℝ≥0) (t : ℝ) :
    laplaceTransform (μ.map (· + p)) t = Real.exp (-(t * (p : ℝ))) * laplaceTransform μ t := by
  rw [laplaceTransform_apply, laplaceTransform_apply, integral_map (by fun_prop) (by fun_prop),
    ← integral_const_mul]
  simp only [NNReal.coe_add, mul_add, neg_add, Real.exp_add, mul_comm]

/-! ## Representing measures of products, dilations and exponential factors -/

namespace RepresentsLaplace

variable {f g : ℝ → ℝ} {μ ν : Measure ℝ≥0}

/-- **The convolution of representing measures represents the product of the functions.** -/
protected lemma conv (hf : RepresentsLaplace μ f) (hg : RepresentsLaplace ν g) :
    RepresentsLaplace (μ ∗ ν) (f * g) := by
  have := hf.isFiniteMeasure
  have := hg.isFiniteMeasure
  refine representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩
  rw [Pi.mul_apply, hf.eq_laplaceTransform ht, hg.eq_laplaceTransform ht, laplaceTransform_conv]

/-- Dilating a representing measure by `c` represents the reparametrized function
`t ↦ f (c t)`. -/
protected lemma comp_const_mul (hf : RepresentsLaplace μ f) (c : ℝ≥0) :
    RepresentsLaplace (μ.map (c * ·)) (fun t => f (c * t)) := by
  have := hf.isFiniteMeasure
  refine representsLaplace_iff.mpr ⟨Measure.isFiniteMeasure_map μ _, fun t ht => ?_⟩
  rw [laplaceTransform_map_const_mul, hf.eq_laplaceTransform (mul_nonneg c.coe_nonneg ht)]

/-- Translating a representing measure by `p` represents the function multiplied by the
exponential `t ↦ e^{-tp}`. -/
protected lemma exp_neg_mul_mul (hf : RepresentsLaplace μ f) (p : ℝ≥0) :
    RepresentsLaplace (μ.map (· + p)) (fun t => Real.exp (-(t * (p : ℝ))) * f t) := by
  have := hf.isFiniteMeasure
  refine representsLaplace_iff.mpr ⟨Measure.isFiniteMeasure_map μ _, fun t ht => ?_⟩
  rw [laplaceTransform_map_add_const, hf.eq_laplaceTransform ht]

end RepresentsLaplace

end TauCeti
