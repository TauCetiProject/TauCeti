/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Owen's T function

This file defines Owen's T function
`T(h, a) = (2π)⁻¹ * ∫ t in 0..a, exp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)`
and develops its real-variable theory: joint continuity and measurability, evenness in `h`,
oddness in `a`, the value `T(0, a) = arctan a / (2π)`, the derivative in `a`, and the bound
`|T(h, a)| ≤ |a| * exp (-h ^ 2 / 2) / (2π)`, which gives the limits `T(h, a) → 0` as `h → ±∞`.

Owen's T function arises in bivariate Gaussian probabilities and expresses the cumulative
distribution function of the standard skew-normal law with shape `α` as `Φ(x) - 2 * T(x, α)`,
where `Φ` is the standard Gaussian cdf. The derivative in `h`, which involves the standard Gaussian
density and cdf, and the skew-normal identities are in
`TauCeti.Probability.Distributions.Gaussian.OwensT`.

## Main declarations

* `Real.owensT` — Owen's T function.
* `Real.continuous_owensT` and `Real.measurable_owensT` — joint continuity and measurability.
* `Real.owensT_neg_left` and `Real.owensT_neg_right` — evenness in `h` and oddness in `a`.
* `Real.owensT_zero_left` — `T(0, a) = arctan a / (2π)`.
* `Real.hasDerivAt_intervalIntegral_owensT` — differentiation in the first argument under the
  integral defining Owen's T function.
* `Real.hasDerivAt_owensT_right` — the derivative in `a`.
* `Real.abs_owensT_le`, `Real.tendsto_owensT_atTop` and `Real.tendsto_owensT_atBot` — the
  Gaussian bound and the limits in `h`.

## References

* D. B. Owen, *Tables for computing bivariate normal probabilities*, Annals of Mathematical
  Statistics 27 (1956), 1075–1090.
* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Real

private theorem abs_owensT_integrand_le (h t : ℝ) :
    |rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)| ≤ rexp (-h ^ 2 / 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  calc rexp (-h ^ 2 * (1 + t ^ 2) / 2) ≤ rexp (-h ^ 2 / 2) :=
        exp_le_exp.2 <| by nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg t)]
    _ ≤ rexp (-h ^ 2 / 2) * (1 + t ^ 2) :=
        le_mul_of_one_le_right (exp_pos _).le (by nlinarith [sq_nonneg t])

/-- **Owen's T function**,
`T(h, a) = (2π)⁻¹ * ∫ t in 0..a, exp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)`.

The integral is oriented, so `T(h, a)` has the sign of `a`. -/
def owensT (h a : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..a, rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)

theorem owensT_def (h a : ℝ) :
    owensT h a = (2 * π)⁻¹ * ∫ t in (0 : ℝ)..a, rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
  (rfl)

/-- The derivative in `h` of the integral defining Owen's T function is
`∫ t in 0..a, -h * exp (-h ^ 2 * (1 + t ^ 2) / 2)`. -/
theorem hasDerivAt_intervalIntegral_owensT (h a : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..a, rexp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
      (∫ t in (0 : ℝ)..a, -h * rexp (-h ^ 2 * (1 + t ^ 2) / 2)) h := by
  have hFc (x : ℝ) : Continuous fun t : ℝ => rexp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun _ => by positivity
  -- Near `h`, the derivative of the integrand is dominated by the constant `|h| + 1`.
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => rexp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
    (F' := fun x t => -x * rexp (-x ^ 2 * (1 + t ^ 2) / 2))
    (bound := fun _ => |h| + 1) (Metric.ball_mem_nhds h one_pos)
    (Eventually.of_forall fun x => (hFc x).aestronglyMeasurable) ((hFc h).intervalIntegrable _ _)
    (by fun_prop :
      Continuous fun t : ℝ => -h * rexp (-h ^ 2 * (1 + t ^ 2) / 2)).aestronglyMeasurable
    (ae_of_all _ fun t _ x hx => ?_) intervalIntegrable_const (ae_of_all _ fun t _ x _ => ?_)).2
  · have hx' : |x| ≤ |h| + 1 := by
      have := abs_sub_abs_le_abs_sub x h
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hx
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (exp_pos _)]
    refine (mul_le_of_le_one_right (abs_nonneg x) (exp_le_one_iff.2 ?_)).trans hx'
    have : 0 ≤ x ^ 2 * (1 + t ^ 2) := by positivity
    linarith
  · have hpos : (1 + t ^ 2) ≠ 0 := by positivity
    convert (((hasDerivAt_pow 2 x).neg.mul_const (1 + t ^ 2)).div_const 2).exp.div_const
      (1 + t ^ 2) using 1
    simp only [Pi.neg_apply]
    field_simp
    ring

/-- Owen's T function is jointly continuous. -/
theorem continuous_owensT : Continuous fun p : ℝ × ℝ => owensT p.1 p.2 := by
  have hint : Continuous fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..p.2, rexp (-p.1 ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (t : ℝ) => rexp (-p.1 ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
      (Continuous.div (by fun_prop) (by fun_prop) fun q => by positivity) continuous_snd
  exact ((continuous_const (y := (2 * π)⁻¹)).mul hint).congr fun p => (owensT_def p.1 p.2).symm

@[fun_prop]
theorem _root_.Continuous.owensT {α : Type*} [TopologicalSpace α] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => Real.owensT (f x) (g x) :=
  continuous_owensT.comp (hf.prodMk hg)

/-- Owen's T function is jointly measurable. -/
theorem measurable_owensT : Measurable fun p : ℝ × ℝ => owensT p.1 p.2 :=
  continuous_owensT.measurable

@[fun_prop]
theorem _root_.Measurable.owensT {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => Real.owensT (f x) (g x) :=
  (measurable_owensT.comp (hf.prodMk hg) :)

/-- Owen's T function is even in `h`. -/
@[simp]
theorem owensT_neg_left (h a : ℝ) : owensT (-h) a = owensT h a := by
  simp [owensT_def]

/-- Owen's T function is odd in `a`. -/
@[simp]
theorem owensT_neg_right (h a : ℝ) : owensT h (-a) = -owensT h a := by
  have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := a)
    fun t => rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)
  simp only [even_two, Even.neg_pow, neg_zero] at hcomp
  rw [owensT_def, owensT_def, intervalIntegral.integral_symm (-a) 0, ← hcomp, mul_neg]

@[simp]
theorem owensT_zero_right (h : ℝ) : owensT h 0 = 0 := by
  simp [owensT_def]

/-- At `h = 0` Owen's T function is `arctan a / (2π)`. -/
@[simp]
theorem owensT_zero_left (a : ℝ) : owensT 0 a = arctan a / (2 * π) := by
  simp [owensT_def, integral_inv_one_add_sq, div_eq_inv_mul]

/-- The derivative of Owen's T function in its second argument is
`exp (-h ^ 2 * (1 + a ^ 2) / 2) / (2π * (1 + a ^ 2))`. -/
theorem hasDerivAt_owensT_right (h a : ℝ) :
    HasDerivAt (owensT h) (rexp (-h ^ 2 * (1 + a ^ 2) / 2) / (2 * π * (1 + a ^ 2))) a := by
  have hcont : Continuous fun t : ℝ => rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun _ => by positivity
  convert ((hcont.integral_hasStrictDerivAt 0 a).hasDerivAt).const_mul (2 * π)⁻¹ using 1
  · funext u
    exact owensT_def h u
  · field_simp

/-- Owen's T function is bounded by `|a| * exp (-h ^ 2 / 2) / (2π)`. -/
theorem abs_owensT_le (h a : ℝ) : |owensT h a| ≤ |a| * rexp (-h ^ 2 / 2) / (2 * π) := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a)
    (f := fun t => rexp (-h ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
    fun t _ => (Real.norm_eq_abs _).trans_le (abs_owensT_integrand_le h t)
  rw [Real.norm_eq_abs, sub_zero] at hint
  rw [owensT_def, abs_mul, abs_of_pos (by positivity), inv_mul_eq_div, mul_comm |a|]
  have := pi_pos
  gcongr

/-- Owen's T function tends to `0` as `h → ∞`. -/
theorem tendsto_owensT_atTop (a : ℝ) : Tendsto (fun h => owensT h a) atTop (𝓝 0) := by
  have hsq : Tendsto (fun h : ℝ => h ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have hexp : Tendsto (fun h : ℝ => rexp (-h ^ 2 / 2)) atTop (𝓝 0) :=
    (tendsto_exp_neg_atTop_nhds_zero.comp hsq).congr fun h => by simp [neg_div]
  have hbound : Tendsto (fun h : ℝ => |a| * rexp (-h ^ 2 / 2) / (2 * π)) atTop (𝓝 0) := by
    simpa using (hexp.const_mul |a|).div_const (2 * π)
  exact squeeze_zero_norm (fun h => abs_owensT_le h a) hbound

/-- Owen's T function tends to `0` as `h → -∞`. -/
theorem tendsto_owensT_atBot (a : ℝ) : Tendsto (fun h => owensT h a) atBot (𝓝 0) :=
  ((tendsto_owensT_atTop a).comp tendsto_neg_atBot_atTop).congr fun h => owensT_neg_left h a

end Real
