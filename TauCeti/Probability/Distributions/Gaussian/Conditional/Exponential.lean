/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.CondExp
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration

/-!
# Gaussian exponential moments with a random known coefficient

If a Gaussian variable `Y` is independent of a sigma algebra `m`, a bounded
`m`-measurable coefficient `a` may be frozen when computing its exponential moment.
The results include an integrable `m`-measurable multiplier `X`. They give the one-step
normalization and moment estimates for exponential likelihoods with predictable grid heights.

The conditional computation uses `TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`
(the independence lemma). No Gaussian law is asserted for the product `a * Y`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X a Y : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} {K : ℝ}

/-- The centered Gaussian exponential normalized by half its variance has mean one. -/
theorem integral_exp_mul_sub_gaussianReal (b : ℝ) (v : ℝ≥0) :
    ∫ y, exp (b * y - (v : ℝ) * b ^ 2 / 2) ∂gaussianReal 0 v = 1 := by
  simp_rw [exp_sub, integral_div]
  have h : (∫ y, exp (b * y) ∂gaussianReal 0 v) = exp ((v : ℝ) * b ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) b
  rw [h, div_self (ne_of_gt (exp_pos _))]

/-- A bounded known coefficient in a Gaussian exponential can be multiplied by any
integrable known variable without losing integrability. -/
theorem integrable_mul_exp_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P) (hXi : Integrable X P)
    (haK : ∀ᵐ ω ∂P, |a ω| ≤ K) :
    Integrable (fun ω ↦ X ω * exp (a ω * Y ω)) P := by
  have hYi : Integrable (fun ω ↦ exp (K * |Y ω|)) P :=
    integrable_exp_mul_abs
      (hlaw.integrable_comp (integrable_exp_mul_gaussianReal K))
      (hlaw.integrable_comp (integrable_exp_mul_gaussianReal (-K)))
  have hXY : IndepFun X Y P := (indep_of_indep_of_le_right hind hX.comap_le).symm
  have hi := (hXY.comp (by fun_prop : Measurable fun x : ℝ ↦ |x|)
    (by fun_prop : Measurable fun y : ℝ ↦ exp (K * |y|))).integrable_mul hXi.abs hYi
  refine hi.mono' (by exact ((hX.mono hm le_rfl).mul
    (((ha.mono hm le_rfl).mul hY).exp)).aestronglyMeasurable) ?_
  filter_upwards [haK] with ω hω
  simp only [norm_mul, Real.norm_eq_abs, abs_exp, Pi.mul_apply, Function.comp_apply]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply exp_le_exp.mpr
  exact (le_abs_self (a ω * Y ω)).trans (by
    simpa [abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (Y ω)))

/-- **Conditional Gaussian exponential moment with a known multiplier.** Both the
coefficient and the multiplier are measurable in the conditioning sigma algebra, whereas
`Y` is independent of it, with mean `μ` and variance `v`. The coefficient need only be
bounded almost everywhere. -/
theorem condExp_mul_exp_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P) (hXi : Integrable X P)
    (haK : ∀ᵐ ω ∂P, |a ω| ≤ K) :
    P[fun ω ↦ X ω * exp (a ω * Y ω) | m] =ᵐ[P]
      fun ω ↦ X ω * exp (μ * a ω + (v : ℝ) * a ω ^ 2 / 2) := by
  have := hlaw.isProbabilityMeasure
  have h := condExp_comp_prodMk_ae_eq_integral_of_indep hm (hX.prodMk ha) hY hind
    (f := fun z : (ℝ × ℝ) × ℝ ↦ z.1.1 * exp (z.1.2 * z.2))
    (by fun_prop) (integrable_mul_exp_of_indep_gaussian hm hX ha hY hind hlaw hXi haK)
  have hi (b : ℝ) : ∫ y, exp (b * y) ∂gaussianReal μ v =
      exp (μ * b + (v : ℝ) * b ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) b
  simpa only [hlaw.map_eq, integral_const_mul, hi] using h

end TauCeti.Probability
