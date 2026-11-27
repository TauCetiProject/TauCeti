/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Stein.Solution
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Stein solution of the identity

For `h(x) = x` the mean `∫ h dγ` under the standard normal law is `0`, and
`∫_{t ≤ w} t e^{-t²/2} dt = -e^{-w²/2}`, so the Stein solution is the constant `-1`. The Stein
equation then reads `0 - w · (-1) = w`, and the bound `|f_h| ≤ K` for `K`-Lipschitz `h` is attained
with `K = 1`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

public section

namespace TauCeti.Examples.SteinSolution

/-- The Stein solution of the identity is the constant `-1`. -/
theorem steinSolution_id : TauCeti.Probability.steinSolution (fun x => x) = fun _ => -1 := by
  ext w
  have hderiv : ∀ t, HasDerivAt (fun t : ℝ => -exp (-(t ^ 2 / 2))) (t * exp (-(t ^ 2 / 2))) t :=
    fun t => by
      convert (TauCeti.hasDerivAt_exp_neg_sq_div_two t).fun_neg using 1
      ring
  have hint : Integrable fun t : ℝ => t * exp (-(t ^ 2 / 2)) := by
    refine (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).congr
      (ae_of_all _ fun t => ?_)
    simp only
    ring_nf
  have hlim : Tendsto (fun t : ℝ => -exp (-(t ^ 2 / 2))) atBot (𝓝 (-0)) := by
    refine (tendsto_exp_atBot.comp ?_).neg
    refine tendsto_neg_atTop_atBot.comp ?_
    exact (tendsto_pow_atTop two_ne_zero |>.comp tendsto_neg_atBot_atTop |>.congr fun t => by
      simp).atTop_div_const two_pos
  have hI := integral_Iic_of_hasDerivAt_of_tendsto (a := w)
    (hderiv w).continuousAt.continuousWithinAt (fun t _ => hderiv t) hint.integrableOn hlim
  rw [TauCeti.Probability.steinSolution_def, integral_id_gaussianReal]
  simp only [sub_zero, hI, neg_zero]
  rw [mul_neg, exp_neg, mul_inv_cancel₀ (exp_ne_zero _)]

end TauCeti.Examples.SteinSolution
