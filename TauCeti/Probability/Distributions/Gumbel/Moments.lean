/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic

import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Logistic.Gumbel
import TauCeti.Probability.Distributions.Logistic.Moments

/-!
# Moments of the Gumbel distribution

For a positive-scale Gumbel law, the identity belongs to every finite `Lᵖ`, its mean is the
location plus the scale times the Euler--Mascheroni constant, and its variance is `π²s² / 6`.

Integrability follows directly from the exponential pushforward construction.  The mean
uses the classical logarithmic integral for the Euler--Mascheroni constant.  For the variance,
the difference of two independent identically distributed Gumbel variables is logistic, so its
variance is twice the Gumbel variance.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), ch. 21.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {m s : ℝ}

private lemma memLp_gumbel_source (p : ℝ≥0) :
    MemLp (fun e : ℝ => m - s * log e) p (expMeasure 1) := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  exact (memLp_const m).sub ((memLp_log_expMeasure one_pos p).const_mul s)

/-- The identity belongs to every finite `Lᵖ` under every Gumbel law, including the zero measure
at a nonpositive scale. -/
theorem memLp_id_gumbelMeasure (m s : ℝ) (p : ℝ≥0) : MemLp id p (gumbelMeasure m s) := by
  by_cases hs : 0 < s
  · rw [gumbelMeasure_of_pos hs,
      memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    refine (memLp_gumbel_source (m := m) (s := s) p).congr_norm (by fun_prop) ?_
    filter_upwards with e
    simp only [Function.comp_apply, id_eq]
  · simp [gumbelMeasure_of_nonpos (le_of_not_gt hs)]

/-- The mean of a positive-scale Gumbel law is `m + s * γ`, where `γ` is the
Euler--Mascheroni constant. -/
@[simp]
theorem integral_id_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    ∫ x, x ∂gumbelMeasure m s = m + s * Real.eulerMascheroniConstant := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [gumbelMeasure_of_pos hs, integral_map (by fun_prop) (by fun_prop),
    integral_sub (integrable_const m) ((integrable_log_expMeasure one_pos).const_mul s),
    integral_const, integral_const_mul, integral_log_expMeasure one_pos]
  simp

/-- The variance of a positive-scale Gumbel law is `π²s² / 6`. -/
@[simp]
theorem variance_id_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    variance id (gumbelMeasure m s) = π ^ 2 * s ^ 2 / 6 := by
  let μ := gumbelMeasure m s
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_gumbelMeasure hs m
  have hmem : MemLp id 2 μ := memLp_id_gumbelMeasure m s 2
  have hfst : MemLp (fun z : ℝ × ℝ => z.1) 2 (μ.prod μ) := hmem.comp_fst μ
  have hsnd : MemLp (fun z : ℝ × ℝ => z.2) 2 (μ.prod μ) := hmem.comp_snd μ
  have hindep : IndepFun (fun z : ℝ × ℝ => z.1) (fun z : ℝ × ℝ => z.2) (μ.prod μ) :=
    indepFun_prod₀ hmem.aemeasurable hmem.aemeasurable
  have hlogistic :
      variance id (logisticMeasure 0 s) = 2 * variance id μ := by
    calc
      variance id (logisticMeasure 0 s) =
          variance id ((μ.prod μ).map fun z : ℝ × ℝ => z.1 - z.2) := by
            rw [map_sub_prod_gumbelMeasure hs m m, sub_self]
      _ = variance (fun z : ℝ × ℝ => z.1 - z.2) (μ.prod μ) :=
        variance_id_map (by fun_prop)
      _ = variance (fun z : ℝ × ℝ => z.1) (μ.prod μ) +
          variance (fun z : ℝ × ℝ => z.2) (μ.prod μ) := by
            rw [variance_fun_sub hfst hsnd, hindep.covariance_eq_zero hfst hsnd]
            ring
      _ = variance id μ + variance id μ := by
        simpa only [Function.comp_apply, id_eq] using
          congrArg₂ (· + ·)
            ((measurePreserving_fst (μ := μ) (ν := μ)).variance_fun_comp
              (f := id) aemeasurable_id)
            ((measurePreserving_snd (μ := μ) (ν := μ)).variance_fun_comp
              (f := id) aemeasurable_id)
      _ = 2 * variance id μ := by ring
  rw [variance_id_logisticMeasure hs] at hlogistic
  linarith

end TauCeti.Probability
