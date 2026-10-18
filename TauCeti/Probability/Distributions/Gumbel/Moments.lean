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

For a positive-scale Gumbel law, the identity belongs to `L²`, its mean is the location plus
the scale times the Euler--Mascheroni constant, and its variance is `π²s² / 6`.

Square-integrability follows directly from the exponential pushforward construction.  The mean
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

namespace TauCeti.Probability

variable {m s : ℝ}

private lemma integrable_exp_mul_gumbel_source {t : ℝ} (ht : -1 < -(t * s)) :
    Integrable (fun e : ℝ => exp (t * (m - s * log e))) (expMeasure 1) := by
  rw [expMeasure]
  have hint : Integrable (fun e : ℝ => e ^ (-(t * s))) (gammaMeasure 1 1) :=
    (integrable_rpow_gammaMeasure_iff one_pos one_pos _).2 ht
  refine (hint.const_mul (exp (t * m))).congr ?_
  filter_upwards [ae_pos_gammaMeasure 1 1] with e he
  rw [Real.rpow_def_of_pos he, ← Real.exp_add]
  congr 1
  ring

private lemma memLp_gumbel_source (hs : 0 < s) :
    MemLp (fun e : ℝ => m - s * log e) 2 (expMeasure 1) := by
  let t := (2 * s)⁻¹
  have ht : t ≠ 0 := inv_ne_zero (mul_ne_zero two_ne_zero hs.ne')
  have hpos : Integrable (fun e : ℝ => exp ((0 + t) * (m - s * log e))) (expMeasure 1) := by
    apply integrable_exp_mul_gumbel_source
    dsimp [t]
    field_simp
    linarith
  have hneg : Integrable (fun e : ℝ => exp ((0 - t) * (m - s * log e))) (expMeasure 1) := by
    apply integrable_exp_mul_gumbel_source
    dsimp [t]
    field_simp
    linarith
  have habs := integrable_pow_abs_mul_exp_of_integrable_exp_mul ht hpos hneg 2
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  simpa only [zero_mul, zero_add, exp_zero, mul_one, sq_abs] using habs

/-- The identity belongs to `L²` under every Gumbel law, including the zero measure at a
nonpositive scale. -/
theorem memLp_id_gumbelMeasure (m s : ℝ) : MemLp id 2 (gumbelMeasure m s) := by
  by_cases hs : 0 < s
  · rw [gumbelMeasure_of_pos hs,
      memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    refine (memLp_gumbel_source (m := m) hs).congr_norm (by fun_prop) ?_
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
  have hmem : MemLp id 2 μ := memLp_id_gumbelMeasure m s
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
