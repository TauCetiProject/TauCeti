/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.Weighted

/-!
# Size biasing the Poisson distribution

Weighting a Poisson law by the count gives its successor pushforward multiplied by the rate.
Consequently, at positive rate its normalized size-biased law is the law of one plus the original
count. At rate zero the total weight vanishes, so the normalized weighted measure is zero.

The statements use the native natural-number carrier and `Measure.weighted`; no separate
size-biased probability structure is needed. The unnormalized identity also describes integration
of count-weighted observables, including at rate zero.

## References

* R. Arratia, L. Goldstein, and F. Kochman, *Size bias for one and all*, Probability Surveys 16
  (2019), 1–61, §2, equations (5)–(6).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

/-- Count weighting a Poisson measure gives its successor pushforward times the rate.
This unnormalized identity includes rate zero. -/
theorem withDensity_natCast_poissonMeasure (r : ℝ≥0) :
    (poissonMeasure r).withDensity (fun n : ℕ ↦ (n : ℝ≥0∞)) =
      (r : ℝ≥0∞) • (poissonMeasure r).map Nat.succ := by
  apply Measure.ext_of_singleton
  intro n
  rw [withDensity_apply _ (measurableSet_singleton n), lintegral_singleton,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) (measurableSet_singleton n)]
  cases n with
  | zero =>
    have hpre : Nat.succ ⁻¹' {0} = ∅ := by ext k; simp
    simp [hpre]
  | succ n =>
    have hpre : Nat.succ ⁻¹' {n + 1} = {n} := by ext k; simp
    rw [hpre, poissonMeasure_singleton, poissonMeasure_singleton]
    have hmass :
        ((n + 1 : ℕ) : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1)!) =
          r * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ)),
      ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
      using congrArg ENNReal.ofReal hmass

/-- The total count weight under a Poisson law is its rate, as a nonnegative extended integral. -/
@[simp]
theorem lintegral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r = r := by
  have h := congrArg (fun μ : Measure ℕ ↦ μ univ) (withDensity_natCast_poissonMeasure r)
  simpa [withDensity_apply] using h

/-- At positive rate the size-biased Poisson law is the law of one plus a Poisson count.
At rate zero its total count weight vanishes and the normalized weighted law is zero. -/
@[simp]
theorem weighted_poissonMeasure (r : ℝ≥0) :
    (poissonMeasure r).weighted (fun n : ℕ ↦ (n : ℝ≥0)) =
      if r = 0 then 0 else (poissonMeasure r).map Nat.succ := by
  by_cases hr : r = 0
  · subst r
    simp
  rw [ite_eq_right hr, Measure.weighted_def]
  simp only [ENNReal.coe_natCast, lintegral_natCast_poissonMeasure,
    withDensity_natCast_poissonMeasure, smul_smul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hr) ENNReal.coe_ne_top, one_smul]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- Adding one to a Poisson variable realizes its size-biased law at positive rate. -/
theorem succ_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ}
    {r : ℝ≥0} (hX : HasLaw X (poissonMeasure r) P) (hr : r ≠ 0) :
    HasLaw (fun ω ↦ Nat.succ (X ω))
      ((poissonMeasure r).weighted (fun n : ℕ ↦ (n : ℝ≥0))) P := by
  rw [TauCeti.Probability.weighted_poissonMeasure, ite_eq_right hr]
  exact (hasLaw_map (by fun_prop : Measurable Nat.succ).aemeasurable).comp hX

end ProbabilityTheory.HasLaw
