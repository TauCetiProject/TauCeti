/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Random variables with a log-normal law

This file transfers the elementary carrier, moment, and exponential-transform theory of the
log-normal measure to random variables carrying that law. The moment formulas include arbitrary
real powers and the singular zero-log-variance boundary. The exact exponential-integrability
domain distinguishes that Dirac boundary from the nondegenerate log-normal laws.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on log-normal distributions.
-/

public section

noncomputable section

open MeasureTheory

open scoped NNReal

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
  {m : ℝ} {v : ℝ≥0}

/-- A random variable with a log-normal law is almost surely positive, including at zero
log-variance. -/
theorem ae_pos_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) :
    ∀ᵐ ω ∂P, 0 < X ω :=
  (hX.ae_iff measurableSet_Ioi.mem).2
    (TauCeti.Probability.ae_pos_logNormalMeasure m v)

/-- Every real power of a log-normal random variable is integrable. -/
theorem integrable_rpow_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) (q : ℝ) :
    Integrable (fun ω ↦ X ω ^ q) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_rpow_logNormalMeasure m v q)

/-- The real-power moments of a log-normal random variable. The formula includes negative powers
and the zero-log-variance boundary. -/
theorem integral_rpow_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) (q : ℝ) :
    ∫ ω, X ω ^ q ∂P = Real.exp (q * m + q ^ 2 * (v : ℝ) / 2) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ q), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_rpow_logNormalMeasure]

/-- Every natural power of a log-normal random variable is integrable. -/
theorem integrable_pow_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_logNormalMeasure m v n)

/-- The natural raw moments of a log-normal random variable. -/
theorem integral_pow_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P =
      Real.exp ((n : ℝ) * m + (n : ℝ) ^ 2 * (v : ℝ) / 2) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_logNormalMeasure]

/-- The expectation of a log-normal random variable. -/
theorem integral_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) :
    ∫ ω, X ω ∂P = Real.exp (m + (v : ℝ) / 2) := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_logNormalMeasure]

/-- The variance of a log-normal random variable. -/
theorem variance_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) :
    variance X P = (Real.exp (v : ℝ) - 1) * Real.exp (2 * m + (v : ℝ)) := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_logNormalMeasure]

/-- An exponential moment of a log-normal random variable is finite exactly when the
log-variance is zero or the exponential rate is nonpositive. -/
theorem integrable_exp_mul_logNormalMeasure_iff
    (hX : HasLaw X (logNormalMeasure m v) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔ v = 0 ∨ t ≤ 0 := by
  have htransport : Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔
      Integrable (fun x : ℝ ↦ Real.exp (t * x)) (logNormalMeasure m v) := by
    rw [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
    rfl
  rw [htransport]
  by_cases hv : v = 0
  · subst v
    simp only [true_or]
    exact iff_true_intro (by
      rw [logNormalMeasure_zero_var]
      exact integrable_dirac (by simp))
  · simp only [hv, false_or]
    exact ⟨fun hint ↦ not_lt.mp fun ht ↦
      TauCeti.Probability.not_integrable_exp_mul_logNormalMeasure m hv ht hint,
      TauCeti.Probability.integrable_exp_mul_logNormalMeasure m v⟩

/-- The exact exponential-integrability domain of a log-normal random variable. It is all of
`ℝ` at zero log-variance and the nonpositive half-line otherwise. -/
theorem integrableExpSet_logNormalMeasure (hX : HasLaw X (logNormalMeasure m v) P) :
    integrableExpSet X P = if v = 0 then Set.univ else Set.Iic 0 := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq,
    hX.integrable_exp_mul_logNormalMeasure_iff]
  by_cases hv : v = 0 <;> simp [hv]

/-- The moment-generating function of a zero-log-variance log-normal random variable. -/
theorem mgf_logNormalMeasure_zero_var
    (hX : HasLaw X (logNormalMeasure m 0) P) (t : ℝ) :
    mgf X P t = Real.exp (t * Real.exp m) := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_logNormalMeasure_zero_var]

/-- The cumulant-generating function of a zero-log-variance log-normal random variable. -/
theorem cgf_logNormalMeasure_zero_var
    (hX : HasLaw X (logNormalMeasure m 0) P) (t : ℝ) :
    cgf X P t = t * Real.exp m := by
  rw [cgf, hX.mgf_logNormalMeasure_zero_var, Real.log_exp]

/-- The characteristic function of the image law of a zero-log-variance log-normal random
variable. -/
theorem charFun_map_logNormalMeasure_zero_var
    (hX : HasLaw X (logNormalMeasure m 0) P) (t : ℝ) :
    charFun (P.map X) t = Complex.exp (Complex.I * (t : ℂ) * Real.exp m) := by
  rw [hX.map_eq, TauCeti.Probability.charFun_logNormalMeasure_zero_var]

end ProbabilityTheory.HasLaw
