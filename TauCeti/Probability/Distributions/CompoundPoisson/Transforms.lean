/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Moments.ConvolutionPower
import TauCeti.Probability.Distributions.Mixture

/-!
# Exponential moments of compound Poisson laws

For a measurable additive real observable `f`, a compound Poisson law of positive rate has
exactly the exponential-integrability domain of its jump law. On that domain its mgf is
`exp (r * (mgf f μ t - 1))` and its cgf is `r * (mgf f μ t - 1)`.
At rate zero the domain is all of `ℝ`, independently of the jump law.
The results hold for arbitrary s-finite jump measures, without normalization.

The observable formulation includes scalar jumps and linear projections of vector jumps.
The formulas follow the Poisson-mixture construction; see W. Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. I, Chapter XII, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal MeasureTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [AddMonoid α] [MeasurableAdd₂ α]
  {μ : Measure α} [SFinite μ] {f : α →+ ℝ}

/-- Every exponential moment of a jump law remains finite under Poisson compounding, for
any measurable additive real observable. -/
theorem integrable_exp_mul_compoundPoissonMeasure (r : ℝ≥0) (hf : Measurable f) {t : ℝ}
    (ht : Integrable (fun x ↦ exp (t * f x)) μ) :
    Integrable (fun x ↦ exp (t * f x)) (compoundPoissonMeasure r μ) := by
  have hpow (n : ℕ) : Integrable (fun x ↦ exp (t * f x)) (μ.convolutionPower n) := by
    induction n with
    | zero =>
        rw [Measure.convolutionPower_zero]
        exact integrable_dirac' (by fun_prop) (by simp)
    | succ n ih =>
        rw [Measure.convolutionPower_succ, Measure.conv,
          integrable_map_measure (by fun_prop) (by fun_prop)]
        simpa only [Function.comp_def, map_add, mul_add, exp_add] using ih.mul_prod ht
  rw [compoundPoissonMeasure_def, Measure.integrable_bind_iff Measurable.of_discrete
    (by fun_prop)]
  refine ⟨ae_of_all _ hpow, ?_⟩
  simp_rw [Real.norm_of_nonneg (exp_pos _).le]
  have hM (n : ℕ) : ∫ x, exp (t * f x) ∂μ.convolutionPower n = mgf f μ t ^ n :=
    μ.mgf_addMonoidHom_convolutionPower f hf n t
  simp_rw [hM]
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_of_nonneg (pow_nonneg mgf_nonneg _)] using
    (hasSum_pow_poissonMeasure r (mgf f μ t)).summable

/-- At positive rate, exponential integrability under a compound Poisson law is equivalent
to exponential integrability under its jump law. -/
theorem integrable_exp_mul_compoundPoissonMeasure_iff {r : ℝ≥0} (hr : r ≠ 0)
    (hf : Measurable f) (t : ℝ) :
    Integrable (fun x ↦ exp (t * f x)) (compoundPoissonMeasure r μ) ↔
      Integrable (fun x ↦ exp (t * f x)) μ := by
  refine ⟨fun h ↦ ?_, integrable_exp_mul_compoundPoissonMeasure r hf⟩
  rw [compoundPoissonMeasure_def, Measure.integrable_bind_iff Measurable.of_discrete
    (by fun_prop)] at h
  -- A positive Poisson intensity assigns positive mass to the one-jump event.
  have hone := (ae_iff_of_countable.mp h.1) 1
    (ENNReal.toReal_pos_iff.mp
      (poissonMeasure_real_singleton_pos 1 (pos_iff_ne_zero.mpr hr))).1.ne'
  simpa only [Measure.convolutionPower_one] using hone

/-- The exact exponential-integrability domain of a compound Poisson law is that of its
jump law at positive rate, and all real rates at zero intensity. -/
@[simp]
theorem integrableExpSet_compoundPoissonMeasure (r : ℝ≥0) (hf : Measurable f) :
    integrableExpSet f (compoundPoissonMeasure r μ) =
      if r = 0 then univ else integrableExpSet f μ := by
  by_cases hr : r = 0
  · subst r
    ext t
    simp only [compoundPoissonMeasure_zero, ite_true, integrableExpSet, mem_ofPred_eq,
      mem_univ, iff_true]
    exact integrable_dirac' (by fun_prop) (by simp)
  · ext t
    simpa only [ite_eq_right hr, integrableExpSet, mem_ofPred_eq] using
      integrable_exp_mul_compoundPoissonMeasure_iff hr hf t

/-- On the compound Poisson exponential-integrability domain, Poisson compounding exponentiates the
single-jump mgf minus one. -/
theorem mgf_compoundPoissonMeasure (r : ℝ≥0) (hf : Measurable f) {t : ℝ}
    (ht : t ∈ integrableExpSet f (compoundPoissonMeasure r μ)) :
    mgf f (compoundPoissonMeasure r μ) t = exp (r * (mgf f μ t - 1)) := by
  rw [compoundPoissonMeasure_def] at ht ⊢
  rw [Measure.mgf_bind _ Measurable.of_discrete.aemeasurable f t ht]
  simp_rw [μ.mgf_addMonoidHom_convolutionPower f hf]
  simpa only [pgf_def, id_eq] using pgf_poissonMeasure r (mgf f μ t)

/-- On the compound Poisson exponential-integrability domain, its cgf is its intensity times
the single-jump mgf minus one. -/
theorem cgf_compoundPoissonMeasure (r : ℝ≥0) (hf : Measurable f) {t : ℝ}
    (ht : t ∈ integrableExpSet f (compoundPoissonMeasure r μ)) :
    cgf f (compoundPoissonMeasure r μ) t = r * (mgf f μ t - 1) := by
  rw [cgf, mgf_compoundPoissonMeasure r hf ht, log_exp]

end TauCeti.Probability
