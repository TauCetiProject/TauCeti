/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Distributions.Exponential.Basic
import TauCeti.Probability.Distributions.Gamma.Pi
import TauCeti.Probability.Distributions.Gamma.Measurability

/-!
# Hypoexponential distributions

The hypoexponential law is the sum of finitely many independent exponential variables with
positive rates. Rates may coincide: equal rates give an Erlang law. The empty sum gives the
Dirac law at zero, and a nonpositive rate gives the zero measure.

This file constructs the law as a product-measure pushforward, proves normalization and
almost-sure positivity for nonempty families, and establishes joint parameter measurability.
The independent-sum characterization lets subsequent calculations use the exponential laws
directly, without a partial-fraction decomposition or distinct-rate assumptions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The sum of independent exponential variables with rates `r`. Invalid rates give zero;
the empty family gives the point mass at zero. Repeated rates are allowed. -/
def hypoexponentialMeasure (r : ι → ℝ) : Measure ℝ :=
  if ∀ i, 0 < r i then (Measure.pi fun i ↦ expMeasure (r i)).map (fun x ↦ ∑ i, x i)
  else 0

/-- With positive rates the hypoexponential law is the sum pushforward of the exponential
product measure. -/
theorem hypoexponentialMeasure_eq_map {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    hypoexponentialMeasure r =
      (Measure.pi fun i ↦ expMeasure (r i)).map (fun x ↦ ∑ i, x i) := by
  rw [hypoexponentialMeasure, ite_eq_left hr]

/-- A family containing a nonpositive rate defines the zero law. -/
@[simp]
theorem hypoexponentialMeasure_eq_zero_of_invalid {r : ι → ℝ} (hr : ¬ ∀ i, 0 < r i) :
    hypoexponentialMeasure r = 0 := by
  rw [hypoexponentialMeasure, ite_eq_right hr]

/-- A hypoexponential law with positive rates is a probability measure, including the
empty family. -/
theorem isProbabilityMeasure_hypoexponentialMeasure {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    IsProbabilityMeasure (hypoexponentialMeasure r) := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr]
  infer_instance

/-- The hypoexponential law of an empty family is the point mass at zero. -/
@[simp]
theorem hypoexponentialMeasure_of_isEmpty [IsEmpty ι] (r : ι → ℝ) :
    hypoexponentialMeasure r = Measure.dirac 0 := by
  rw [hypoexponentialMeasure_eq_map (fun i ↦ isEmptyElim i)]
  simp

/-- A nonempty hypoexponential sum is almost surely strictly positive. This also holds for
invalid rates, where the measure is zero. -/
theorem ae_pos_hypoexponentialMeasure [Nonempty ι] (r : ι → ℝ) :
    ∀ᵐ x ∂hypoexponentialMeasure r, 0 < x := by
  by_cases hr : ∀ i, 0 < r i
  · rw [hypoexponentialMeasure_eq_map hr]
    apply (ae_map_iff (by fun_prop) (by measurability)).2
    simpa only [expMeasure] using ae_pos_sum_pi_gammaMeasure (fun _ ↦ 1) r
  · simp [hypoexponentialMeasure_eq_zero_of_invalid hr]

/-- At a common positive rate, a nonempty hypoexponential law is the Erlang law with shape
equal to the number of summands. -/
theorem hypoexponentialMeasure_const [Nonempty ι] {r : ℝ} (hr : 0 < r) :
    hypoexponentialMeasure (fun _ : ι ↦ r) = gammaMeasure (Fintype.card ι) r := by
  rw [hypoexponentialMeasure_eq_map (fun _ ↦ hr)]
  simpa only [expMeasure, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    map_sum_pi_gammaMeasure (a := fun _ : ι ↦ (1 : ℝ)) (fun _ ↦ one_pos) hr

/-- A single positive-rate hypoexponential summand has the exponential law. -/
@[simp]
theorem hypoexponentialMeasure_of_unique [Unique ι] (r : ι → ℝ) (hr : 0 < r default) :
    hypoexponentialMeasure r = expMeasure (r default) := by
  calc
    hypoexponentialMeasure r = hypoexponentialMeasure (fun _ : ι ↦ r default) :=
      congrArg hypoexponentialMeasure (funext fun i ↦ congrArg r (Unique.eq_default i))
    _ = expMeasure (r default) := by
      simpa only [Fintype.card_unique, Nat.cast_one, expMeasure] using
        (hypoexponentialMeasure_const (ι := ι) hr)

/-- The hypoexponential family is jointly measurable in all rates, including its invalid
zero-measure branch. -/
@[fun_prop]
theorem measurable_hypoexponentialMeasure :
    Measurable (hypoexponentialMeasure : (ι → ℝ) → Measure ℝ) := by
  classical
  unfold hypoexponentialMeasure
  refine Measurable.ite (by measurability) ?_ measurable_const
  simp_rw [expMeasure, pi_gammaMeasure_eq_withDensity]
  refine (Measure.measurable_map _ (by fun_prop)).comp (measurable_withDensity ?_)
  exact Finset.measurable_prod _ fun i _ ↦
    measurable_uncurry_gammaPDF.comp (by fun_prop :
      Measurable fun p : (ι → ℝ) × (ι → ℝ) ↦ (((1 : ℝ), p.1 i), p.2 i))

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- A finite sum of independent exponential variables has the hypoexponential law with
their rates. This includes the empty sum under a probability measure. -/
theorem iIndepFun.hasLaw_sum_hypoexponentialMeasure
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} {r : ι → ℝ} (hindep : iIndepFun X P) (hr : ∀ i, 0 < r i)
    (hX : ∀ i, HasLaw (X i) (expMeasure (r i)) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (hypoexponentialMeasure r) P := by
  rw [hypoexponentialMeasure_eq_map hr]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ι → ℝ ↦ ∑ i, x i).aemeasurable).comp
    (hindep.hasLaw_pi hX)

end ProbabilityTheory
