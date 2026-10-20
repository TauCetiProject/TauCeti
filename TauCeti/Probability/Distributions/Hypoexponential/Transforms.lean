/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Basic
import TauCeti.Probability.Moments.Pi
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Transforms and moments of hypoexponential laws

The exponential-integrability domain is the intersection of the half-lines below the rates.
The moment-generating and characteristic functions factor into the exponential transforms,
and the cumulant-generating function is a sum of logarithms. These formulas hold with
repeated rates and include the empty-family Dirac law through empty products and sums.

Every natural moment is integrable. The mean and variance are respectively the sums of
the reciprocal rates and squared reciprocal rates.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {r : ι → ℝ}

/-- The exact exponential-integrability domain of a hypoexponential law consists of the
arguments strictly smaller than every rate. For an empty family it is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    integrableExpSet id (hypoexponentialMeasure r) = {t | ∀ i, t < r i} := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  have hmap : integrableExpSet id (hypoexponentialMeasure r) =
      integrableExpSet (fun x : ι → ℝ ↦ ∑ i, x i) (Measure.pi fun i ↦ expMeasure (r i)) := by
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, id_eq]
    rw [hypoexponentialMeasure_eq_map hr,
      integrable_map_measure (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
  have hpi := integrableExpSet_sum_pi (μ := fun i ↦ expMeasure (r i)) (fun _ ↦ id)
  simp only [id_eq, integrableExpSet_id_expMeasure (hr _)] at hpi
  rw [hmap, hpi]
  ext t
  simp

/-- On its exact integrability domain the hypoexponential mgf is the product of the
exponential mgfs. -/
@[simp]
theorem mgf_id_hypoexponentialMeasure (hr : ∀ i, 0 < r i) {t : ℝ}
    (ht : ∀ i, t < r i) :
    mgf id (hypoexponentialMeasure r) t = ∏ i, r i / (r i - t) := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr, mgf_id_map (by fun_prop)]
  have hprod := mgf_sum_pi (μ := fun i ↦ expMeasure (r i)) (fun _ ↦ id) t
  simp only [id_eq] at hprod
  rw [hprod]
  exact Finset.prod_congr rfl fun i _ ↦ mgf_id_expMeasure (hr i) (ht i)

/-- The hypoexponential cgf is the negative sum of `log (1 - t / r i)` on its exact domain. -/
@[simp]
theorem cgf_id_hypoexponentialMeasure (hr : ∀ i, 0 < r i) {t : ℝ}
    (ht : ∀ i, t < r i) :
    cgf id (hypoexponentialMeasure r) t = -∑ i, log (1 - t / r i) := by
  rw [cgf, mgf_id_hypoexponentialMeasure hr ht,
    log_prod (fun i _ ↦ (div_pos (hr i) (sub_pos.mpr (ht i))).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_sub_div (hr i).ne', log_div (hr i).ne' (sub_pos.mpr (ht i)).ne',
    log_div (sub_pos.mpr (ht i)).ne' (hr i).ne']
  ring

/-- The characteristic function of a hypoexponential law is the product of the exponential
characteristic functions, without a restriction on the argument. -/
@[simp]
theorem charFun_hypoexponentialMeasure (hr : ∀ i, 0 < r i) (t : ℝ) :
    charFun (hypoexponentialMeasure r) t = ∏ i, (r i : ℂ) / (r i - Complex.I * t) := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr, charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply, charFun_expMeasure (hr _) t]

private theorem zero_mem_interior_integrableExpSet (hr : ∀ i, 0 < r i) :
    0 ∈ interior (integrableExpSet id (hypoexponentialMeasure r)) := by
  rw [integrableExpSet_id_hypoexponentialMeasure hr]
  have hopen : IsOpen {t : ℝ | ∀ i, t < r i} := by
    convert
      (isOpen_iInter_of_finite fun i : ι ↦ isOpen_Iio (a := r i))
      using 1
    ext t
    simp
  simpa only [hopen.interior_eq, mem_ofPred_eq] using hr

/-- Every natural moment of a hypoexponential law is integrable. Invalid rates give the
zero measure, so integrability holds for every rate vector. -/
@[simp]
theorem integrable_pow_hypoexponentialMeasure (r : ι → ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (hypoexponentialMeasure r) := by
  by_cases hr : ∀ i, 0 < r i
  · exact integrable_pow_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet hr) n
  · simp [hypoexponentialMeasure_eq_zero_of_invalid hr]

/-- The mean of a hypoexponential law is the sum of the reciprocal rates. -/
@[simp]
theorem integral_id_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    ∫ x, x ∂hypoexponentialMeasure r = ∑ i, (r i)⁻¹ := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr, integral_map (by fun_prop) (by fun_prop)]
  have hint (i : ι) : Integrable (fun x : ι → ℝ ↦ x i)
      (Measure.pi fun i ↦ expMeasure (r i)) :=
    integrable_eval (by
      simpa only [Function.id_def, pow_one] using integrable_pow_expMeasure (hr i) 1)
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ hint i)]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [integral_eval, integral_id_expMeasure (hr i)]

/-- The variance of a hypoexponential law is the sum of the squared reciprocal rates. -/
@[simp]
theorem variance_id_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    Var[id; hypoexponentialMeasure r] = ∑ i, (r i ^ 2)⁻¹ := by
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr,
    variance_map aemeasurable_id (by fun_prop), Function.id_comp]
  have hsum : (fun x : ι → ℝ ↦ ∑ i, x i) = ∑ i, fun x : ι → ℝ ↦ id (x i) := by
    ext x
    simp
  rw [hsum, variance_sum_pi]
  · simp only [variance_id_expMeasure (hr _)]
  · intro i
    apply memLp_of_mem_interior_integrableExpSet
    simpa only [integrableExpSet_id_expMeasure (hr i), interior_Iio, mem_Iio] using hr i

end TauCeti.Probability
