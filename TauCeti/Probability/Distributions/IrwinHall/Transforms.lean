/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Basic
import TauCeti.Probability.Moments.ConvolutionPower
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-!
# Moments and transforms of Irwin–Hall distributions

An Irwin–Hall variable of order `n` has mean `n / 2` and variance `n / 12`. Its bounded carrier
gives every natural and exponential moment. The moment-generating and characteristic functions
are the `n`th powers of the unit-uniform transforms; their apparent singularities at zero are
removable, with value one. All results include the empty-sum law at order zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- Every exponential moment of an Irwin–Hall law exists. -/
@[simp]
theorem integrableExpSet_id_irwinHallMeasure (n : ℕ) :
    integrableExpSet id (irwinHallMeasure n) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_univ, iff_true]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_irwinHallMeasure n)

/-- Every natural moment of an Irwin–Hall law is integrable. -/
@[simp]
theorem integrable_pow_irwinHallMeasure (n k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (irwinHallMeasure n) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id)
  simp

/-- The mean of an Irwin–Hall law is half its order. -/
@[simp]
theorem integral_id_irwinHallMeasure (n : ℕ) :
    ∫ x, x ∂irwinHallMeasure n = (n : ℝ) / 2 := by
  rw [← Fintype.card_fin n, ← map_sum_pi_uniformMeasure_zero_one,
    integral_map (by fun_prop) (by fun_prop)]
  have hint : Integrable id (uniformMeasure 0 1) := by
    apply integrable_of_mem_interior_integrableExpSet
    simp
  have hcoord (i : Fin n) : Integrable (fun x : Fin n → ℝ ↦ x i)
      (Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1) := integrable_eval hint
  rw [integral_finsetSum _ (fun i _ ↦ hcoord i)]
  simp [integral_eval, integral_id_uniformMeasure zero_lt_one, div_eq_mul_inv]

/-- The variance of an Irwin–Hall law is its order divided by twelve. -/
@[simp]
theorem variance_id_irwinHallMeasure (n : ℕ) :
    Var[id; irwinHallMeasure n] = (n : ℝ) / 12 := by
  rw [← Fintype.card_fin n, ← map_sum_pi_uniformMeasure_zero_one,
    variance_map aemeasurable_id (by fun_prop), Function.id_comp]
  have hLp : MemLp id 2 (uniformMeasure 0 1) := by
    apply memLp_of_mem_interior_integrableExpSet
    simp
  have hsum : (fun x : Fin n → ℝ ↦ ∑ i, x i) =
      ∑ i, fun x : Fin n → ℝ ↦ id (x i) := by
    ext x
    simp
  rw [hsum, variance_sum_pi (fun _ ↦ hLp)]
  simp [variance_id_uniformMeasure zero_lt_one, div_eq_mul_inv]

/-- Away from zero, the Irwin–Hall mgf is `((exp t - 1) / t) ^ n`.
At zero it is one by the probability-measure mgf identity. -/
@[simp]
theorem mgf_id_irwinHallMeasure (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    mgf id (irwinHallMeasure n) t = ((exp t - 1) / t) ^ n := by
  have hpower := (uniformMeasure 0 1).mgf_addMonoidHom_convolutionPower
    (AddMonoidHom.id ℝ) measurable_id n t
  simpa [irwinHallMeasure_def, mgf_id_uniformMeasure zero_lt_one ht] using hpower

/-- The Irwin–Hall cgf is `n * log ((exp t - 1) / t)` away from zero.
At zero the probability-measure cgf identity gives zero. -/
@[simp]
theorem cgf_id_irwinHallMeasure (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    cgf id (irwinHallMeasure n) t = n * log ((exp t - 1) / t) := by
  rw [cgf, mgf_id_irwinHallMeasure n ht, log_pow]

/-- Away from zero, the characteristic function is the `n`th power of the unit-uniform
characteristic function. At zero it is one. -/
@[simp]
theorem charFun_irwinHallMeasure (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    charFun (irwinHallMeasure n) t =
      ((Complex.exp (Complex.I * t) - 1) / (Complex.I * t)) ^ n := by
  rw [irwinHallMeasure_def, Measure.charFun_convolutionPower]
  simp [charFun_uniformMeasure zero_lt_one ht]

end TauCeti.Probability
