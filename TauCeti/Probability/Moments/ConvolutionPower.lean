/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Independence.ConvolutionPower
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Algebra.Order.Chebyshev

/-!
# Moments of convolution powers

Finite convolution powers preserve finite moments. Their means add, their scalar variances
add, and their first and second absolute moments admit bounds polynomial in the number of
summands. These bounds permit integration over a random number of independent summands,
without requiring exponential moments of the jump law.

The proofs use the independent coordinate variables on a finite product probability space.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsProbabilityMeasure μ]

/-- Convolution powers preserve membership in every `Lᵖ` space. -/
theorem memLp_id_convolutionPower {p : ℝ≥0∞} (hμ : MemLp id p μ) (n : ℕ) :
    MemLp id p (μ.convolutionPower n) := by
  have hlaw : HasLaw (fun x : Fin n → E ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
    simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
      (iIndepFun_pi (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)
  have hsum : MemLp (fun x : Fin n → E ↦ ∑ i, x i) p (Measure.pi fun _ ↦ μ) := by
    simpa using memLp_finsetSum Finset.univ (fun i _ ↦
      hμ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ μ) i))
  rw [← hlaw.map_eq]
  simpa only [Function.id_comp] using
    (memLp_map_measure_iff (g := id) (by fun_prop) hlaw.aemeasurable).2 hsum

/-- Convolution powers of a law with a finite first moment have finite first moments. -/
theorem integrable_id_convolutionPower (hμ : Integrable id μ) (n : ℕ) :
    Integrable id (μ.convolutionPower n) :=
  memLp_one_iff_integrable.1 (memLp_id_convolutionPower (memLp_one_iff_integrable.2 hμ) n)

/-- The mean of a convolution power is the number of summands times the jump mean. -/
theorem integral_id_convolutionPower [NormedSpace ℝ E] (hμ : Integrable id μ) (n : ℕ) :
    ∫ x, x ∂μ.convolutionPower n = n • ∫ x, x ∂μ := by
  have hlaw : HasLaw (fun x : Fin n → E ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
    simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
      (iIndepFun_pi (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)
  rw [← hlaw.integral_eq]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_eval (i := i) (μ := fun _ : Fin n ↦ μ) hμ)]
  simp [integral_eval]

/-- The first absolute moment of a convolution power grows at most linearly. -/
theorem integral_norm_convolutionPower_le (hμ : Integrable id μ) (n : ℕ) :
    ∫ x, ‖x‖ ∂μ.convolutionPower n ≤ (n : ℝ) * ∫ x, ‖x‖ ∂μ := by
  have hlaw : HasLaw (fun x : Fin n → E ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
    simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
      (iIndepFun_pi (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)
  rw [← hlaw.integral_comp (f := fun x ↦ ‖x‖) (by fun_prop)]
  simp only [Function.comp_apply]
  have heval (i : Fin n) : Integrable (fun x : Fin n → E ↦ ‖x i‖)
      (Measure.pi fun _ ↦ μ) := integrable_comp_eval (μ := fun _ : Fin n ↦ μ) hμ.norm
  calc
    _ ≤ ∫ x : Fin n → E, ∑ i, ‖x i‖ ∂Measure.pi (fun _ ↦ μ) := by
      apply integral_mono
      · exact hlaw.integrable_comp (integrable_id_convolutionPower hμ n).norm
      · exact integrable_finsetSum _ (fun i _ ↦ heval i)
      · exact fun x ↦ norm_sum_le _ _
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ heval i)]
      simp_rw [integral_comp_eval (μ := fun _ : Fin n ↦ μ)
        (f := fun x : E ↦ ‖x‖) (by fun_prop)]
      simp

/-- The second absolute moment of a convolution power grows at most quadratically. -/
theorem integral_norm_sq_convolutionPower_le (hμ : MemLp id 2 μ) (n : ℕ) :
    ∫ x, ‖x‖ ^ 2 ∂μ.convolutionPower n ≤ (n : ℝ) ^ 2 * ∫ x, ‖x‖ ^ 2 ∂μ := by
  have hlaw : HasLaw (fun x : Fin n → E ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
    simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
      (iIndepFun_pi (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)
  have hsq : Integrable (fun x : E ↦ ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
  have hpow := memLp_id_convolutionPower hμ n
  have heval (i : Fin n) : Integrable (fun x : Fin n → E ↦ ‖x i‖ ^ 2)
      (Measure.pi fun _ ↦ μ) := integrable_comp_eval (μ := fun _ : Fin n ↦ μ) hsq
  rw [← hlaw.integral_comp (f := fun x ↦ ‖x‖ ^ 2) (by fun_prop)]
  simp only [Function.comp_apply]
  calc
    _ ≤ ∫ x : Fin n → E, (n : ℝ) * ∑ i, ‖x i‖ ^ 2 ∂Measure.pi (fun _ ↦ μ) := by
      apply integral_mono
      · exact hlaw.integrable_comp
          ((memLp_two_iff_integrable_sq_norm hpow.aestronglyMeasurable).1 hpow)
      · exact (integrable_finsetSum _ (fun i _ ↦ heval i)).const_mul _
      · intro x
        calc
          ‖∑ i, x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
              (norm_sum_le _ _)
          _ ≤ _ := by simpa using
            (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n ↦ ‖x i‖))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ heval i)]
      simp_rw [integral_comp_eval (μ := fun _ : Fin n ↦ μ)
        (f := fun x : E ↦ ‖x‖ ^ 2) (by fun_prop)]
      simp [pow_two, mul_assoc]

variable [NormedSpace ℝ E]

/-- Covariances of linear observables add under convolution powers. Only the two observed
second moments need be finite. -/
theorem covariance_convolutionPower (μ : Measure E) [IsProbabilityMeasure μ]
    (L M : E →L[ℝ] ℝ) (hL : MemLp L 2 μ) (hM : MemLp M 2 μ) (n : ℕ) :
    covariance L M (μ.convolutionPower n) = (n : ℝ) * covariance L M μ := by
  classical
  have hlaw : HasLaw (fun x : Fin n → E ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
    simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
      (iIndepFun_pi (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)
  have hLeval (i : Fin n) : MemLp (fun x : Fin n → E ↦ L (x i)) 2
      (Measure.pi fun _ ↦ μ) := hL.comp_measurePreserving (measurePreserving_eval _ i)
  have hMeval (i : Fin n) : MemLp (fun x : Fin n → E ↦ M (x i)) 2
      (Measure.pi fun _ ↦ μ) := hM.comp_measurePreserving (measurePreserving_eval _ i)
  rw [← hlaw.covariance_fun_comp (f := L) (g := M) (by fun_prop) (by fun_prop)]
  simp only [_root_.map_sum]
  rw [covariance_fun_sum_fun_sum hLeval hMeval]
  calc
    _ = ∑ _ : Fin n, covariance L M μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · exact (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw.covariance_fun_comp
          (by fun_prop) (by fun_prop)
      · intro j _ hij
        have hindep := (iIndepFun_pi (μ := fun _ : Fin n ↦ μ)
          (fun _ : Fin n ↦ measurable_id.aemeasurable)).indepFun
          hij.symm
        exact (hindep.comp (by fun_prop) (by fun_prop)).covariance_eq_zero (hLeval i) (hMeval j)
      · simp
    _ = _ := by simp

end MeasureTheory.Measure
