/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Independence.ConvolutionPower
public import TauCeti.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.MeanInequalities

/-!
# Moments of convolution powers

Finite convolution powers preserve finite moments. Their means and covariances of linear
observables add, and their absolute moments of order `p ≥ 1` admit bounds of order `n ^ p`
in the number `n` of summands. These bounds permit integration over a random number of summands,
without requiring exponential moments of the base measure.

The moment-generating function of a measurable additive real observable under an `n`-fold
convolution power of an s-finite measure is the `n`th power of its moment-generating function
under the original measure. This identity also holds for totalized divergent integrals.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α] [MeasurableAdd₂ α]

/-- The mgf of an additive real observable under a convolution power is the corresponding
power of its mgf. -/
@[simp]
theorem mgf_addMonoidHom_convolutionPower (μ : Measure α) [SFinite μ]
    (f : α →+ ℝ) (hf : Measurable f) (n : ℕ) (t : ℝ) :
    mgf f (μ.convolutionPower n) t = mgf f μ t ^ n := by
  rw [← mgf_id_map hf.aemeasurable, Measure.map_convolutionPower μ f hf,
    ← mgf_id_map hf.aemeasurable]
  induction n with
  | zero => simp [mgf]
  | succ n ih => simp [TauCeti.mgf_id_conv, ih, pow_succ]

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]
  {μ : Measure E} [IsProbabilityMeasure μ]

/-- Convolution powers preserve membership in every `Lᵖ` space. -/
theorem memLp_id_convolutionPower {p : ℝ≥0∞} (hμ : MemLp id p μ) (n : ℕ) :
    MemLp id p (μ.convolutionPower n) := by
  have hlaw := μ.hasLaw_sum_pi_convolutionPower n
  have hsum : MemLp (fun x : Fin n → E ↦ ∑ i, x i) p (Measure.pi fun _ ↦ μ) := by
    simpa using memLp_finsetSum Finset.univ (fun i _ ↦
      hμ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ μ) i))
  rw [← hlaw.map_eq]
  simpa only [Function.id_comp] using
    (memLp_map_measure_iff (g := id) (by
      obtain ⟨s, hs, hs_ae⟩ := hsum.aestronglyMeasurable.isSeparable_ae_range
      apply aestronglyMeasurable_id_of_isSeparable hs.closure
      refine (ae_map_iff hlaw.aemeasurable isClosed_closure.measurableSet).2 ?_
      filter_upwards [hs_ae] with x hx using subset_closure hx) hlaw.aemeasurable).2 hsum

/-- Convolution powers of a law with a finite first moment have finite first moments. -/
theorem integrable_id_convolutionPower (hμ : Integrable id μ) (n : ℕ) :
    Integrable id (μ.convolutionPower n) :=
  memLp_one_iff_integrable.1 (memLp_id_convolutionPower (memLp_one_iff_integrable.2 hμ) n)

/-- The mean of a convolution power is the number of summands times the mean of `μ`. -/
@[simp]
theorem integral_id_convolutionPower [NormedSpace ℝ E] (hμ : Integrable id μ) (n : ℕ) :
    ∫ x, x ∂μ.convolutionPower n = n • ∫ x, x ∂μ := by
  have hlaw := μ.hasLaw_sum_pi_convolutionPower n
  rw [← hlaw.integral_comp (f := fun x : E ↦ x)
    (integrable_id_convolutionPower hμ n).aestronglyMeasurable]
  simp only [Function.comp_apply]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_eval (i := i) (μ := fun _ : Fin n ↦ μ) hμ)]
  simp [integral_comp_eval (μ := fun _ : Fin n ↦ μ) (f := fun x : E ↦ x)
    hμ.aestronglyMeasurable]

/-- The absolute moment of order `p ≥ 1` of a convolution power grows at most as `n ^ p`. -/
theorem integral_norm_rpow_convolutionPower_le {p : ℝ} (hp : 1 ≤ p)
    (hμ : MemLp id (ENNReal.ofReal p) μ) (n : ℕ) :
    ∫ x, ‖x‖ ^ p ∂μ.convolutionPower n ≤ (n : ℝ) ^ p * ∫ x, ‖x‖ ^ p ∂μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hlaw := μ.hasLaw_sum_pi_convolutionPower n
  have hrpow : Integrable (fun x : E ↦ ‖x‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0, id_eq] using hμ.integrable_norm_rpow'
  have hpow := memLp_id_convolutionPower hμ n
  have heval (i : Fin n) : Integrable (fun x : Fin n → E ↦ ‖x i‖ ^ p)
      (Measure.pi fun _ ↦ μ) := integrable_comp_eval (μ := fun _ : Fin n ↦ μ) hrpow
  rw [← hlaw.integral_comp (f := fun x ↦ ‖x‖ ^ p) (by
    simpa only [ENNReal.toReal_ofReal hp0, id_eq] using
      hpow.integrable_norm_rpow'.aestronglyMeasurable)]
  simp only [Function.comp_apply]
  calc
    _ ≤ ∫ x : Fin n → E, (n : ℝ) ^ (p - 1) * ∑ i, ‖x i‖ ^ p
        ∂Measure.pi (fun _ ↦ μ) := by
      apply integral_mono
      · exact hlaw.integrable_comp (f := fun x : E ↦ ‖x‖ ^ p) (by
          simpa only [ENNReal.toReal_ofReal hp0, id_eq] using hpow.integrable_norm_rpow')
      · exact (integrable_finsetSum _ (fun i _ ↦ heval i)).const_mul _
      · intro x
        calc
          ‖∑ i, x i‖ ^ p ≤ (∑ i, ‖x i‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) hp0
          _ ≤ _ := by
            simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
              Finset.univ (f := fun i : Fin n ↦ ‖x i‖) hp (fun _ _ ↦ norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ heval i)]
      simp_rw [integral_comp_eval (μ := fun _ : Fin n ↦ μ)
        (f := fun x : E ↦ ‖x‖ ^ p) hrpow.aestronglyMeasurable]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc]
      congr 1
      simpa using (Real.rpow_add_one' (Nat.cast_nonneg n)
        (by linarith : p - 1 + 1 ≠ 0) : (n : ℝ) ^ (p - 1 + 1) = _).symm

variable [NormedSpace ℝ E]

/-- The mean of a linear observable under a convolution power is the number of summands
times its mean under `μ`. Only the observed first moment needs to be finite. -/
@[simp]
theorem integral_continuousLinearMap_convolutionPower (μ : Measure E) [IsProbabilityMeasure μ]
    (L : E →L[ℝ] ℝ) (hL : Integrable L μ) (n : ℕ) :
    ∫ x, L x ∂μ.convolutionPower n = (n : ℝ) * ∫ x, L x ∂μ := by
  have hlaw := μ.hasLaw_sum_pi_convolutionPower n
  rw [← hlaw.integral_comp (f := L) (by fun_prop)]
  simp only [Function.comp_apply, _root_.map_sum]
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_comp_eval (μ := fun _ : Fin n ↦ μ) hL)]
  simp_rw [integral_comp_eval (μ := fun _ : Fin n ↦ μ) (f := L) (by fun_prop)]
  simp

/-- Covariances of linear observables add under convolution powers. Only the two observed
second moments need be finite. -/
@[simp]
theorem covariance_convolutionPower (μ : Measure E) [IsProbabilityMeasure μ]
    (L M : E →L[ℝ] ℝ) (hL : MemLp L 2 μ) (hM : MemLp M 2 μ) (n : ℕ) :
    covariance L M (μ.convolutionPower n) = (n : ℝ) * covariance L M μ := by
  classical
  have hlaw := μ.hasLaw_sum_pi_convolutionPower n
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
