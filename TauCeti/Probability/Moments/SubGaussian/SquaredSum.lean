/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubGaussian
public import TauCeti.Probability.Moments.SubExponential

/-!
# Concentration of sums of squared sub-Gaussian variables

Independent sub-Gaussian variables with common variance proxy `c` have a centered sum of
squares with a Bernstein tail at scales `c * sqrt (card ι)` and `c`. This is also the
fixed-direction estimate for the Gram matrix of independent sub-Gaussian rows.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §§2.8 and 4.6.
-/

public section

open MeasureTheory Real
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {X : ι → Ω → ℝ} {c : ℝ≥0}

/-- A centered sum of independent squared sub-Gaussian variables has a quadratic MGF bound
on the interval `c * |θ| ≤ 1 / 8`. -/
theorem mgf_sum_sq_sub_integral_le (hindep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) c P) {θ : ℝ}
    (hθ : (c : ℝ) * |θ| ≤ 1 / 8) :
    Integrable (fun ω ↦ exp (θ * ∑ i, (X i ω ^ 2 - ∫ ω', X i ω' ^ 2 ∂P))) P ∧
      mgf (fun ω ↦ ∑ i, (X i ω ^ 2 - ∫ ω', X i ω' ^ 2 ∂P)) P θ ≤
        exp (384 * (c : ℝ) ^ 2 * Fintype.card ι * θ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let Y : ι → Ω → ℝ := fun i ω ↦ X i ω ^ 2 - ∫ ω', X i ω' ^ 2 ∂P
  have hY : iIndepFun Y P := hindep.comp
    (fun i x ↦ x ^ 2 - ∫ ω', X i ω' ^ 2 ∂P) (fun _ ↦ by fun_prop)
  have hYm (i : ι) : AEMeasurable (Y i) P :=
    ((hX i).aemeasurable.pow_const 2).sub_const _
  refine ⟨?_, ?_⟩
  · exact hY.integrable_exp_mul_sum_of_aemeasurable
      (s := Finset.univ) (fun i _ ↦ hYm i) (fun i _ ↦ ((hX i).mgf_sq_sub_integral_le hθ).1)
  · simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_left_comm, mul_assoc] using hY.mgf_sum_le_exp_sum
      (s := Finset.univ) (fun i _ ↦ hYm i) (fun i _ ↦ ((hX i).mgf_sq_sub_integral_le hθ).2)

/-- Bernstein concentration for a centered sum of independent squared sub-Gaussian
variables. Zero proxies and empty sums are allowed, with total real division. -/
theorem measureReal_abs_sum_sq_sub_integral_gt_le (hindep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) c P) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |∑ i, (X i ω ^ 2 - ∫ ω', X i ω' ^ 2 ∂P)|} ≤
      2 * exp (-(1 / 1536) *
        min (t ^ 2 / ((c : ℝ) ^ 2 * Fintype.card ι)) (t / c)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hconstant : min (1 / (4 * (384 : ℝ))) (1 / (2 * (8 : ℝ))) = 1 / 1536 := by
    norm_num
  simpa only [hconstant] using
    (TauCeti.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le
      (Y := fun ω ↦ ∑ i, (X i ω ^ 2 - ∫ ω', X i ω' ^ 2 ∂P))
      (C₁ := 384) (C₂ := 8) (F := (c : ℝ) ^ 2 * Fintype.card ι) (op := (c : ℝ))
      (by norm_num) (by norm_num) (by positivity) c.coe_nonneg
      (by
        intro θ hθ
        obtain ⟨hi, hb⟩ := hindep.mgf_sum_sq_sub_integral_le hX (θ := θ) (by linarith)
        exact ⟨hi, hb.trans_eq (by congr 1; ring)⟩) ht)

end ProbabilityTheory.iIndepFun
