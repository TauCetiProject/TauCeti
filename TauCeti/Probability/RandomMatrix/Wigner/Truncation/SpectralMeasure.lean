/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Truncation.Basic
public import TauCeti.Probability.RandomMatrix.Perturbation

/-!
# Spectral statistics of truncated Wigner corners

The expected normalized squared Frobenius error controls the difference of Lipschitz
spectral statistics in mean square and in probability, uniformly over positive dimensions.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1 and Lemma 2.1.19.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

variable [IsProbabilityMeasure P] {X : Ω → ℂ} (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
  (hd : ∀ ij, IdentDistrib (ξ ij) X P P)

include hd hX hmean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mean-square control of a Lipschitz spectral statistic, uniformly in positive dimension. -/
theorem integral_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_sq_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f)
    (hη : ∀ i, AEMeasurable (η i) P) (R : ℝ≥0) (n : ℕ) :
    ∫ ω, ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖ ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  refine (integral_norm_integral_spectralMeasure_sub_sq_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq hX hd R _) hf
    (aemeasurable_wignerMatrix (fun ij _ ↦ (hd ij).aemeasurable_fst) fun i _ ↦ hη i)
    (aemeasurable_wignerMatrix (fun ij _ ↦
      (((hd ij).symm.memLp_snd hX).aestronglyMeasurable.centeredTruncation R).aemeasurable)
      fun i _ ↦ hη i)).trans ?_
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean hd R n)
      (sq_nonneg (K : ℝ))

/-- A spectral-statistic approximation probability bound uniform over all positive dimensions. -/
theorem measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε)
    (R : ℝ≥0) (n : ℕ) :
    P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖} ≤
      ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P) := by
  refine (measure_norm_integral_spectralMeasure_sub_ge_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq hX hd R _) hf hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    mul_inv, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean hd R n)
      (by positivity : 0 ≤ (K : ℝ) ^ 2 / ε ^ 2)

/-- Bounded centered off-diagonal approximation is valid in probability, uniformly over
all positive matrix sizes, for every Lipschitz spectral statistic. -/
theorem tendsto_iSup_measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ≥0 ↦ ⨆ n : ℕ,
      P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
        ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
          (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖})
      atTop (𝓝 0) := by
  have ht : Tendsto (fun R : ℝ≥0 ↦ ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (hX.tendsto_integral_indicator_norm_sq.const_mul ((K : ℝ) ^ 2 / ε ^ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ bot_le) (fun R ↦ iSup_le fun n ↦
      measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
        hX hmean hd hf hε R n)

end TauCeti.Probability
