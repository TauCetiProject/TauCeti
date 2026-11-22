/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Truncation.Basic
public import TauCeti.Probability.RandomMatrix.SpectralMeasure.Perturbation

/-!
# Spectral statistics of truncated Wigner corners

Here a spectral statistic is the empirical spectral average of a Lipschitz test function. For a
`K`-Lipschitz test function, `K²` times the expected normalized squared Frobenius error bounds the
Bochner integral of the squared difference of such averages, and `K² / ε²` times it bounds the
outer probability of a difference at least `ε > 0`. For truncation at `R`, that error is at most
the second absolute moment of the common upper-entry law discarded beyond `R`, so the bounds are
uniform over positive dimensions. At a fixed dimension, only the upper entries of that corner
need a common centered, square-integrable law, and both bounds hold for an unrestricted diagonal.
The common diagonal cancels in the matrix difference, but not necessarily in the difference of
the averages, which depend nonlinearly on the matrix. So the integral bound is mean-square
control only when that squared difference is integrable, for instance when the diagonal entries
of the corner are almost everywhere measurable. Likewise, a nonmeasurable diagonal can make the
event of a large difference nonmeasurable; the tail bounds are ordinary probability bounds
whenever those events are measurable.

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

variable {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
  [IsProbabilityMeasure P] {X : Ω' → ℂ} (hX : MemLp X 2 Q)
  (hmean : ∫ ω, X ω ∂Q = 0)

include hX hmean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- At a positive dimension, the Bochner integral of the squared difference of the empirical
spectral averages of a Lipschitz test function is bounded independently of the dimension. The
upper entries of the corner share a centered, square-integrable law, and the inequality needs no
assumption on the diagonal entries. It is mean-square control when the squared difference is
integrable, for instance when the diagonal entries of the corner are almost everywhere
measurable. -/
theorem integral_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_sq_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) (R : ℝ≥0) (n : ℕ)
    (hd : ∀ ij : StrictUpper, ij.val.2 < n + 1 → IdentDistrib (ξ ij) X P Q) :
    ∫ ω, ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖ ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂Q := by
  refine (integral_norm_integral_spectralMeasure_sub_sq_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq
      (fun ij hij ↦ (hd ij hij).symm.memLp_snd hX) R) hf).trans ?_
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean R n hd)
      (sq_nonneg (K : ℝ))

/-- At a positive dimension, the outer probability that the empirical spectral averages of a
Lipschitz test function over the corner and over its centered truncation differ by at least a
positive threshold is bounded independently of the dimension. The upper entries of the corner
share a centered, square-integrable law, and the diagonal is unrestricted. This is an ordinary
probability bound whenever the event is measurable. -/
theorem measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε)
    (R : ℝ≥0) (n : ℕ) (hd : ∀ ij : StrictUpper, ij.val.2 < n + 1 → IdentDistrib (ξ ij) X P Q) :
    P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖} ≤
      ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂Q) := by
  refine (measure_norm_integral_spectralMeasure_sub_ge_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq
      (fun ij hij ↦ (hd ij hij).symm.memLp_snd hX) R) hf hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    mul_inv, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean R n hd)
      (by positivity : 0 ≤ (K : ℝ) ^ 2 / ε ^ 2)

/-- Bounded centered off-diagonal approximation is valid in outer probability, uniformly over
all positive matrix sizes, for the empirical spectral average of every Lipschitz test function
when the upper entries have a common centered, square-integrable law. These are ordinary
probabilities whenever the events are measurable. -/
theorem tendsto_iSup_measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation
    (hd : ∀ ij, IdentDistrib (ξ ij) X P Q)
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ≥0 ↦ ⨆ n : ℕ,
      P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
        ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
          (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖})
      atTop (𝓝 0) := by
  have ht : Tendsto (fun R : ℝ≥0 ↦ ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂Q))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (hX.tendsto_integral_indicator_norm_sq.const_mul ((K : ℝ) ^ 2 / ε ^ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ bot_le) (fun R ↦ iSup_le fun n ↦
      measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
        hX hmean hf hε R n fun ij _ ↦ hd ij)

end TauCeti.Probability
