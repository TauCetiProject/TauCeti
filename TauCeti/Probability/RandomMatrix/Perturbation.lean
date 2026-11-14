/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HoffmanWielandt
public import TauCeti.Probability.Moments.Chebyshev
public import TauCeti.Topology.Instances.Matrix

/-!
# Mean-square perturbations of random spectral statistics

The Hoffman–Wielandt bound transfers a small expected normalized squared Frobenius
perturbation to a small mean-square difference of Lipschitz spectral statistics, and to a
probability bound for their difference. The matrices may be dependent. For the mean-square
conclusion they are measurable almost everywhere; only the squared Frobenius perturbation
needs to be integrable. All matrix norms here are Frobenius norms.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), Lemma 2.1.19.
-/

public section

open MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace TauCeti.Probability

variable {Ω n 𝕜 E : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} (A B : Ω → Matrix n n 𝕜)
  (hA : ∀ ω, (A ω).IsHermitian) (hB : ∀ ω, (B ω).IsHermitian)
  (hD : Integrable (fun ω ↦ ‖A ω - B ω‖ ^ 2) P)
  {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f)

include hD hf

/-- The difference of Lipschitz spectral statistics has an integrable squared norm
when the matrices are measurable almost everywhere and the squared Frobenius error is integrable. -/
theorem integrable_norm_integral_spectralMeasure_sub_sq
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (hAm : AEMeasurable A P) (hBm : AEMeasurable B P) :
    Integrable (fun ω ↦ ‖(∫ x, f x ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) -
      ∫ x, f x ∂((B ω).spectralMeasure (hB ω) : Measure ℝ)‖ ^ 2) P := by
  have hc := (Matrix.isClosed_setOfPred_isHermitian (R := 𝕜) (n := n)).measurableSet
  have hAm' : AEMeasurable (fun ω ↦ (⟨A ω, hA ω⟩ : {M : Matrix n n 𝕜 // M.IsHermitian}))
      P := (MeasurableEmbedding.subtype_coe hc).aemeasurable_comp_iff.mp hAm
  have hBm' : AEMeasurable (fun ω ↦ (⟨B ω, hB ω⟩ : {M : Matrix n n 𝕜 // M.IsHermitian}))
      P := (MeasurableEmbedding.subtype_coe hc).aemeasurable_comp_iff.mp hBm
  -- Supply the inherited metric and countability on the predicate subtype of Hermitian matrices.
  have : TopologicalSpace.PseudoMetrizableSpace {M : Matrix n n 𝕜 // M.IsHermitian} :=
    @PseudoEMetricSpace.pseudoMetrizableSpace {M : Matrix n n 𝕜 // M.IsHermitian} inferInstance
  have : SecondCountableTopology {M : Matrix n n 𝕜 // M.IsHermitian} :=
    TopologicalSpace.secondCountableTopology_induced _ (Matrix n n 𝕜) Subtype.val
  have hSA := (Matrix.continuous_integral_spectralMeasure (n := n) (𝕜 := 𝕜)
    hf.continuous).comp_aestronglyMeasurable hAm'.aestronglyMeasurable
  have hSB := (Matrix.continuous_integral_spectralMeasure (n := n) (𝕜 := 𝕜)
    hf.continuous).comp_aestronglyMeasurable hBm'.aestronglyMeasurable
  have hi : Integrable (fun ω ↦
      ((K : ℝ) * ‖A ω - B ω‖ / Real.sqrt (Fintype.card n)) ^ 2) P := by
    simpa only [div_pow, mul_pow] using (hD.const_mul ((K : ℝ) ^ 2)).div_const _
  refine hi.mono' ((hSA.sub hSB).norm.pow 2) (.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le (hA ω) (hB ω) hf) 2

/-- Mean-square Frobenius control gives mean-square control of every Lipschitz linear
spectral statistic, with the normalization by matrix dimension. -/
theorem integral_norm_integral_spectralMeasure_sub_sq_le
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (hAm : AEMeasurable A P) (hBm : AEMeasurable B P) :
    ∫ ω, ‖(∫ x, f x ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) -
      ∫ x, f x ∂((B ω).spectralMeasure (hB ω) : Measure ℝ)‖ ^ 2 ∂P ≤
      (K : ℝ) ^ 2 / Fintype.card n * ∫ ω, ‖A ω - B ω‖ ^ 2 ∂P := by
  calc
    _ ≤ ∫ ω, ((K : ℝ) * ‖A ω - B ω‖ / Real.sqrt (Fintype.card n)) ^ 2 ∂P := by
      apply integral_mono_ae
        (integrable_norm_integral_spectralMeasure_sub_sq A B hA hB hD hf hAm hBm)
      · simpa only [div_pow, mul_pow] using (hD.const_mul ((K : ℝ) ^ 2)).div_const _
      · exact .of_forall fun ω ↦ pow_le_pow_left₀ (norm_nonneg _)
          (Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le
            (hA ω) (hB ω) hf) 2
    _ = _ := by
      simp_rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]
      rw [integral_mul_const, integral_const_mul]
      ring

/-- A quantitative probability bound for a Lipschitz spectral-statistic perturbation.
The estimate includes constant test functions (`K = 0`). -/
theorem measure_norm_integral_spectralMeasure_sub_ge_le {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ ‖(∫ x, f x ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) -
      ∫ x, f x ∂((B ω).spectralMeasure (hB ω) : Measure ℝ)‖} ≤
      ENNReal.ofReal ((K : ℝ) ^ 2 / (Fintype.card n * ε ^ 2) *
        ∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) := by
  let c : ℝ := K / Real.sqrt (Fintype.card n)
  have hc : 0 ≤ c := by positivity
  have hi : Integrable (fun ω ↦ ‖c * ‖A ω - B ω‖‖ ^ 2) P := by
    simpa only [norm_mul, Real.norm_of_nonneg hc, Real.norm_of_nonneg (norm_nonneg _),
      mul_pow] using hD.const_mul (c ^ 2)
  calc
    _ ≤ P {ω | ε ≤ ‖c * ‖A ω - B ω‖‖} := by
      apply measure_mono
      intro ω hω
      rw [Set.mem_ofPred_eq, Real.norm_of_nonneg (mul_nonneg hc (norm_nonneg _))]
      exact hω.trans (by
        simpa only [c, div_mul_eq_mul_div] using
          Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le
            (hA ω) (hB ω) hf)
    _ ≤ ENNReal.ofReal ((∫ ω, ‖c * ‖A ω - B ω‖‖ ^ 2 ∂P) / ε ^ 2) :=
      meas_ge_le_integral_norm_sq_div_sq hi hε
    _ = _ := by
      simp only [norm_mul, Real.norm_of_nonneg hc, Real.norm_of_nonneg (norm_nonneg _),
        mul_pow, integral_const_mul, c, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      congr 1
      ring

end TauCeti.Probability
