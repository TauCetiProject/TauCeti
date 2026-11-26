/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.MarchenkoPastur

import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.IdentDistribIndep
import TauCeti.Analysis.Matrix.SampleCovariance.Measurable
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Separable

/-!
# The Marchenko–Pastur law in probability

For rectangular matrices of i.i.d. entries with a common centred law and unit second absolute
moment, the empirical covariance spectral measures converge weakly in probability as the aspect
ratio tends to a positive limit. The sample spaces can vary with the dimension. The joint law of
each rectangular matrix agrees with that of a corner of a single infinite i.i.d. array, so the
almost-sure theorem for the corners gives the probabilities of deviations at each size.
-/

public section

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- **Marchenko–Pastur law in probability.** Let `X n` be a `p n × n` matrix with independent
real or complex entries of common law `ν`, centred and with unit second absolute moment. If
`p n / n → y > 0`, the probability that the empirical spectral measure of `X n * (X n)ᴴ / n`
lies outside any weak neighborhood of `MP_y` tends to zero. The underlying sample spaces and
probability measures may vary with `n`. -/
theorem marchenkoPastur_in_probability {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    {p : ℕ → ℕ} [∀ n, NeZero (p n)] {X : (n : ℕ) → Ω n → Matrix (Fin (p n)) (Fin n) 𝕜}
    {ν : Measure 𝕜} {y : ℝ≥0}
    (hX : ∀ n (ij : Fin (p n) × Fin n), HasLaw (fun ω ↦ X n ω ij.1 ij.2) ν (P n))
    (hindep : ∀ n, iIndepFun (fun ij : Fin (p n) × Fin n ↦ fun ω ↦ X n ω ij.1 ij.2) (P n))
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y))
    {U : Set (ProbabilityMeasure ℝ)} (hU : U ∈ 𝓝 (marchenkoPastur y).toProbabilityMeasure) :
    Tendsto (fun n ↦ P n {ω | (sampleCovariance (X n ω)).spectralMeasure
      (isHermitian_sampleCovariance _) ∉ U}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure ν :=
    (hX 1 (0, 0)).isProbabilityMeasure_iff.mp (hindep 1).isProbabilityMeasure
  obtain ⟨Ω', _, Q, ξ, hξm, hξ, hξind, _⟩ := exists_iid (ℕ × ℕ) ν
  let Y (n : ℕ) (ω : Ω') : Matrix (Fin (p n)) (Fin n) 𝕜 :=
    Matrix.of fun i j ↦ ξ (i, j) ω
  let L (n : ℕ) (A : Matrix (Fin (p n)) (Fin n) 𝕜) : ProbabilityMeasure ℝ :=
    A.sampleCovariance.spectralMeasure (isHermitian_sampleCovariance A)
  have hLm (n : ℕ) : Measurable (L n) := measurable_spectralMeasure_sampleCovariance
  have hY (n : ℕ) : Measurable (Y n) := .of_eval_matrix _ fun i j ↦ hξm (i, j)
  have hLaw (n : ℕ) : IdentDistrib (L n ∘ X n) (L n ∘ Y n) (P n) Q := by
    have hξn := hξind.precomp
      (Fin.val_injective.prodMap Fin.val_injective :
        Function.Injective (fun ij : Fin (p n) × Fin n ↦ (ij.1.val, ij.2.val)))
    have hentries := IdentDistrib.pi (fun ij ↦ (hX n ij).identDistrib (hξ (ij.1, ij.2)))
      (hindep n) hξn
    exact (hentries.comp (MeasurableEquiv.curry (Fin (p n)) (Fin n) 𝕜).measurable).comp (hLm n)
  -- Use an open neighborhood so that equality in law transfers its complement event.
  obtain ⟨V, hVU, hVo, hVmem⟩ := mem_nhds_iff.1 hU
  have hVm : MeasurableSet Vᶜ := hVo.measurableSet.compl
  have hcorner : ∀ᵐ ω ∂Q, Tendsto (fun n ↦ (L n ∘ Y n) ω) atTop
      (𝓝 (marchenkoPastur y).toProbabilityMeasure) :=
    marchenkoPastur_ae hξ hξind hmean hvar hy hp
  have hVlim : Tendsto (fun n ↦ Q ((L n ∘ Y n) ⁻¹' Vᶜ)) atTop (𝓝 0) := by
    have hnever : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, ω ∈ (L n ∘ Y n) ⁻¹' Vᶜ ↔ ω ∈ (∅ : Set Ω') := by
      filter_upwards [hcorner] with ω hω
      filter_upwards [hω.eventually (hVo.mem_nhds hVmem)] with n hn
      exact iff_of_false (fun hbad ↦ hbad hn) (notMem_empty ω)
    simpa only [measure_empty] using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop .empty (fun n ↦ hVm.preimage ((hLm n).comp (hY n))) hnever
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVlim (fun _ ↦ zero_le) ?_
  intro n
  calc
    P n {ω | (L n ∘ X n) ω ∉ U} ≤ P n ((L n ∘ X n) ⁻¹' Vᶜ) :=
      measure_mono fun _ hω hVω ↦ hω (hVU hVω)
    _ = Q ((L n ∘ Y n) ⁻¹' Vᶜ) := (hLaw n).measure_mem_eq hVm

end TauCeti.Probability
