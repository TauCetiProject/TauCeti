/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.RandomMatrix.Concentration.Resolvent

import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.Probability.RandomMatrix.CircularLaw.Replacement.Basic

/-!
# Almost-sure replacement for Hermitian dilation resolvents

Concentration of the normalized resolvent trace upgrades
`TauCeti.tendsto_integral_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw`
from replacement in expectation to almost-sure comparison.
`MeasureTheory.ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform`
then transfers deterministic weak spectral limits of shifted Hermitian dilations.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89, §5.1.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti.Probability

/-- At each fixed nonreal spectral parameter, the difference between normalized resolvent
traces tends to zero on a product of measurable conull sets. For each array of size `k + 1`,
the entries are multiplied by `1 / √(k + 1)` before adding the shared deterministic shift.
The fixed i.i.d. entry laws have matching finite complex means, complex second moments and
second absolute moments. -/
theorem exists_measurableSet_mem_ae_tendsto_normalizedResolventTrace_fromBlocks_sub_of_hasLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    {Y : (k : ℕ) → Ω' → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (hY : ∀ k, HasLaw (Y k) (Measure.pi (fun _ ↦ ν)) Q)
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) := (D k).addInvSqrtCardSmulEntries
    let f (k : ℕ) x := (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).normalizedResolventTrace z
    ∃ s ∈ ae P, ∃ t ∈ ae Q, MeasurableSet s ∧ MeasurableSet t ∧
      ∀ ω ∈ s, ∀ ω' ∈ t, Tendsto (fun k ↦ f k (X k ω) - f k (Y k ω')) atTop (𝓝 0) := by
  intro Z f
  have hmeanDiff :=
    tendsto_integral_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
      hX hY hμ hν hmean hsq habs D hz
  have hXcenter := ae_tendsto_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
    hX D hz
  have hYcenter := ae_tendsto_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
    hY D hz
  obtain ⟨s, hs, hsm, hXs⟩ := hXcenter.exists_measurable_mem
  obtain ⟨t, ht, htm, hYt⟩ := hYcenter.exists_measurable_mem
  refine ⟨s, hs, t, ht, hsm, htm, fun ω hω ω' hω' ↦ ?_⟩
  convert ((hXs ω hω).add hmeanDiff).sub (hYt ω' hω') using 1
  · ext k
    ring
  · simp

/-- Almost-sure weak convergence of the spectral measures of shifted Hermitian dilations
transfers between fixed i.i.d. entry laws with matching finite mixed moments through degree
two. For each array of size `k + 1`, the entries are multiplied by `1 / √(k + 1)` before adding
the shared deterministic shift. The arrays may be realized on different spaces. The limiting
probability measure is deterministic. -/
theorem ae_tendsto_spectralMeasure_fromBlocks_of_hasLaw_of_ae_tendsto
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    {Y : (k : ℕ) → Ω' → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (hY : ∀ k, HasLaw (Y k) (Measure.pi (fun _ ↦ ν)) Q)
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {ρ : ProbabilityMeasure ℝ} :
    let Z (k : ℕ) := (D k).addInvSqrtCardSmulEntries
    let L (k : ℕ) x := (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).spectralMeasure
      (IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero)
    (∀ᵐ ω' ∂Q, Tendsto (fun k ↦ L k (Y k ω')) atTop (𝓝 ρ)) →
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ L k (X k ω)) atTop (𝓝 ρ) := by
  intro Z L hlim
  have := (hY 0).isProbabilityMeasure
  apply ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform
  intro z hz
  have htrace (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :
      resolventTransform (L k x : Measure ℝ) z =
        (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).normalizedResolventTrace z := by
    have hH : (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
    exact resolventTransform_spectralMeasure _ hH (hH.notMem_spectrum_of_im_ne_zero hz.ne')
  obtain ⟨s, hs, t, ht, -, -, hreplace⟩ :=
    exists_measurableSet_mem_ae_tendsto_normalizedResolventTrace_fromBlocks_sub_of_hasLaw
      hX hY hμ hν hmean hsq habs D hz.ne'
  obtain ⟨ω', hω', hω't⟩ := (hlim.and ht).exists
  filter_upwards [hs] with ω hω
  have hRef := ProbabilityMeasure.tendsto_resolventTransform_of_tendsto hω' hz.ne'
  have hdiff' : Tendsto (fun k ↦ resolventTransform (L k (X k ω) : Measure ℝ) z -
      resolventTransform (L k (Y k ω') : Measure ℝ) z) atTop (𝓝 0) := by
    simp only [htrace]
    exact hreplace ω hω ω' hω't
  simpa only [sub_add_cancel, zero_add] using hdiff'.add hRef

end TauCeti.Probability
