/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Independence.Matrix

import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.Probability.RandomMatrix.CircularLaw.Replacement
import TauCeti.Probability.RandomMatrix.Concentration.Resolvent

/-!
# Almost-sure replacement for Hermitian dilation resolvents

Concentration of the normalized resolvent trace about its expectation upgrades finite-variance
replacement in expectation to almost-sure comparison. This transfers deterministic weak spectral
limits of shifted Hermitian dilations between entry laws with matching moments.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89, §5.1.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti.Probability

private theorem ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
    ∀ᵐ ω ∂P, Tendsto (fun k ↦ f k (X k ω) - ∫ w, f k (X k w) ∂P) atTop (𝓝 0) := by
  intro Z _
  have hentry (k : ℕ) (i j : Fin (k + 1)) : AEMeasurable (fun ω ↦ X k ω (i, j)) P :=
    (measurable_pi_apply _).comp_aemeasurable (hX k).aemeasurable
  have hrows (k : ℕ) : iIndepFun (fun i ω ↦ (Z k (X k ω)).row i) P := by
    have hraw := (hasLaw_pi_iff.mp (hX k)).1.matrix_row
      (X := fun ω ↦ Matrix.of fun i j ↦ X k ω (i, j)) (hentry k)
    let g (i : Fin (k + 1)) (r : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :=
      D k i j + (Real.sqrt (k + 1))⁻¹ • r j
    have heq : (fun i ω ↦ (Z k (X k ω)).row i) =
        (fun i ↦ g i ∘ fun ω ↦ (Matrix.of fun i j ↦ X k ω (i, j)).row i) := by
      funext i ω j
      simp only [Z, g, Function.comp_apply, Matrix.row_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply]
    rw [heq]
    exact hraw.comp g (fun _ ↦ by fun_prop)
  have hm (k : ℕ) : AEMeasurable (fun ω ↦ Z k (X k ω)) P := by
    have hZ : Measurable (Z k) := by unfold Z; fun_prop
    exact hZ.comp_aemeasurable (hX k).aemeasurable
  exact ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral hrows hm hz

/-- Almost-sure finite-variance replacement for the normalized resolvent traces of shifted
Hermitian dilations. The two sequences may live on different probability spaces. Within each
matrix the entries have product law, and their laws match in complex mean, complex second
moment and second absolute moment. The same deterministic shift is used in both matrices. -/
theorem ae_ae_tendsto_normalized_trace_inv_fromBlocks_sub_of_hasLaw
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
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
    ∀ᵐ ω ∂P, ∀ᵐ ω' ∂Q, Tendsto (fun k ↦ f k (X k ω) - f k (Y k ω')) atTop (𝓝 0) := by
  intro Z f
  have hmeanDiff :=
    tendsto_integral_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
      hX hY hμ hν hmean hsq habs D hz
  filter_upwards [ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw hX D hz]
    with ω hω
  filter_upwards [ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw hY D hz]
    with ω' hω'
  convert (hω.add hmeanDiff).sub hω' using 1
  · ext k
    ring
  · simp

/-- Almost-sure weak convergence of the spectral measures of shifted Hermitian dilations
transfers between independent entry laws with matching mixed moments through degree two.
The limiting probability measure is deterministic and the two arrays may be realized on
different spaces. -/
theorem ae_tendsto_spectralMeasure_fromBlocks_of_hasLaw
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
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
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
        ((2 : ℂ) * (k + 1))⁻¹ * (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace := by
    have hH : (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
    simpa only [L, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
      ← two_mul (k + 1 : ℂ)] using
      resolventTransform_spectralMeasure _ hH (hH.notMem_spectrum_of_im_ne_zero hz.ne')
  have hreplace :=
    ae_ae_tendsto_normalized_trace_inv_fromBlocks_sub_of_hasLaw hX hY hμ hν hmean hsq habs D hz.ne'
  filter_upwards [hreplace] with ω hω
  obtain ⟨ω', hω', hdiff⟩ := (hlim.and hω).exists
  have hRef := ProbabilityMeasure.tendsto_resolventTransform_of_tendsto hω' hz.ne'
  have hdiff' : Tendsto (fun k ↦ resolventTransform (L k (X k ω) : Measure ℝ) z -
      resolventTransform (L k (Y k ω') : Measure ℝ) z) atTop (𝓝 0) := by
    simp only [htrace]
    exact hdiff
  simpa only [sub_add_cancel, zero_add] using hdiff'.add hRef

end TauCeti.Probability
