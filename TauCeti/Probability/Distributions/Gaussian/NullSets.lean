/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Gaussian null sets under affine changes of variables

The standard Gaussian and Lebesgue measure on a finite-dimensional real inner product space
have the same null sets. In particular, translations and nonzero scalar dilations
preserve Gaussian null sets. This allows almost-everywhere properties of a function to be
transported to the integrands defining Gaussian smoothing, including in dimension zero.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Standard Gaussian measure is absolutely continuous with respect to Lebesgue measure. -/
theorem stdGaussian_absolutelyContinuous_volume : stdGaussian E ≪ (volume : Measure E) := by
  rw [stdGaussian_eq_withDensity_norm E]
  exact withDensity_absolutelyContinuous _ _

/-- Lebesgue measure is absolutely continuous with respect to standard Gaussian measure. -/
theorem volume_absolutelyContinuous_stdGaussian : (volume : Measure E) ≪ stdGaussian E := by
  rw [stdGaussian_eq_withDensity_norm E]
  exact absolutelyContinuous_withDensity_ofReal (by fun_prop)
    (Filter.Eventually.of_forall fun x => by positivity)

/-- An affine map with nonzero scalar linear part preserves Gaussian null sets. -/
theorem quasiMeasurePreserving_add_smul_stdGaussian (x : E) {σ : ℝ} (hσ : σ ≠ 0) :
    QuasiMeasurePreserving (fun z => x + σ • z) (stdGaussian E) (stdGaussian E) := by
  exact ((quasiMeasurePreserving_add_left (volume : Measure E) x).comp
    (Measure.quasiMeasurePreserving_smul volume hσ)).mono
      stdGaussian_absolutelyContinuous_volume volume_absolutelyContinuous_stdGaussian

/-- An almost-everywhere assertion holds after a nondegenerate affine change of Gaussian
variables exactly when it holds before the change. No measurability of the assertion is needed. -/
theorem ae_add_smul_stdGaussian_iff (x : E) {σ : ℝ} (hσ : σ ≠ 0) {p : E → Prop} :
    (∀ᵐ z ∂stdGaussian E, p (x + σ • z)) ↔ ∀ᵐ z ∂stdGaussian E, p z := by
  refine ⟨fun h => ?_, (quasiMeasurePreserving_add_smul_stdGaussian x hσ).ae⟩
  have h' := (quasiMeasurePreserving_add_smul_stdGaussian (-σ⁻¹ • x)
    (inv_ne_zero hσ)).ae h
  simpa [smul_add, smul_smul, hσ] using h'

end TauCeti.Probability
