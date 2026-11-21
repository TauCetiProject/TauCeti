/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic

import TauCeti.Analysis.Matrix.MeasurableSpace

/-!
# Measurability of sample covariance matrices and their spectral measures

The sample covariance map and its empirical spectral measure are measurable for the
entrywise measurable structure, including for an empty sample. The spectral probability
measure requires a nonempty row index.
-/

public section

open MeasureTheory

namespace Matrix

variable {p n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The sample covariance matrix is an entrywise measurable function of the data matrix. -/
@[fun_prop]
theorem measurable_sampleCovariance :
    Measurable (sampleCovariance : Matrix p n 𝕜 → Matrix p p 𝕜) := by
  rw [funext sampleCovariance_def]
  have hgram := TauCeti.measurable_matrix_mul_conjTranspose (R := 𝕜) (m := p) (n := n)
    continuous_star.measurable
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  simp only [Matrix.smul_apply]
  exact (continuous_const_smul (1 / (Fintype.card n : ℝ))).measurable.comp hgram.eval_matrix

/-- The empirical spectral measure of a sample covariance is measurable in the data. -/
@[fun_prop]
theorem measurable_spectralMeasure_sampleCovariance [Fintype p] [DecidableEq p] [Nonempty p] :
    Measurable (fun X : Matrix p n 𝕜 ↦ X.sampleCovariance.spectralMeasure
      (isHermitian_sampleCovariance X)) :=
  measurable_spectralMeasure.comp
    (measurable_sampleCovariance.subtype_mk (h := fun X ↦ isHermitian_sampleCovariance X))

end Matrix
