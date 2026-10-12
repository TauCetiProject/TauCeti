/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lipschitz images of Haar-null sets

A map between finite-dimensional real normed spaces of the same dimension that is Lipschitz on a
set `s` sends `s` to a null set whenever `s` is null, for any additive Haar measures on the source
and the target. Lipschitz maps increase the Hausdorff `d`-measure by at most the factor `K ^ d`
(`LipschitzOnWith.hausdorffMeasure_image_le`), and in dimension `d` every additive Haar measure is
mutually absolutely continuous with the `d`-dimensional Hausdorff measure, through the Euclidean
Hausdorff measure `μHE[d]`, which is itself an additive Haar measure.

## Main statements

* `LipschitzOnWith.addHaar_image_eq_zero` — a map Lipschitz on a Haar-null set has a Haar-null
  image, between finite-dimensional real normed spaces of equal dimension.
-/

public section

open MeasureTheory MeasureTheory.Measure Module

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Lipschitz maps preserve Haar-null sets.** If `f : E → F` is Lipschitz on a set `s` that is
null for an additive Haar measure `μ` on `E`, and `E` and `F` are finite-dimensional real normed
spaces of the same dimension, then `f '' s` is null for every additive Haar measure `ν` on `F`. -/
theorem addHaar_image_eq_zero (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F)
    [IsAddHaarMeasure ν] (hdim : finrank ℝ E = finrank ℝ F) {K : NNReal} {f : E → F}
    {s : Set E} (hf : LipschitzOnWith K f s) (hs : μ s = 0) : ν (f '' s) = 0 := by
  -- Both measures are absolutely continuous with respect to the `d`-dimensional Euclidean
  -- Hausdorff measure, a nonzero multiple of the Hausdorff measure `μH[d]`.
  set d := finrank ℝ E
  have hc : addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] ≠ 0 :=
    addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hsE : (μH[d] : Measure E) s = 0 := by
    have h := absolutelyContinuous_isAddHaarMeasure (μHE[d] : Measure E) μ hs
    rw [euclideanHausdorffMeasure_def, Measure.smul_apply, smul_eq_zero] at h
    exact h.resolve_left hc
  have himage : (μH[d] : Measure F) (f '' s) = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc (μH[d] : Measure F) (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μH[d] s :=
          hf.hausdorffMeasure_image_le (Nat.cast_nonneg d)
      _ = 0 := by rw [hsE, mul_zero]
  have : IsAddHaarMeasure (μHE[d] : Measure F) := by
    rw [hdim]
    infer_instance
  refine absolutelyContinuous_isAddHaarMeasure ν (μHE[d] : Measure F) ?_
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, himage, smul_zero]

end LipschitzOnWith
