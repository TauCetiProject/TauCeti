/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Lipschitz images of Haar-null sets

A map from a finite-dimensional real normed space to one of at least the same dimension that is
Lipschitz on a set `s` sends `s` to a null set whenever `s` is null, for any additive Haar measures
on the source and the target. In dimension `d` the Hausdorff measure `μH[d]` is an additive Haar
measure, so every additive Haar measure is mutually absolutely continuous with it. Lipschitz maps
increase the Hausdorff `d`-measure by at most the factor `K ^ d`
(`LipschitzOnWith.hausdorffMeasure_image_le`), and a set of zero Hausdorff `d`-measure has zero
Hausdorff `d'`-measure for every `d' ≥ d`.

## Main statements

* `LipschitzOnWith.addHaar_image_eq_zero` — a map Lipschitz on a Haar-null set has a Haar-null
  image, from a finite-dimensional real normed space to one of at least the same dimension.
-/

public section

open MeasureTheory MeasureTheory.Measure Module

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Lipschitz maps preserve Haar-null sets.** If `f : E → F` is Lipschitz on a set `s` that is
null for an additive Haar measure `μ` on `E`, and `E` and `F` are finite-dimensional real normed
spaces with `finrank ℝ E ≤ finrank ℝ F`, then `f '' s` is null for every additive Haar measure `ν`
on `F`. -/
theorem addHaar_image_eq_zero (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F)
    [IsAddHaarMeasure ν] (hdim : finrank ℝ E ≤ finrank ℝ F) {K : NNReal} {f : E → F}
    {s : Set E} (hf : LipschitzOnWith K f s) (hs : μ s = 0) : ν (f '' s) = 0 := by
  -- With `d = finrank ℝ E`, `s` is `μH[d]`-null, hence so is its Lipschitz image; that image is
  -- then `μH[finrank ℝ F]`-null, and `ν` is absolutely continuous with respect to this measure.
  set d := finrank ℝ E
  have hsE : (μH[d] : Measure E) s = 0 :=
    absolutelyContinuous_isAddHaarMeasure (μH[d] : Measure E) μ hs
  have himage : (μH[d] : Measure F) (f '' s) = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc (μH[d] : Measure F) (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μH[d] s :=
          hf.hausdorffMeasure_image_le (Nat.cast_nonneg d)
      _ = 0 := by rw [hsE, mul_zero]
  refine absolutelyContinuous_isAddHaarMeasure ν (μH[finrank ℝ F] : Measure F) ?_
  exact le_antisymm ((hausdorffMeasure_mono (by exact_mod_cast hdim) _).trans himage.le)
    (zero_le)

end LipschitzOnWith
