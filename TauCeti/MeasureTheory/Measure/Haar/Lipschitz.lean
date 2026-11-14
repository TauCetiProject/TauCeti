/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lipschitz images of Haar-null sets

A map from a finite-dimensional real normed space to one of at least the same dimension that is
Lipschitz on a set `s` sends `s` to a null set whenever `s` is null, for any additive Haar measures
on the source and the target. In dimension `d` the Hausdorff measure `μH[d]` is an additive Haar
measure, so every additive Haar measure is mutually absolutely continuous with it. Lipschitz maps
increase the Hausdorff `d`-measure by at most the factor `K ^ d`
(`LipschitzOnWith.hausdorffMeasure_image_le`), and a set of zero Hausdorff `d`-measure has zero
Hausdorff `d'`-measure for every `d' ≥ d`. The same factor `K ^ d` bounds the growth of the
normalized Euclidean Hausdorff measure `μHE[d]`, a constant multiple of `μH[d]`.

## Main statements

* `LipschitzOnWith.addHaar_image_eq_zero` — a map Lipschitz on a Haar-null set has a Haar-null
  image, from a finite-dimensional real normed space to one of at least the same dimension.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_le` — a `K`-Lipschitz map increases `μHE[d]`
  by at most the factor `K ^ d`.
* `LipschitzWith.euclideanHausdorffMeasure_image_inter_cone_div_le` — the image under a
  `K`-Lipschitz map of the parameters in a thin cone `{v | |ψ v| ≤ t ‖v‖}` within the ball of
  radius `c r` has `k`-dimensional density at most `K ^ k c ^ k` times the share of the cone in the
  unit ball.
-/

public section

open MeasureTheory MeasureTheory.Measure Module
open scoped NNReal ENNReal

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Lipschitz maps preserve Haar-null sets.** If `f : E → F` is Lipschitz on a set `s` that is
null for an additive Haar measure `μ` on `E`, and `E` and `F` are finite-dimensional real normed
spaces with `finrank ℝ E ≤ finrank ℝ F`, then `f '' s` is null for every additive Haar measure `ν`
on `F`. -/
theorem addHaar_image_eq_zero (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F)
    [IsAddHaarMeasure ν] (hdim : finrank ℝ E ≤ finrank ℝ F) {K : ℝ≥0} {f : E → F}
    {s : Set E} (hf : LipschitzOnWith K f s) (hs : μ s = 0) : ν (f '' s) = 0 := by
  -- With `d = finrank ℝ E`, `s` is `μH[d]`-null, hence so is its Lipschitz image; that image is
  -- then `μH[finrank ℝ F]`-null, and `ν` is absolutely continuous with respect to this measure.
  have hsE : μH[finrank ℝ E] s = 0 := absolutelyContinuous_isAddHaarMeasure _ μ hs
  have himage : μH[finrank ℝ E] (f '' s) = 0 := by
    simpa [hsE] using hf.hausdorffMeasure_image_le (finrank ℝ E).cast_nonneg
  exact absolutelyContinuous_isAddHaarMeasure ν μH[finrank ℝ F] <|
    nonpos_iff_eq_zero.1 ((hausdorffMeasure_mono (Nat.cast_le.2 hdim) _).trans_eq himage)

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A map that is `K`-Lipschitz on `s` increases the `d`-dimensional Euclidean Hausdorff measure
of `s` by at most the factor `K ^ d`. -/
theorem euclideanHausdorffMeasure_image_le {K : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, _root_.smul_apply, mul_smul_comm,
    ← ENNReal.rpow_natCast]
  gcongr
  exact hf.hausdorffMeasure_image_le d.cast_nonneg

end LipschitzOnWith

namespace LipschitzWith

open Metric Set

variable {Y : Type*} [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The image under a `K`-Lipschitz map of the parameters `u` with `u - u₀` in the part of a
cone `|ψ v| ≤ t ‖v‖` in the closed ball of radius `c r` has `k`-dimensional density at most
`K ^ k c ^ k` times the share of the cone in the unit ball. -/
theorem euclideanHausdorffMeasure_image_inter_cone_div_le
    {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (EuclideanSpace ℝ (Fin k))) (u₀ : EuclideanSpace ℝ (Fin k))
    (ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) (t : ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    μHE[k] (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤
      (K : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) /
        volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  have hcr : 0 < c * r := by positivity
  have himage := (hf.lipschitzOnWith (s := s ∩ (fun u ↦ u - u₀) ⁻¹'
    (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))).euclideanHausdorffMeasure_image_le k
  have hvol : μHE[k] (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖})) ≤
      ENNReal.ofReal ((c * r) ^ k) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
    have hμ : (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume k
    have hvolS := Measure.addHaar_closedBall_inter_setOf_abs_le_mul_norm volume ψ t hcr
    rw [finrank_euclideanSpace_fin] at hvolS
    rw [hμ, ← hvolS]
    refine (measure_mono inter_subset_right).trans_eq ?_
    simp only [sub_eq_add_neg]
    exact measure_preimage_add_right _ _ _
  rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
  calc μHE[k] (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
      ≤ (K : ℝ≥0∞) ^ k * (ENNReal.ofReal ((c * r) ^ k) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
        gcongr
        exact himage.trans (by gcongr)
    _ = ENNReal.ofReal (r ^ k) * ((K : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity)]
        ac_rfl
    _ = _ := ENNReal.mul_div_mul_left _ _
          (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

end LipschitzWith
