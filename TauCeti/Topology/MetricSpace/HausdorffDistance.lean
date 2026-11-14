/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distances to sets

For a nonempty set in a pseudometric space, the extended distance `Metric.infEDist x S` equals
`ENNReal.ofReal t` for some `t ≥ 0` exactly when the real distance `Metric.infDist x S` equals `t`
(`Metric.infEDist_eq_ofReal_iff`).

Hausdorff convergence to zero passes along chains of sets: if `A i` approaches `B i` and `B i`
approaches `Z` in the Hausdorff extended distance, then `A i` approaches `Z`
(`Metric.tendsto_hausdorffEDist_of_tendsto_of_tendsto`). If sets `A i` approach a closed set `Z`,
every limit of points `y i ∈ A i` lies in `Z` (`Metric.mem_of_tendsto_hausdorffEDist`).
-/

public section

open Filter Topology

namespace Metric

/-- For a nonempty set in a pseudometric space, the extended distance to it equals a nonnegative
real number exactly when the real distance does. -/
theorem infEDist_eq_ofReal_iff {X : Type*} [PseudoMetricSpace X] {x : X} {S : Set X}
    {t : ℝ} (hS : S.Nonempty) (ht : 0 ≤ t) :
    infEDist x S = ENNReal.ofReal t ↔ infDist x S = t := by
  constructor
  · intro h
    rw [infDist, h, ENNReal.toReal_ofReal ht]
  · intro h
    rw [← h, infDist, ENNReal.ofReal_toReal (infEDist_ne_top hS)]

variable {X ι : Type*} [PseudoEMetricSpace X] {l : Filter ι}

/-- If sets `A i` approach `B i` and `B i` approach `Z` in the Hausdorff extended distance, then
`A i` approach `Z`. -/
theorem tendsto_hausdorffEDist_of_tendsto_of_tendsto {A B : ι → Set X} {Z : Set X}
    (hAB : Tendsto (fun i ↦ hausdorffEDist (A i) (B i)) l (𝓝 0))
    (hBZ : Tendsto (fun i ↦ hausdorffEDist (B i) Z) l (𝓝 0)) :
    Tendsto (fun i ↦ hausdorffEDist (A i) Z) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hAB.add hBZ)
    (fun _ ↦ zero_le) fun _ ↦ hausdorffEDist_triangle

/-- If sets `A i` approach a closed set `Z` in the Hausdorff extended distance, then every limit
of points `y i ∈ A i` lies in `Z`. -/
theorem mem_of_tendsto_hausdorffEDist [l.NeBot] {A : ι → Set X} {Z : Set X} (hZ : IsClosed Z)
    (hA : Tendsto (fun i ↦ hausdorffEDist (A i) Z) l (𝓝 0)) {y : ι → X}
    (hy : ∀ᶠ i in l, y i ∈ A i) {y₀ : X} (hy₀ : Tendsto y l (𝓝 y₀)) : y₀ ∈ Z := by
  -- `infEDist y₀ Z ≤ edist y₀ (y i) + hausdorffEDist (A i) Z`, and both terms tend to zero.
  have hlim : Tendsto (fun i ↦ edist y₀ (y i) + hausdorffEDist (A i) Z) l (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := y₀)).edist hy₀).add hA
  rw [mem_iff_infEDist_zero_of_closed hZ, ← nonpos_iff_eq_zero]
  refine ge_of_tendsto hlim ?_
  filter_upwards [hy] with i hi
  exact infEDist_le_edist_add_infEDist.trans
    (add_le_add le_rfl (infEDist_le_hausdorffEDist_of_mem hi))

end Metric
