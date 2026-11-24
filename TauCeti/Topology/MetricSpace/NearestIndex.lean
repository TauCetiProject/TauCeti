/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

/-!
# The index of a nearest point among finitely many

For finitely many points `θ i` of a pseudometric space, indexed by a nonempty linear order,
`TauCeti.nearestIndex θ y` is the least index of a nearest point to `y`: ties between equally near
points are broken by the order of the index type.

## Main definitions

* `TauCeti.nearestIndex θ y`: the least index `i` with `dist y (θ i) ≤ dist y (θ j)` for all `j`.

## Main results

* `TauCeti.nearestIndex_eq_iff`, `TauCeti.isLeast_nearestIndex`: the characterization as the least
  index of a nearest point.
* `TauCeti.dist_nearestIndex_le`: the selected point minimizes the distance to `y`.
* `TauCeti.dist_nearestIndex_le_two_mul`: the selected point lies within twice the distance from
  `y` to any `θ j` of `θ j`.

Its measurability is `TauCeti.measurable_nearestIndex`, in
`TauCeti.MeasureTheory.MeasurableSpace.Metric`.
-/

public section

namespace TauCeti

section NearestIndex

variable {ι Y : Type*} [PseudoMetricSpace Y] [Fintype ι] [Nonempty ι] [LinearOrder ι]

open scoped Classical in
/-- The index of a nearest point to `y` among the `θ i`: the least `i`, for the linear order of
`ι`, such that `dist y (θ i) ≤ dist y (θ j)` for every `j`. -/
noncomputable def nearestIndex (θ : ι → Y) (y : Y) : ι :=
  (Finset.univ.filter fun i ↦ ∀ j, dist y (θ i) ≤ dist y (θ j)).min' <| by
    obtain ⟨i, hi⟩ := Finite.exists_min (fun i ↦ dist y (θ i))
    exact ⟨i, by simpa using hi⟩

/-- `nearestIndex θ y = i` exactly when `θ i` is a nearest point to `y` and every index of a
nearest point is at least `i`. -/
theorem nearestIndex_eq_iff {θ : ι → Y} {y : Y} {i : ι} :
    nearestIndex θ y = i ↔ (∀ j, dist y (θ i) ≤ dist y (θ j)) ∧
      ∀ j, (∀ k, dist y (θ j) ≤ dist y (θ k)) → i ≤ j := by
  simp [nearestIndex, Finset.min'_eq_iff]

/-- `nearestIndex θ y` is the least index of a nearest point to `y`. -/
theorem isLeast_nearestIndex (θ : ι → Y) (y : Y) :
    IsLeast {i | ∀ j, dist y (θ i) ≤ dist y (θ j)} (nearestIndex θ y) :=
  nearestIndex_eq_iff.1 rfl

/-- `θ (nearestIndex θ y)` is a nearest point to `y`. -/
@[simp]
theorem dist_nearestIndex_le (θ : ι → Y) (y : Y) (j : ι) :
    dist y (θ (nearestIndex θ y)) ≤ dist y (θ j) :=
  (nearestIndex_eq_iff.1 rfl).1 j

/-- The nearest point to `y` is within twice the distance from `y` to `θ j` of `θ j`. -/
theorem dist_nearestIndex_le_two_mul (θ : ι → Y) (y : Y) (j : ι) :
    dist (θ (nearestIndex θ y)) (θ j) ≤ 2 * dist y (θ j) := by
  calc dist (θ (nearestIndex θ y)) (θ j) ≤ dist y (θ (nearestIndex θ y)) + dist y (θ j) :=
        dist_triangle_left _ _ _
    _ ≤ 2 * dist y (θ j) := by linarith [dist_nearestIndex_le θ y j]

end NearestIndex

end TauCeti
