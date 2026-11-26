/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Points of rational coordinates in Euclidean space

This file defines the set `TauCeti.EuclideanSpace.rationalPoints n` of points of
`EuclideanSpace ℝ (Fin n)` all of whose coordinates are rational. It is countable, dense and,
for `n ≠ 0`, null.

## Main definitions

* `TauCeti.EuclideanSpace.rationalPoints n`: the points of rational coordinates.

## Main results

* `TauCeti.EuclideanSpace.rationalPoints_eq_range`: the rational points as the range of the
  coordinatewise cast `(Fin n → ℚ) → EuclideanSpace ℝ (Fin n)`.
* `TauCeti.EuclideanSpace.mem_rationalPoints_iff`: membership means every coordinate is rational.
* `TauCeti.EuclideanSpace.countable_rationalPoints`: the rational points form a countable set.
* `TauCeti.EuclideanSpace.dense_rationalPoints`: the rational points are dense.
* `TauCeti.EuclideanSpace.volume_rationalPoints`: the rational points form a null set, for `n ≠ 0`.
-/

public section

open MeasureTheory Set

namespace TauCeti.EuclideanSpace

/-- The points of rational coordinates in `EuclideanSpace ℝ (Fin n)`. -/
def rationalPoints (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ)

/-- The points of rational coordinates are the range of the coordinatewise cast from `ℚ`. -/
theorem rationalPoints_eq_range (n : ℕ) :
    rationalPoints n = range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ) :=
  (rfl)

/-- A point lies in `rationalPoints n` exactly when all of its coordinates are rational. -/
@[simp]
theorem mem_rationalPoints_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ rationalPoints n ↔ ∀ i, ∃ q : ℚ, x i = q := by
  rw [rationalPoints_eq_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨q, rfl⟩ i
    exact ⟨q i, rfl⟩
  · choose q hq using h
    exact ⟨q, by ext i; simp [hq]⟩

/-- The points of rational coordinates form a countable set. -/
theorem countable_rationalPoints {n : ℕ} : (rationalPoints n).Countable := by
  rw [rationalPoints_eq_range]
  exact countable_range _

/-- The points of rational coordinates are dense in `EuclideanSpace ℝ (Fin n)`. -/
theorem dense_rationalPoints {n : ℕ} : Dense (rationalPoints n) := by
  rw [rationalPoints_eq_range]
  have h : DenseRange fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  exact (WithLp.toLp_surjective 2).denseRange.comp h (PiLp.continuous_toLp 2 _)

/-- The points of rational coordinates form a null set, for `n ≠ 0`. -/
theorem volume_rationalPoints {n : ℕ} [NeZero n] : volume (rationalPoints n) = 0 :=
  countable_rationalPoints.measure_zero _

end TauCeti.EuclideanSpace
