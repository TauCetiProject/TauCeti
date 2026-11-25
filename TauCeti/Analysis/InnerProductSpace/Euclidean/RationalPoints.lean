/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Points of rational coordinates in Euclidean space

This file defines the set `TauCeti.EuclideanSpace.rationalPoints n` of points of
`EuclideanSpace ℝ (Fin n)` all of whose coordinates are rational. It is countable and dense.

## Main definitions

* `TauCeti.EuclideanSpace.rationalPoints n`: the points of rational coordinates.

## Main results

* `TauCeti.EuclideanSpace.mem_rationalPoints_iff`: membership means every coordinate is rational.
* `TauCeti.EuclideanSpace.countable_rationalPoints`: the rational points form a countable set.
* `TauCeti.EuclideanSpace.dense_rationalPoints`: the rational points are dense.
-/

public section

open Set

namespace TauCeti.EuclideanSpace

/-- The points of rational coordinates in `EuclideanSpace ℝ (Fin n)`. -/
abbrev rationalPoints (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ)

/-- A point lies in `rationalPoints n` exactly when all of its coordinates are rational. -/
theorem mem_rationalPoints_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ rationalPoints n ↔ ∀ i, ∃ q : ℚ, x i = q := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨q, rfl⟩ i
    exact ⟨q i, rfl⟩
  · choose q hq using h
    exact ⟨q, by ext i; simp [hq]⟩

/-- The points of rational coordinates form a countable set. -/
theorem countable_rationalPoints {n : ℕ} : (rationalPoints n).Countable :=
  countable_range _

/-- The points of rational coordinates are dense in `EuclideanSpace ℝ (Fin n)`. -/
theorem dense_rationalPoints {n : ℕ} : Dense (rationalPoints n) := by
  have h : DenseRange fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n ↦ ℝ).symm.surjective.denseRange.comp h
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n ↦ ℝ).symm.continuous)

end TauCeti.EuclideanSpace
