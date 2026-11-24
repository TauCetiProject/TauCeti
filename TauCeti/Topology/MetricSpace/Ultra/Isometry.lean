/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Displacement of isometries of ultrametric spaces

An isometry `f` of an ultrametric space moves a point `y` at most as far as the larger of the
displacement `dist (f x) x` of any other point `x` and the distance `dist x y`: by the strong
triangle inequality through `f x` and `x`, since `dist (f y) (f x) = dist y x`. In particular an
isometry fixing `x` moves every point of a ball around `x` by at most the radius. For a Galois
group acting isometrically on a valued field, this says that an element close to `α` has conjugates
as close to it as those of `α` are to `α`, up to their distance.

## Main results

* `Isometry.dist_apply_le_max`: `dist (f y) y ≤ max (dist (f x) x) (dist x y)` for an isometry `f`
  of an ultrametric space.
-/

public section

/-- **Displacement under an ultrametric isometry.** An isometry `f` of an ultrametric space moves
`y` at most as far as the larger of the displacement of `x` and the distance from `x` to `y`. -/
theorem Isometry.dist_apply_le_max {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]
    {f : X → X} (hf : Isometry f) (x y : X) : dist (f y) y ≤ max (dist (f x) x) (dist x y) :=
  calc dist (f y) y ≤ max (dist (f y) (f x)) (max (dist (f x) x) (dist x y)) :=
        (dist_triangle_max _ _ _).trans (max_le_max le_rfl (dist_triangle_max _ _ _))
    _ = max (dist (f x) x) (dist x y) := by
        rw [hf.dist_eq, dist_comm y x, max_left_comm, max_self]
