/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Constructions on convex bodies

A continuous linear map `f : V →L[ℝ] W` sends convex, compact, nonempty sets to convex, compact,
nonempty sets, so it pushes a convex body `K` of `V` forward to the convex body `K.map f` of `W`
with carrier `f '' K`. This is how a convex body is carried along a change of coordinates, for
instance to transport the successive minima of a lattice with respect to a body along a linear
equivalence.

In a proper real seminormed space `V`, every closed metric ball `Metric.closedBall x r` of
nonnegative radius `r` is likewise convex, compact, and nonempty, giving `ConvexBody.closedBall`.

## Main definitions

* `ConvexBody.map f K`: the image of the convex body `K` under the continuous linear map `f`.
* `ConvexBody.closedBall x r hr`: `Metric.closedBall x r` (`0 ≤ r`) as a convex body in a proper
  real seminormed space.
-/

public section

open scoped Pointwise

namespace ConvexBody

section Map

variable {V W X : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W] [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X]

/-- The image of a convex body under a continuous linear map, as a convex body. -/
def map (f : V →L[ℝ] W) (K : ConvexBody V) : ConvexBody W where
  carrier := f '' K
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f

@[simp, norm_cast]
theorem coe_map (f : V →L[ℝ] W) (K : ConvexBody V) : (K.map f : Set W) = f '' K := (rfl)

@[simp]
theorem mem_map {f : V →L[ℝ] W} {K : ConvexBody V} {y : W} : y ∈ K.map f ↔ ∃ x ∈ K, f x = y :=
  Iff.rfl

@[simp]
theorem map_id (K : ConvexBody V) : K.map (ContinuousLinearMap.id ℝ V) = K :=
  ConvexBody.ext (Set.image_id _)

theorem map_comp (g : W →L[ℝ] X) (f : V →L[ℝ] W) (K : ConvexBody V) :
    K.map (g.comp f) = (K.map f).map g :=
  ConvexBody.ext (Set.image_comp g f _)

end Map

section ClosedBall

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- The closed ball `Metric.closedBall x r` of nonnegative radius in a proper real seminormed
space, packaged as a `ConvexBody`. -/
def closedBall (x : V) (r : ℝ) (hr : 0 ≤ r) : ConvexBody V where
  carrier := Metric.closedBall x r
  convex' := convex_closedBall x r
  isCompact' := isCompact_closedBall x r
  nonempty' := Metric.nonempty_closedBall.2 hr

/-- The carrier of `ConvexBody.closedBall x r hr` is `Metric.closedBall x r`. -/
@[simp, norm_cast]
theorem coe_closedBall (x : V) (r : ℝ) (hr : 0 ≤ r) :
    (closedBall x r hr : Set V) = Metric.closedBall x r :=
  (rfl)

/-- Membership in `ConvexBody.closedBall x r hr` reduces to `dist y x ≤ r`. -/
@[simp]
theorem mem_closedBall {x y : V} {r : ℝ} {hr : 0 ≤ r} :
    y ∈ closedBall x r hr ↔ dist y x ≤ r :=
  Metric.mem_closedBall

/-- For `0 < r`, the center `x` belongs to the interior of `ConvexBody.closedBall x r hr.le`. -/
theorem mem_interior_closedBall_self (x : V) {r : ℝ} (hr : 0 < r) :
    x ∈ interior (closedBall x r hr.le : Set V) :=
  Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)

end ClosedBall

end ConvexBody
