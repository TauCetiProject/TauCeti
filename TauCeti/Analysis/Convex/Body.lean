/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Constructions on convex bodies

A continuous linear map `f : V →L[ℝ] W` sends convex, compact, nonempty sets to convex, compact,
nonempty sets, so it pushes a convex body `K` of `V` forward to the convex body `K.map f` of `W`
with carrier `f '' K`. This is how a convex body is carried along a change of coordinates, for
instance to transport the successive minima of a lattice with respect to a body along a linear
equivalence. A convex body with `0` in its interior is a compact neighbourhood of `0`, so it forces
the ambient normed space to be finite-dimensional
(`ConvexBody.finiteDimensional_of_zero_mem_interior`).

In a proper real seminormed space `V`, every closed metric ball `Metric.closedBall x r` of
nonnegative radius `r` is likewise convex, compact, and nonempty, giving `ConvexBody.closedBall`.

The closed unit ball `ConvexBody.closedUnitBall E` has dilates given by closed balls of radius
`t ≥ 0` and contains the origin in its interior. These facts identify successive minima for the
closed unit ball with lengths of lattice vectors.

## Main definitions

* `ConvexBody.map f K`: the image of the convex body `K` under the continuous linear map `f`.
* `ConvexBody.closedBall x r hr`: `Metric.closedBall x r` (`0 ≤ r`) as a convex body in a proper
  real seminormed space.
* `ConvexBody.closedUnitBall E`: the closed unit ball of a proper real normed space.
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

/-- A convex body with `0` in its interior lives in a finite-dimensional space: it contains a
compact neighbourhood of `0`, so `E` is locally compact (Riesz's theorem). -/
theorem finiteDimensional_of_zero_mem_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : ConvexBody E} (hK : 0 ∈ interior (K : Set E)) : FiniteDimensional ℝ E :=
  haveI := K.isCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (mem_interior_iff_mem_nhds.1 hK)
  .of_locallyCompactSpace ℝ

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

/-! ### The closed unit ball -/

section ClosedUnitBall

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
/-- The closed unit ball of a proper real normed space, such as a finite-dimensional one, as a
convex body. -/
def closedUnitBall [ProperSpace E] : ConvexBody E :=
  closedBall 0 1 zero_le_one

@[simp, norm_cast]
theorem coe_closedUnitBall [ProperSpace E] :
    (closedUnitBall E : Set E) = Metric.closedBall 0 1 := (rfl)

variable {K : ConvexBody E}

/-- For a convex body `K` that is the closed unit ball and `t ≥ 0`, the dilate `t • K` is the
closed ball of radius `t`. -/
theorem mem_smul_iff_norm_le_of_coe_eq_closedBall (hK : (K : Set E) = Metric.closedBall 0 1) {t : ℝ}
    (ht : 0 ≤ t) {x : E} : x ∈ t • (K : Set E) ↔ ‖x‖ ≤ t := by
  rw [hK, smul_closedBall t 0 zero_le_one, smul_zero, Real.norm_eq_abs, abs_of_nonneg ht,
    mul_one, mem_closedBall_zero_iff]

/-- A convex body that is the closed unit ball contains the origin in its interior. -/
theorem zero_mem_interior_of_coe_eq_closedBall (hK : (K : Set E) = Metric.closedBall 0 1) :
    0 ∈ interior (K : Set E) := by
  rw [hK]
  exact mem_interior_iff_mem_nhds.2 (closedBall_mem_nhds 0 one_pos)

end ClosedUnitBall

end ConvexBody
