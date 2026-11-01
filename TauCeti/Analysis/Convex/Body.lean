/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# The image of a convex body under a continuous linear map

A continuous linear map `f : V →L[ℝ] W` sends convex, compact, nonempty sets to convex, compact,
nonempty sets, so it pushes a convex body `K` of `V` forward to the convex body `K.map f` of `W`
with carrier `f '' K`. This is how a convex body is carried along a change of coordinates, for
instance to transport the successive minima of a lattice with respect to a body along a linear
equivalence.

## Main definitions

* `ConvexBody.map f K`: the image of the convex body `K` under the continuous linear map `f`.
-/

public section

open scoped Pointwise

namespace ConvexBody

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

end ConvexBody
