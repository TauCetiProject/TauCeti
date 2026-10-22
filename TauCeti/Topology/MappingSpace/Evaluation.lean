/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
public import TauCeti.Topology.MappingSpace.Based

/-!
# Evaluation of mapping spaces

Evaluation at a point is a continuous map from the compact-open mapping space. The continuous
family of constant maps is a section of evaluation, and the fibre over a point is the based
mapping space. This gives the split sequence

`Map_*(B, X) → Map(B, X) → X`

used for mapping spaces out of spheres. No compactness or separation hypothesis is needed on
either space. That the constant maps embed `X` in `Map(B, X)` for nonempty `B` is
`ContinuousMap.isEmbedding_const`.

## Main declarations

* `TauCeti.mappingSpaceEval`: evaluation `Map(B, X) → X` at a chosen point of `B`.
* `TauCeti.mappingSpaceEval_comp_const'`: constant maps form a continuous section.
* `TauCeti.isQuotientMap_mappingSpaceEval`: evaluation is a quotient map.
* `TauCeti.mappingSpaceEval_comp_subtypeVal`: evaluation is constant on the based mapping space,
  the fibre over `x`; its universal lift is `TauCeti.BasedMap.lift`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

open Topology

namespace TauCeti

universe u v w

variable {B : Type u} {X : Type v} [TopologicalSpace B] [TopologicalSpace X]

/-- Evaluation at `b` as a continuous map from the compact-open mapping space. -/
def mappingSpaceEval (b : B) : C(C(B, X), X) :=
  ⟨fun f ↦ f b, continuous_eval_const b⟩

/-- Evaluation at `b` applies a map to `b`. -/
@[simp]
theorem mappingSpaceEval_apply (b : B) (f : C(B, X)) :
    mappingSpaceEval b f = f b :=
  (rfl)

/-- Evaluation at any point is a left inverse of the constant maps. -/
theorem leftInverse_mappingSpaceEval_const (b : B) :
    Function.LeftInverse (mappingSpaceEval (X := X) b) (ContinuousMap.const B) := fun _ ↦ by
  simp

/-- The continuous family of constant maps is a section of evaluation at every point. -/
@[simp]
theorem mappingSpaceEval_comp_const' (b : B) :
    (mappingSpaceEval (X := X) b).comp ContinuousMap.const' = ContinuousMap.id X :=
  ContinuousMap.ext (leftInverse_mappingSpaceEval_const b)

/-- Evaluation at a point is a quotient map. Its continuous section by constant maps detects
openness in the target. -/
theorem isQuotientMap_mappingSpaceEval (b : B) :
    IsQuotientMap (mappingSpaceEval (X := X) b) :=
  .of_inverse ContinuousMap.continuous_const' (mappingSpaceEval b).continuous
    (leftInverse_mappingSpaceEval_const b)

/-- Evaluation at `b` is constant with value `x` on the based mapping space, the subspace of maps
sending `b` to `x`. -/
@[simp]
theorem mappingSpaceEval_comp_subtypeVal (b : B) (x : X) :
    (mappingSpaceEval b).comp (ContinuousMap.subtypeVal {f : C(B, X) | f b = x}) =
      ContinuousMap.const _ x := by
  ext f
  simp only [ContinuousMap.comp_apply, mappingSpaceEval_apply, ContinuousMap.subtypeVal_apply,
    ContinuousMap.const_apply]
  exact f.2

end TauCeti
