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
either space.

## Main declarations

* `TauCeti.mappingSpaceEvaluation`: evaluation `Map(B, X) → X` at a chosen point of `B`.
* `TauCeti.mappingSpaceEvaluation_comp_const`: constant maps form a continuous section.
* `TauCeti.isQuotientMap_mappingSpaceEvaluation`: evaluation is a quotient map.
* `TauCeti.isEmbedding_mappingSpaceConst`: constant maps embed `X` into `Map(B, X)`.
* `TauCeti.BasedMap.inclusion`: the inclusion of the fibre over `x` into `Map(B, X)`.
* `TauCeti.BasedMap.lift`: the universal lift of a family of maps whose value at the basepoint is
  fixed.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

open Topology

namespace TauCeti

universe u v w

variable {B : Type u} {X : Type v} [TopologicalSpace B] [TopologicalSpace X]

/-- Evaluation at `b` as a continuous map from the compact-open mapping space. -/
def mappingSpaceEvaluation (b : B) : C(C(B, X), X) :=
  ⟨fun f ↦ f b, continuous_eval_const b⟩

/-- Evaluation at `b` applies a map to `b`. -/
@[simp]
theorem mappingSpaceEvaluation_apply (b : B) (f : C(B, X)) :
    mappingSpaceEvaluation b f = f b :=
  (rfl)

/-- The continuous family of constant maps is a section of evaluation at every point. -/
@[simp]
theorem mappingSpaceEvaluation_comp_const (b : B) :
    (mappingSpaceEvaluation (X := X) b).comp ContinuousMap.const' = ContinuousMap.id X := by
  ext x
  rfl

/-- Evaluation at a point is a quotient map. Its continuous section by constant maps detects
openness in the target. -/
theorem isQuotientMap_mappingSpaceEvaluation (b : B) :
    IsQuotientMap (mappingSpaceEvaluation (X := X) b) := by
  refine ⟨isCoinducing_iff.mpr fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦
      (mappingSpaceEvaluation b).continuous.isOpen_preimage s hs⟩,
    fun x ↦ ⟨ContinuousMap.const B x, rfl⟩⟩
  simpa only [Set.preimage_preimage, Function.comp_def, mappingSpaceEvaluation_apply,
      ContinuousMap.const_apply, Set.preimage_id'] using
    ContinuousMap.continuous_const'.isOpen_preimage _ hs

/-- Constant maps embed the target in its mapping space whenever the source has a chosen point.
Evaluation at that point is a continuous left inverse. -/
theorem isEmbedding_mappingSpaceConst (b : B) :
    IsEmbedding (ContinuousMap.const B : X → C(B, X)) :=
  (show Function.LeftInverse (mappingSpaceEvaluation (X := X) b) (ContinuousMap.const B) from
    fun _ ↦ rfl).isEmbedding (mappingSpaceEvaluation b).continuous
      ContinuousMap.continuous_const'

namespace BasedMap

variable {b : B} {x : X}

/-- The inclusion of the based mapping space, the fibre of evaluation over `x`, into the full
mapping space. -/
def inclusion : C(BasedMap B X b x, C(B, X)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of a based map is its underlying continuous map. -/
@[simp]
theorem inclusion_apply (f : BasedMap B X b x) : inclusion f = f.1 :=
  (rfl)

/-- Evaluation is constant with value `x` on the based mapping space. -/
@[simp]
theorem mappingSpaceEvaluation_comp_inclusion :
    (mappingSpaceEvaluation b).comp (inclusion (B := B) (X := X) (b := b) (x := x)) =
      ContinuousMap.const _ x := by
  ext f
  exact f.2

/-- A continuous family of maps with fixed value `x` at `b` lifts continuously to the based
mapping space. -/
def lift {Y : Type w} [TopologicalSpace Y] (f : C(Y, C(B, X))) (hf : ∀ y, f y b = x) :
    C(Y, BasedMap B X b x) :=
  ⟨fun y ↦ ⟨f y, hf y⟩, f.continuous.subtype_mk fun y ↦ hf y⟩

/-- A lifted family has the same underlying map at every parameter. -/
@[simp]
theorem lift_apply_val {Y : Type w} [TopologicalSpace Y] (f : C(Y, C(B, X)))
    (hf : ∀ y, f y b = x) (y : Y) :
    (lift f hf y).1 = f y :=
  (rfl)

/-- The underlying map of a lifted family is the original family. -/
@[simp]
theorem inclusion_comp_lift {Y : Type w} [TopologicalSpace Y] (f : C(Y, C(B, X)))
    (hf : ∀ y, f y b = x) :
    (inclusion (B := B) (X := X) (b := b) (x := x)).comp (lift f hf) = f :=
  (rfl)

/-- A lift into the based mapping space is determined by its underlying family of maps. -/
theorem lift_unique {Y : Type w} [TopologicalSpace Y] (f : C(Y, C(B, X)))
    (hf : ∀ y, f y b = x) (g : C(Y, BasedMap B X b x))
    (hg : (inclusion (B := B) (X := X) (b := b) (x := x)).comp g = f) :
    g = lift f hf := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  exact DFunLike.congr_fun hg y

end BasedMap

end TauCeti
