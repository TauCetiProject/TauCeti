/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Retract

/-!
# Reflecting indecomposability through a functor

A functor preserving zero morphisms and binary biproducts reflects indecomposability at an
object if it reflects zero objects on that object's retracts. This local condition is useful
for quotient functors: a quotient can kill many objects while killing no nonzero summand of
the particular object under consideration.
-/

public section

namespace CategoryTheory.Functor

open Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- A functor preserving zero morphisms and binary biproducts reflects indecomposability at `X`
if every retract of `X` whose image is zero is itself zero. -/
theorem indecomposable_of_indecomposable_obj_of_reflects_isZero_retract (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBinaryBiproducts F] {X : C}
    (hX : Indecomposable (F.obj X))
    (hF : ∀ {Y : C}, Retract Y X → IsZero (F.obj Y) → IsZero Y) :
    Indecomposable X :=
  ⟨fun h0 ↦ hX.1 (F.map_isZero h0), fun Y Z e ↦
    (hX.2 _ _ (F.mapIso e ≪≫ F.mapBiprod Y Z)).imp
      (hF ((BinaryBiproduct.bicone Y Z).retract_left.trans e.symm.retract))
      (hF ((BinaryBiproduct.bicone Y Z).retract_right.trans e.symm.retract))⟩

end CategoryTheory.Functor
