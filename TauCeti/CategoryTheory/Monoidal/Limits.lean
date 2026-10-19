/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Colimit preservation for tensoring

The left unitor identifies tensoring on the left by the tensor unit with the identity functor.
Thus this functor preserves colimits, without any closedness assumption on the monoidal category.
This allows constructions that require tensoring to preserve coproducts to be used with the unit.

For the pointwise monoidal structure on a functor category `J ⥤ C`, colimits of shape `K` are
computed pointwise when `C` has them, so tensoring with a functor `F` preserves them as soon as
tensoring with each value `F.obj j` does in `C`. This is how colimit preservation passes from a
monoidal category to its simplicial objects with the degreewise tensor product. The proofs adapt
that of the corresponding instance for cartesian monoidal `C` in
`Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory` to arbitrary monoidal `C`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w w' v u

namespace TauCeti

/-- Tensoring on the left with the tensor unit preserves colimits, via
`MonoidalCategory.leftUnitorNatIso`. -/
instance preservesColimits_tensorUnitLeft (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    PreservesColimitsOfSize.{w, w'} (tensorUnitLeft C) :=
  preservesColimits_of_natIso (leftUnitorNatIso C).symm

section FunctorCategory

variable {C J K : Type*} [Category* C] [MonoidalCategory C] [Category* J] [Category* K]
  [HasColimitsOfShape K C]

/-- For the pointwise tensor product on `J ⥤ C`, tensoring on the left with `F` preserves
colimits of shape `K` when tensoring on the left with each `F.obj j` does. -/
instance preservesColimitsOfShape_functor_tensorLeft (F : J ⥤ C)
    [∀ j, PreservesColimitsOfShape K (tensorLeft (F.obj j))] :
    PreservesColimitsOfShape K (tensorLeft F) :=
  preservesColimitsOfShape_of_evaluation _ _ fun j ↦
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) : (evaluation J C).obj j ⋙ tensorLeft (F.obj j) ≅
        tensorLeft F ⋙ (evaluation J C).obj j)

/-- For the pointwise tensor product on `J ⥤ C`, tensoring on the right with `F` preserves
colimits of shape `K` when tensoring on the right with each `F.obj j` does. -/
instance preservesColimitsOfShape_functor_tensorRight (F : J ⥤ C)
    [∀ j, PreservesColimitsOfShape K (tensorRight (F.obj j))] :
    PreservesColimitsOfShape K (tensorRight F) :=
  preservesColimitsOfShape_of_evaluation _ _ fun j ↦
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) : (evaluation J C).obj j ⋙ tensorRight (F.obj j) ≅
        tensorRight F ⋙ (evaluation J C).obj j)

end FunctorCategory

end TauCeti
