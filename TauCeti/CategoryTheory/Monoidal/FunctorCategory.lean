/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Tensoring in functor categories

For the pointwise monoidal structure on a functor category `J ⥤ C`, colimits of shape `K` are
computed pointwise when `C` has them, so tensoring with a functor `F` preserves them as soon as
tensoring with each value `F.obj j` does in `C`. This is how colimit preservation passes from a
monoidal category to its simplicial objects with the degreewise tensor product. The proofs adapt
that of the corresponding instance for cartesian monoidal `C` in
`Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory` to arbitrary monoidal `C`.

The pointwise tensor product is additive or linear in both variables whenever the tensor
product in the coefficient category is.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

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

variable [Preadditive C] [MonoidalPreadditive C]

/-- The pointwise tensor product in a functor category is additive in both variables. -/
instance functorCategoryMonoidalPreadditive : MonoidalPreadditive (J ⥤ C) where
  whiskerLeft_zero := by
    intros
    ext j
    exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight := by
    intros
    ext j
    exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add f g := by
    ext j
    exact MonoidalPreadditive.whiskerLeft_add (f.app j) (g.app j)
  add_whiskerRight f g := by
    ext j
    exact MonoidalPreadditive.add_whiskerRight (f.app j) (g.app j)

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

/-- The pointwise tensor product in a functor category is linear in both variables. -/
instance functorCategoryMonoidalLinear : MonoidalLinear R (J ⥤ C) where
  whiskerLeft_smul F {_ _} r f := by
    ext j
    dsimp only [Monoidal.whiskerLeft_app, NatTrans.app_smul, Monoidal.tensorObj_obj]
    exact MonoidalLinear.whiskerLeft_smul (F.obj j) r (f.app j)
  smul_whiskerRight r {_ _} f F := by
    ext j
    dsimp only [Monoidal.whiskerRight_app, NatTrans.app_smul, Monoidal.tensorObj_obj]
    exact MonoidalLinear.smul_whiskerRight r (f.app j) (F.obj j)

end TauCeti
