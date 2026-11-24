/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Tensoring in functor categories

For the pointwise monoidal structure on a functor category `J ⥤ C`, colimits of shape `K` are
computed pointwise when `C` has them, so tensoring with a functor `F` preserves them as soon as
tensoring with each value `F.obj j` does in `C`. This is how colimit preservation passes from a
monoidal category to its simplicial objects with the degreewise tensor product. The proofs adapt
that of the corresponding instance for cartesian monoidal `C` in
`Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory` to arbitrary monoidal `C`.

Tensoring on the left is linear whenever tensoring with each value of the fixed functor is
linear.
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

variable {R : Type*} [Semiring R] [Preadditive C] [Linear R C]

/-- Pointwise tensoring on the left is linear if it is linear at each value of the fixed
functor. -/
instance functorCategoryTensorLeftLinear (F : J ⥤ C) [∀ j, (tensorLeft (F.obj j)).Linear R] :
    (tensorLeft F).Linear R where
  map_smul f r := by
    ext j
    -- Reduce the pointwise operations on both sides together, keeping their source and
    -- target in the same tensor-product carriers in the coefficient category.
    change F.obj j ◁ (r • f.app j) = r • (F.obj j ◁ f.app j)
    exact (tensorLeft (F.obj j)).map_smul r (f.app j)

end TauCeti
