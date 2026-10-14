/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Monoidal opposites of monoidal functors

A functor `F : C ⥤ D` induces a functor between the monoidal opposites by applying `F` to the
underlying objects and morphisms. If `F` is strong monoidal, so is this induced functor: its tensor
comparison is the monoidal opposite of the comparison of `F`, with the two inputs reversed.

This construction lets a monoidal functor whose codomain is a monoidal opposite be applied twice.
In particular, applying it to a monoidal dual functor produces the second half of a monoidal
double-dual functor.

## Main declarations

* `CategoryTheory.Functor.opMop`: the functor induced between monoidal opposites;
* `CategoryTheory.Functor.opMopMonoidal`: its strong monoidal structure.
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite

namespace CategoryTheory.Functor

open LaxMonoidal OplaxMonoidal Monoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

-- Adapted from https://github.com/leanprover-community/mathlib4/pull/42145.
/-- A functor between monoidal categories, applied to the underlying objects and morphisms of their
monoidal opposites. -/
@[expose]
def opMop (F : C ⥤ D) : Cᴹᵒᵖ ⥤ Dᴹᵒᵖ :=
  unmopFunctor C ⋙ F ⋙ mopFunctor D

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- The monoidal opposite of a functor applies the original functor to the underlying object. -/
@[simp]
theorem opMop_obj (F : C ⥤ D) (X : Cᴹᵒᵖ) : F.opMop.obj X = mop (F.obj (unmop X)) :=
  rfl

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- The monoidal opposite of a functor applies the original functor to the underlying morphism. -/
@[simp]
theorem opMop_map (F : C ⥤ D) {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) :
    F.opMop.map f = (F.map f.unmop).mop :=
  rfl

/-- Taking monoidal opposites preserves strong monoidal functors. -/
@[instance_reducible]
instance opMopMonoidal (F : C ⥤ D) [F.Monoidal] : F.opMop.Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := (Monoidal.εIso F).mop
      μIso X Y := (Monoidal.μIso F (unmop Y) (unmop X)).mop
      μIso_hom_natural_left f X := by
        apply Quiver.Hom.unmop_inj
        simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
          Monoidal.μIso_hom, Functor.mapIso_hom, mopFunctor_map, Quiver.Hom.unmop_mop] using
          LaxMonoidal.μ_natural_right F (unmop X) f.unmop
      μIso_hom_natural_right X f := by
        apply Quiver.Hom.unmop_inj
        simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
          Monoidal.μIso_hom, Functor.mapIso_hom, mopFunctor_map, Quiver.Hom.unmop_mop] using
          LaxMonoidal.μ_natural_left F f.unmop (unmop X)
      associativity X Y Z := by
        apply Quiver.Hom.unmop_inj
        simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_whiskerLeft,
          unmop_tensorObj, Monoidal.μIso_hom, Functor.mapIso_hom, mopFunctor_map,
          Quiver.Hom.unmop_mop, unmop_hom_associator] using
            LaxMonoidal.associativity_inv F (unmop Z) (unmop Y) (unmop X)
      left_unitality X := by
        apply Quiver.Hom.unmop_inj
        simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
          unmop_tensorUnit, Monoidal.εIso_hom, Monoidal.μIso_hom, Functor.mapIso_hom,
          mopFunctor_map, Quiver.Hom.unmop_mop, unmop_hom_leftUnitor] using
            LaxMonoidal.right_unitality F (unmop X)
      right_unitality X := by
        apply Quiver.Hom.unmop_inj
        simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
          unmop_tensorUnit, Monoidal.εIso_hom, Monoidal.μIso_hom, Functor.mapIso_hom,
          mopFunctor_map, Quiver.Hom.unmop_mop, unmop_hom_rightUnitor] using
            LaxMonoidal.left_unitality F (unmop X) }

variable (F : C ⥤ D) [F.Monoidal]

/-- The unit comparison of the monoidal opposite of a strong monoidal functor. -/
@[simp]
theorem opMop_ε : ε F.opMop = (ε F).mop :=
  rfl

/-- The inverse unit comparison of the monoidal opposite of a strong monoidal functor. -/
@[simp]
theorem opMop_η : η F.opMop = (η F).mop :=
  rfl

/-- The tensor comparison of the monoidal opposite of a strong monoidal functor. -/
@[simp]
theorem opMop_μ (X Y : Cᴹᵒᵖ) :
    μ F.opMop X Y = (μ F (unmop Y) (unmop X)).mop :=
  rfl

/-- The inverse tensor comparison of the monoidal opposite of a strong monoidal functor. -/
@[simp]
theorem opMop_δ (X Y : Cᴹᵒᵖ) :
    δ F.opMop X Y = (δ F (unmop Y) (unmop X)).mop :=
  rfl

end CategoryTheory.Functor
