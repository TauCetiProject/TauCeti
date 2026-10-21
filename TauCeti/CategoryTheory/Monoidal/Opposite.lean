/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Opposites and monoidal opposites of monoidal functors

A functor `F : C ⥤ D` induces a functor between the monoidal opposites by applying `F` to the
underlying objects and morphisms. If `F` is lax, oplax, or strong monoidal, so is this induced
functor: its tensor comparison is the monoidal opposite of the comparison of `F`, with the two
inputs reversed.

The opposite functor `F.op : Cᵒᵖ ⥤ Dᵒᵖ` exchanges the two kinds of structure: since morphisms
are reversed in `Cᵒᵖ` and `Dᵒᵖ`, the opposite of an oplax monoidal functor is lax monoidal and
the opposite of a lax monoidal functor is oplax monoidal, with comparison morphisms the opposites
of those of `F`. A strong monoidal functor has a strong monoidal opposite.

These constructions let a monoidal functor whose codomain is `(Dᵒᵖ)ᴹᵒᵖ`, such as the right dual
functor of a rigid monoidal category, be applied twice: its opposite monoidal opposite lands in
`((Dᵒᵖ)ᴹᵒᵖ)ᵒᵖᴹᵒᵖ`, which is identified with `D` as a monoidal category by
`MonoidalOpposite.opMopOpMopEquivalence`, since the two reversals of the tensor product cancel.

## Main declarations

* `CategoryTheory.Functor.opMop`: the functor induced between monoidal opposites;
* `CategoryTheory.Functor.opMopLaxMonoidal`, `CategoryTheory.Functor.opMopOplaxMonoidal`,
  `CategoryTheory.Functor.opMopMonoidal`: its lax, oplax, and strong monoidal structures;
* `CategoryTheory.Functor.isEquivalence_opMop`: the monoidal opposite of an equivalence is an
  equivalence;
* `CategoryTheory.Functor.opLaxMonoidal`, `CategoryTheory.Functor.opOplaxMonoidal`,
  `CategoryTheory.Functor.opMonoidal`: the lax, oplax, and strong monoidal structures on the
  opposite of an oplax, lax, and strong monoidal functor;
* `CategoryTheory.MonoidalOpposite.opMopOpMopEquivalence`: the equivalence
  `((Cᵒᵖ)ᴹᵒᵖ)ᵒᵖᴹᵒᵖ ≌ C`, whose functor is strong monoidal with identity
  comparison morphisms.
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite

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

/-- Taking monoidal opposites preserves lax monoidal functors. -/
@[instance_reducible]
instance opMopLaxMonoidal (F : C ⥤ D) [F.LaxMonoidal] : F.opMop.LaxMonoidal where
  ε := (ε F).mop
  μ X Y := (μ F (unmop Y) (unmop X)).mop
  μ_natural_left f X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
      Quiver.Hom.unmop_mop] using LaxMonoidal.μ_natural_right F (unmop X) f.unmop
  μ_natural_right X f := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
      Quiver.Hom.unmop_mop] using LaxMonoidal.μ_natural_left F f.unmop (unmop X)
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_whiskerLeft,
      unmop_tensorObj, Quiver.Hom.unmop_mop, unmop_hom_associator] using
        LaxMonoidal.associativity_inv F (unmop Z) (unmop Y) (unmop X)
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
      unmop_tensorUnit, Quiver.Hom.unmop_mop, unmop_hom_leftUnitor] using
        LaxMonoidal.right_unitality F (unmop X)
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
      unmop_tensorUnit, Quiver.Hom.unmop_mop, unmop_hom_rightUnitor] using
        LaxMonoidal.left_unitality F (unmop X)

/-- Taking monoidal opposites preserves oplax monoidal functors. -/
@[instance_reducible]
instance opMopOplaxMonoidal (F : C ⥤ D) [F.OplaxMonoidal] : F.opMop.OplaxMonoidal where
  η := (η F).mop
  δ X Y := (δ F (unmop Y) (unmop X)).mop
  δ_natural_left f X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
      Quiver.Hom.unmop_mop] using OplaxMonoidal.δ_natural_right F (unmop X) f.unmop
  δ_natural_right X f := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
      Quiver.Hom.unmop_mop] using OplaxMonoidal.δ_natural_left F f.unmop (unmop X)
  oplax_associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_whiskerLeft,
      unmop_tensorObj, Quiver.Hom.unmop_mop, unmop_hom_associator] using
        OplaxMonoidal.associativity_inv F (unmop Z) (unmop Y) (unmop X)
  oplax_left_unitality X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerRight, unmop_tensorObj,
      unmop_tensorUnit, Quiver.Hom.unmop_mop, unmop_inv_leftUnitor] using
        OplaxMonoidal.right_unitality F (unmop X)
  oplax_right_unitality X := by
    apply Quiver.Hom.unmop_inj
    simpa only [opMop_obj, opMop_map, unmop_comp, unmop_whiskerLeft, unmop_tensorObj,
      unmop_tensorUnit, Quiver.Hom.unmop_mop, unmop_inv_rightUnitor] using
        OplaxMonoidal.left_unitality F (unmop X)

/-- Taking monoidal opposites preserves strong monoidal functors. -/
@[instance_reducible]
instance opMopMonoidal (F : C ⥤ D) [F.Monoidal] : F.opMop.Monoidal where
  ε_η := Quiver.Hom.unmop_inj (Monoidal.ε_η F)
  η_ε := Quiver.Hom.unmop_inj (Monoidal.η_ε F)
  μ_δ X Y := Quiver.Hom.unmop_inj (Monoidal.μ_δ F (unmop Y) (unmop X))
  δ_μ X Y := Quiver.Hom.unmop_inj (Monoidal.δ_μ F (unmop Y) (unmop X))

/-- The monoidal opposite of an equivalence of categories is an equivalence of categories. -/
instance isEquivalence_opMop (F : C ⥤ D) [F.IsEquivalence] : F.opMop.IsEquivalence :=
  inferInstanceAs ((unmopEquiv C).functor ⋙ F ⋙ (mopEquiv D).functor).IsEquivalence

section

variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The unit comparison of the monoidal opposite of a lax monoidal functor. -/
@[simp]
theorem opMop_ε : ε F.opMop = (ε F).mop :=
  rfl

/-- The tensor comparison of the monoidal opposite of a lax monoidal functor. -/
@[simp]
theorem opMop_μ (X Y : Cᴹᵒᵖ) :
    μ F.opMop X Y = (μ F (unmop Y) (unmop X)).mop :=
  rfl

end

section

variable (F : C ⥤ D) [F.OplaxMonoidal]

/-- The counit comparison of the monoidal opposite of an oplax monoidal functor. -/
@[simp]
theorem opMop_η : η F.opMop = (η F).mop :=
  rfl

/-- The cotensor comparison of the monoidal opposite of an oplax monoidal functor. -/
@[simp]
theorem opMop_δ (X Y : Cᴹᵒᵖ) :
    δ F.opMop X Y = (δ F (unmop Y) (unmop X)).mop :=
  rfl

end

/-- The opposite of an oplax monoidal functor is lax monoidal. -/
@[instance_reducible]
instance opLaxMonoidal (F : C ⥤ D) [F.OplaxMonoidal] : F.op.LaxMonoidal where
  ε := (η F).op
  μ X Y := (δ F (unop X) (unop Y)).op
  μ_natural_left f X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_tensorObj,
      Quiver.Hom.unop_op] using OplaxMonoidal.δ_natural_left F f.unop (unop X)
  μ_natural_right X f := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerLeft, unop_tensorObj,
      Quiver.Hom.unop_op] using OplaxMonoidal.δ_natural_right F (unop X) f.unop
  associativity X Y Z := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_whiskerLeft,
      unop_tensorObj, Quiver.Hom.unop_op, unop_hom_associator, Category.assoc] using
        (OplaxMonoidal.associativity_inv F (unop X) (unop Y) (unop Z)).symm
  left_unitality X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_tensorObj,
      unop_tensorUnit, Quiver.Hom.unop_op, unop_hom_leftUnitor, Category.assoc] using
        OplaxMonoidal.left_unitality F (unop X)
  right_unitality X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerLeft, unop_tensorObj,
      unop_tensorUnit, Quiver.Hom.unop_op, unop_hom_rightUnitor, Category.assoc] using
        OplaxMonoidal.right_unitality F (unop X)

/-- The opposite of a lax monoidal functor is oplax monoidal. -/
@[instance_reducible]
instance opOplaxMonoidal (F : C ⥤ D) [F.LaxMonoidal] : F.op.OplaxMonoidal where
  η := (ε F).op
  δ X Y := (μ F (unop X) (unop Y)).op
  δ_natural_left f X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_tensorObj,
      Quiver.Hom.unop_op] using LaxMonoidal.μ_natural_left F f.unop (unop X)
  δ_natural_right X f := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerLeft, unop_tensorObj,
      Quiver.Hom.unop_op] using LaxMonoidal.μ_natural_right F (unop X) f.unop
  oplax_associativity X Y Z := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_whiskerLeft,
      unop_tensorObj, Quiver.Hom.unop_op, unop_hom_associator, Category.assoc] using
        (LaxMonoidal.associativity_inv F (unop X) (unop Y) (unop Z)).symm
  oplax_left_unitality X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerRight, unop_tensorObj,
      unop_tensorUnit, Quiver.Hom.unop_op, unop_inv_leftUnitor, Category.assoc] using
        LaxMonoidal.left_unitality F (unop X)
  oplax_right_unitality X := by
    apply Quiver.Hom.unop_inj
    simpa only [op_obj, op_map, unop_comp, unop_whiskerLeft, unop_tensorObj,
      unop_tensorUnit, Quiver.Hom.unop_op, unop_inv_rightUnitor, Category.assoc] using
        LaxMonoidal.right_unitality F (unop X)

/-- The opposite of a strong monoidal functor is strong monoidal. -/
@[instance_reducible]
instance opMonoidal (F : C ⥤ D) [F.Monoidal] : F.op.Monoidal where
  ε_η := Quiver.Hom.unop_inj (Monoidal.ε_η F)
  η_ε := Quiver.Hom.unop_inj (Monoidal.η_ε F)
  μ_δ X Y := Quiver.Hom.unop_inj (Monoidal.μ_δ F (unop X) (unop Y))
  δ_μ X Y := Quiver.Hom.unop_inj (Monoidal.δ_μ F (unop X) (unop Y))

section

variable (F : C ⥤ D) [F.OplaxMonoidal]

/-- The unit comparison of the opposite of an oplax monoidal functor. -/
@[simp]
theorem op_ε : ε F.op = (η F).op :=
  rfl

/-- The tensor comparison of the opposite of an oplax monoidal functor. -/
@[simp]
theorem op_μ (X Y : Cᵒᵖ) : μ F.op X Y = (δ F (unop X) (unop Y)).op :=
  rfl

end

section

variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The counit comparison of the opposite of a lax monoidal functor. -/
@[simp]
theorem op_η : η F.op = (ε F).op :=
  rfl

/-- The cotensor comparison of the opposite of a lax monoidal functor. -/
@[simp]
theorem op_δ (X Y : Cᵒᵖ) : δ F.op X Y = (μ F (unop X) (unop Y)).op :=
  rfl

end

end CategoryTheory.Functor

namespace CategoryTheory.MonoidalOpposite

universe v u

variable (C : Type u) [Category.{v} C]

/-- The equivalence between `((Cᵒᵖ)ᴹᵒᵖ)ᵒᵖᴹᵒᵖ` and `C`, removing the four wrappers. -/
@[expose, simps]
def opMopOpMopEquivalence : (Cᵒᵖᴹᵒᵖ)ᵒᵖᴹᵒᵖ ≌ C where
  functor :=
    { obj X := unop (unmop (unop (unmop X)))
      map f := f.unmop.unop.unmop.unop }
  inverse :=
    { obj X := mop (op (mop (op X)))
      map f := f.op.mop.op.mop }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable [MonoidalCategory C]

/-- Removing the four wrappers from `((Cᵒᵖ)ᴹᵒᵖ)ᵒᵖᴹᵒᵖ` is strong monoidal with identity comparison
morphisms: the tensor product is reversed twice. -/
instance opMopOpMopEquivalenceFunctorMonoidal :
    (opMopOpMopEquivalence C).functor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      μIso_hom_natural_left _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      μIso_hom_natural_right _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      -- The associator and unitors of `((Cᵒᵖ)ᴹᵒᵖ)ᵒᵖᴹᵒᵖ` are, after removing the wrappers,
      -- definitionally those of `C`; `change` exposes this so that only identities remain.
      associativity X Y Z := by
        change 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ (unop (unmop (unop (unmop X)))) (unop (unmop (unop (unmop Y))))
          (unop (unmop (unop (unmop Z))))).hom = (α_ _ _ _).hom ≫ _ ◁ 𝟙 _ ≫ 𝟙 _
        simp
      left_unitality X := by
        change (λ_ _).hom = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ (unop (unmop (unop (unmop X))))).hom
        simp
      right_unitality X := by
        change (ρ_ _).hom = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ (unop (unmop (unop (unmop X))))).hom
        simp }

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The unit comparison of the removal of the four wrappers is the identity. -/
@[simp]
theorem opMopOpMopEquivalence_functor_ε : ε (opMopOpMopEquivalence C).functor = 𝟙 (𝟙_ C) :=
  rfl

/-- The tensor comparison of the removal of the four wrappers is the identity. -/
@[simp]
theorem opMopOpMopEquivalence_functor_μ (X Y : (Cᵒᵖᴹᵒᵖ)ᵒᵖᴹᵒᵖ) :
    μ (opMopOpMopEquivalence C).functor X Y =
      𝟙 ((opMopOpMopEquivalence C).functor.obj X ⊗ (opMopOpMopEquivalence C).functor.obj Y) :=
  rfl

/-- The counit comparison of the removal of the four wrappers is the identity. -/
@[simp]
theorem opMopOpMopEquivalence_functor_η : η (opMopOpMopEquivalence C).functor = 𝟙 (𝟙_ C) :=
  rfl

/-- The cotensor comparison of the removal of the four wrappers is the identity. -/
@[simp]
theorem opMopOpMopEquivalence_functor_δ (X Y : (Cᵒᵖᴹᵒᵖ)ᵒᵖᴹᵒᵖ) :
    δ (opMopOpMopEquivalence C).functor X Y =
      𝟙 ((opMopOpMopEquivalence C).functor.obj X ⊗ (opMopOpMopEquivalence C).functor.obj Y) :=
  rfl

end CategoryTheory.MonoidalOpposite
