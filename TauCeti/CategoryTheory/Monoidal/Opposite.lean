/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
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

The same construction transposes trivializations. For functors `P : D ⥤ (Cᵒᵖ)ᴹᵒᵖ` and
`Q : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`, write `P'` and `Q'` for their opposite monoidal opposites followed by the
removal of the wrappers. A natural isomorphism `P ⋙ Q' ≅ 𝟭 D` gives, componentwise through
opposites, a natural isomorphism `𝟭 (Dᵒᵖ)ᴹᵒᵖ ≅ P' ⋙ Q`, which is monoidal when the given one is.
When `C = D`, the composite `(P ⋙ P') ⋙ (Q ⋙ Q')` is then trivialized as well: its middle
part `P' ⋙ Q` is trivialized by the transpose, and what remains is `P ⋙ Q'`. For the dual
functors of a rigid monoidal category, this turns the trivializations of the mixed double duals
into the statement that the double left and double right dual functors are mutually inverse.

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
  comparison morphisms;
* `CategoryTheory.Iso.opMopComp`: the transpose `𝟭 (Dᵒᵖ)ᴹᵒᵖ ≅ P' ⋙ Q` of a natural isomorphism
  `P ⋙ Q' ≅ 𝟭 D`, monoidal by `CategoryTheory.Iso.isMonoidal_opMopComp_hom`;
* `CategoryTheory.Iso.doubleCompDouble`: the resulting isomorphism `(P ⋙ P') ⋙ (Q ⋙ Q') ≅ 𝟭 C`,
  monoidal by `CategoryTheory.Iso.isMonoidal_doubleCompDouble_hom`.
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

namespace CategoryTheory.Iso

open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {P : D ⥤ Cᵒᵖᴹᵒᵖ} {Q : C ⥤ Dᵒᵖᴹᵒᵖ}

/-- The transpose of a natural isomorphism `P ⋙ Q' ≅ 𝟭 D`, where `Q'` is the opposite monoidal
opposite of `Q : C ⥤ (Dᵒᵖ)ᴹᵒᵖ` followed by the removal of the wrappers: the natural isomorphism
`𝟭 (Dᵒᵖ)ᴹᵒᵖ ≅ P' ⋙ Q`, where `P'` is formed from `P : D ⥤ (Cᵒᵖ)ᴹᵒᵖ` in the same way. Its
component at `Y` is the opposite of the component of the given isomorphism at the underlying
object of `Y`, as for Mathlib's `CategoryTheory.NatIso.op`. -/
def opMopComp (e : P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor ≅ 𝟭 D) :
    𝟭 Dᵒᵖᴹᵒᵖ ≅ (P.op.opMop ⋙ (opMopOpMopEquivalence C).functor) ⋙ Q :=
  NatIso.ofComponents (fun Y => (mopFunctor Dᵒᵖ).mapIso (e.app Y.unmop.unop).op)
    fun f => Quiver.Hom.unmop_inj (Quiver.Hom.unop_inj (e.hom.naturality f.unmop.unop).symm)

variable (e : P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor ≅ 𝟭 D)

/-- The components of `e.opMopComp` are the opposites of the components of `e.hom`. -/
@[simp]
theorem opMopComp_hom_app (Y : Dᵒᵖᴹᵒᵖ) :
    e.opMopComp.hom.app Y = (e.hom.app Y.unmop.unop).op.mop :=
  (rfl)

/-- The components of the inverse of `e.opMopComp` are the opposites of the components of
`e.inv`. -/
@[simp]
theorem opMopComp_inv_app (Y : Dᵒᵖᴹᵒᵖ) :
    e.opMopComp.inv.app Y = (e.inv.app Y.unmop.unop).op.mop :=
  (rfl)

section Square

variable {P Q : C ⥤ Cᵒᵖᴹᵒᵖ}

/-- For functors `P Q : C ⥤ (Cᵒᵖ)ᴹᵒᵖ`, write `P'` and `Q'` for their opposite monoidal opposites
followed by the removal of the wrappers. A natural isomorphism `P ⋙ Q' ≅ 𝟭 C` makes the functor
`P ⋙ P'`, which applies `P` twice, inverse on one side to `Q ⋙ Q'`: the middle composite
`P' ⋙ Q` is trivialized by the transpose `Iso.opMopComp`, and what remains is `P ⋙ Q'`. -/
def doubleCompDouble (e : P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence C).functor ≅ 𝟭 C) :
    (P ⋙ P.op.opMop ⋙ (opMopOpMopEquivalence C).functor) ⋙
      (Q ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence C).functor) ≅ 𝟭 C :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.opMopComp.symm _ ≪≫ Functor.leftUnitor _) ≪≫ e

variable (e : P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence C).functor ≅ 𝟭 C)

/-- The component of `e.doubleCompDouble` at `X`: apply `Q` to the inverse of `e` at the
underlying object of `P.obj X`, then apply `e` at `X`. -/
@[simp]
theorem doubleCompDouble_hom_app (X : C) :
    e.doubleCompDouble.hom.app X =
      (Q.map (e.inv.app (P.obj X).unmop.unop)).unmop.unop ≫ e.hom.app X :=
  -- Only the identity components of the coherence isomorphisms are removed.
  (Category.id_comp _).trans (((Category.id_comp _).trans (Category.comp_id _)) =≫ _)

/-- The component of the inverse of `e.doubleCompDouble` at `X`. -/
@[simp]
theorem doubleCompDouble_inv_app (X : C) :
    e.doubleCompDouble.inv.app X =
      e.inv.app X ≫ (Q.map (e.hom.app (P.obj X).unmop.unop)).unmop.unop :=
  -- Only the identity components of the coherence isomorphisms are removed.
  (Category.comp_id _).trans (_ ≫= ((Category.comp_id _).trans (Category.id_comp _)))

end Square

variable [MonoidalCategory C] [MonoidalCategory D]

/-- The unit comparison of `P' ⋙ Q`, with the wrappers removed, is the counit comparison of
`P ⋙ Q'`. -/
private theorem unmop_unop_ε_comp [P.OplaxMonoidal] [Q.LaxMonoidal] :
    (ε ((P.op.opMop ⋙ (opMopOpMopEquivalence C).functor) ⋙ Q)).unmop.unop =
      η (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor) := by
  rw [comp_ε, comp_ε, opMopOpMopEquivalence_functor_ε]
  -- `Category.id_comp` cannot be rewritten in place: the identity is typed through the removal
  -- of the wrappers, so it is applied under `congrArg`.
  refine (congrArg (fun g => (ε Q ≫ Q.map g).unmop.unop) (Category.id_comp _)).trans ?_
  rw [comp_η, comp_η, opMopOpMopEquivalence_functor_η]
  exact (_ ≫= Category.comp_id _).symm

/-- The tensor comparison of `P' ⋙ Q`, with the wrappers removed, is the cotensor comparison of
`P ⋙ Q'` at the underlying objects, in the reverse order. -/
private theorem unmop_unop_μ_comp [P.OplaxMonoidal] [Q.LaxMonoidal] (X Y : Dᵒᵖᴹᵒᵖ) :
    (μ ((P.op.opMop ⋙ (opMopOpMopEquivalence C).functor) ⋙ Q) X Y).unmop.unop =
      δ (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor) Y.unmop.unop
        (X.unmop.unop) := by
  rw [comp_μ, comp_μ, opMopOpMopEquivalence_functor_μ]
  -- As in `unmop_unop_ε_comp`, the identity is typed through the removal of the wrappers.
  refine (congrArg (fun g => (μ Q _ _ ≫ Q.map g).unmop.unop) (Category.id_comp _)).trans ?_
  rw [comp_δ, comp_δ, opMopOpMopEquivalence_functor_δ]
  exact (_ ≫= Category.comp_id _).symm

/-- The transpose of a monoidal natural isomorphism between strong monoidal functors is
monoidal. -/
instance isMonoidal_opMopComp_hom [P.Monoidal] [Q.Monoidal] [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal e.opMopComp.hom where
  -- Removing the wrappers, both conditions say that the components of `e.hom` are the oplax
  -- structure morphisms of `P ⋙ Q'`, which follows from monoidality of `e.hom` since `P ⋙ Q'`
  -- is strong monoidal. Removing the wrappers from a composite reverses it, definitionally.
  unit := by
    have h : e.hom.app (𝟙_ D) = η (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor) := by
      rw [← cancel_epi (ε (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor)),
        Functor.Monoidal.ε_η, NatTrans.IsMonoidal.unit, id_ε]
    exact Quiver.Hom.unmop_inj (Quiver.Hom.unop_inj
      ((Category.comp_id _).trans (h.trans unmop_unop_ε_comp.symm)))
  tensor X Y := by
    have h : e.hom.app (Y.unmop.unop ⊗ X.unmop.unop) =
        δ (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor) _ _ ≫
          (e.hom.app Y.unmop.unop ⊗ₘ e.hom.app X.unmop.unop) := by
      rw [← cancel_epi (μ (P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence D).functor) _ _),
        Functor.Monoidal.μ_δ_assoc, NatTrans.IsMonoidal.tensor, id_μ, Category.comp_id]
    exact Quiver.Hom.unmop_inj (Quiver.Hom.unop_inj
      ((Category.comp_id _).trans (h.trans (unmop_unop_μ_comp X Y =≫ _).symm)))

/-- `Iso.doubleCompDouble` is monoidal when the given isomorphism is: it is assembled from that
isomorphism, its transpose, and the coherence isomorphisms of composition of functors. -/
instance isMonoidal_doubleCompDouble_hom {P Q : C ⥤ Cᵒᵖᴹᵒᵖ} [P.Monoidal] [Q.Monoidal]
    (e : P ⋙ Q.op.opMop ⋙ (opMopOpMopEquivalence C).functor ≅ 𝟭 C) [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal e.doubleCompDouble.hom := by
  dsimp only [doubleCompDouble, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

end CategoryTheory.Iso
