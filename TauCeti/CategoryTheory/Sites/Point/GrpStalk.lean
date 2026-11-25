/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Stalks of presheaves of groups at a point of a site

Let `Φ` be a point of a site `(C, J)` and `P` a presheaf of groups on `C`. Mathlib's fiber functor
`CategoryTheory.GrothendieckTopology.Point.presheafFiber` needs all colimits of size `w` in the
coefficient category, which Mathlib does not provide for `GrpCat`. The indexing category
`Φ.fiber.Elementsᵒᵖ` is filtered and finally small, so `GrpCat` has colimits of this shape
(`GrpCat.FilteredColimits.colimitCoconeIsColimit`) and the forgetful functor preserves them. The
stalk `Φ.GrpStalk P` of the underlying presheaf of sets is therefore the underlying set of the
colimit of `P` in `GrpCat` (`Φ.grpStalkMulEquiv P`), and germs are group homomorphisms.

## Main definitions

* `Φ.GrpStalk P`: the stalk of the presheaf of sets underlying `P`, with its `Group` instance.
* `Φ.grpStalkMulEquiv P`: the stalk is the colimit of `P` in `GrpCat`.
* `Φ.grpGerm P X x`: the germ homomorphism `P.obj (op X) →* Φ.GrpStalk P` at `x : Φ.fiber.obj X`.
* `Φ.grpStalkMap f`: the homomorphism of stalks induced by a morphism of presheaves of groups.
-/

public section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J)

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ GrpCat.{w} :=
  have : HasColimitsOfShape (FinallySmall.FilteredFinalModel.{w} Φ.fiber.Elementsᵒᵖ) GrpCat.{w} :=
    ⟨fun F ↦ HasColimit.mk ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit.{w, w} F⟩⟩
  Functor.Final.hasColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _)

variable (P : Cᵒᵖ ⥤ GrpCat.{w})

/-- The stalk at `Φ` of the presheaf of sets underlying a presheaf of groups `P`. -/
abbrev GrpStalk : Type w := Φ.presheafFiber.obj (P ⋙ forget GrpCat)

/-- The stalk of the presheaf of sets underlying `P` is the underlying set of the colimit of `P`
in `GrpCat`, because the forgetful functor preserves filtered colimits. -/
noncomputable def grpStalkEquiv :
    Φ.GrpStalk P ≃ ↑(colimit ((Functor.Elements.π Φ.fiber).op ⋙ P) : GrpCat.{w}) :=
  have := FinallySmall.preservesColimitsOfShape_of_isFiltered.{w} Φ.fiber.Elementsᵒᵖ
    (forget GrpCat.{w})
  (preservesColimitIso (forget GrpCat) ((Functor.Elements.π Φ.fiber).op ⋙ P)).toEquiv.symm

/-- **The stalk of a presheaf of groups is a group**, with the group structure of the colimit
in `GrpCat`. -/
noncomputable instance : Group (Φ.GrpStalk P) := (Φ.grpStalkEquiv P).group

/-- The stalk of a presheaf of groups is isomorphic, as a group, to its colimit in `GrpCat`. -/
noncomputable def grpStalkMulEquiv :
    Φ.GrpStalk P ≃* ↑(colimit ((Functor.Elements.π Φ.fiber).op ⋙ P) : GrpCat.{w}) :=
  (Φ.grpStalkEquiv P).mulEquiv

/-- The comparison with the colimit in `GrpCat` sends germs to the colimit injections. -/
theorem grpStalkMulEquiv_toPresheafFiber (X : C) (x : Φ.fiber.obj X) (a : P.obj (op X)) :
    Φ.grpStalkMulEquiv P (Φ.toPresheafFiber X x (P ⋙ forget GrpCat) a) =
      colimit.ι ((Functor.Elements.π Φ.fiber).op ⋙ P) (op (Φ.fiber.elementsMk X x)) a := by
  have := FinallySmall.preservesColimitsOfShape_of_isFiltered.{w} Φ.fiber.Elementsᵒᵖ
    (forget GrpCat.{w})
  exact ConcreteCategory.congr_hom (ι_preservesColimitIso_inv (forget GrpCat)
    ((Functor.Elements.π Φ.fiber).op ⋙ P) (op (Φ.fiber.elementsMk X x))) a

/-- The germ at `x : Φ.fiber.obj X` of sections of `P` over `X`, as a group homomorphism. -/
@[expose]
noncomputable def grpGerm (X : C) (x : Φ.fiber.obj X) : P.obj (op X) →* Φ.GrpStalk P where
  toFun a := Φ.toPresheafFiber X x (P ⋙ forget GrpCat) a
  map_one' := (grpStalkMulEquiv Φ P).injective <| by
    simp only [map_one, grpStalkMulEquiv_toPresheafFiber]
  map_mul' a b := (grpStalkMulEquiv Φ P).injective <| by
    simp only [map_mul, grpStalkMulEquiv_toPresheafFiber]

/-- The germ homomorphism is the germ map of the underlying presheaf of sets. -/
theorem grpGerm_apply (X : C) (x : Φ.fiber.obj X) (a : P.obj (op X)) :
    Φ.grpGerm P X x a = Φ.toPresheafFiber X x (P ⋙ forget GrpCat) a :=
  rfl

/-- Germs are compatible with restriction. -/
theorem grpGerm_map {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (a : P.obj (op Y)) :
    Φ.grpGerm P X x (P.map f.op a) = Φ.grpGerm P Y (Φ.fiber.map f x) a :=
  Φ.toPresheafFiber_w_apply f x (P ⋙ forget GrpCat) a

/-- Every element of the stalk is a germ. -/
theorem exists_grpGerm_eq (p : Φ.GrpStalk P) :
    ∃ (X : C) (x : Φ.fiber.obj X) (a : P.obj (op X)), Φ.grpGerm P X x a = p := by
  obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P ⋙ forget GrpCat) p
  exact ⟨X, x, a, rfl⟩

/-- Any two elements of the stalk are germs at a common point. -/
theorem exists_grpGerm_eq₂ (p q : Φ.GrpStalk P) :
    ∃ (X : C) (x : Φ.fiber.obj X) (a b : P.obj (op X)),
      Φ.grpGerm P X x a = p ∧ Φ.grpGerm P X x b = q := by
  obtain ⟨X, x, a, b, rfl, rfl⟩ :=
    Φ.toPresheafFiber_jointly_surjective₂ (P := P ⋙ forget GrpCat) p q
  exact ⟨X, x, a, b, rfl, rfl⟩

/-- Group homomorphisms out of the stalk agree if they agree on germs. -/
theorem grpStalk_hom_ext {M : Type*} [Monoid M] {φ ψ : Φ.GrpStalk P →* M}
    (h : ∀ (X : C) (x : Φ.fiber.obj X) (a : P.obj (op X)),
      φ (Φ.grpGerm P X x a) = ψ (Φ.grpGerm P X x a)) : φ = ψ :=
  MonoidHom.ext fun p ↦ by
    obtain ⟨X, x, a, rfl⟩ := Φ.exists_grpGerm_eq P p
    exact h X x a

variable {P} {Q R : Cᵒᵖ ⥤ GrpCat.{w}}

/-- The homomorphism of stalks induced by a morphism of presheaves of groups. -/
noncomputable def grpStalkMap (f : P ⟶ Q) : Φ.GrpStalk P →* Φ.GrpStalk Q :=
  (grpStalkMulEquiv Φ Q).symm.toMonoidHom.comp <|
    (colimMap (Functor.whiskerLeft (Functor.Elements.π Φ.fiber).op f)).hom.comp
      (grpStalkMulEquiv Φ P).toMonoidHom

/-- `Φ.grpStalkMap f` sends germs to germs. -/
@[simp]
theorem grpStalkMap_grpGerm (f : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) (a : P.obj (op X)) :
    Φ.grpStalkMap f (Φ.grpGerm P X x a) = Φ.grpGerm Q X x (f.app _ a) := by
  simp only [grpStalkMap, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, grpGerm_apply, grpStalkMulEquiv_toPresheafFiber,
    MulEquiv.symm_apply_eq]
  exact ConcreteCategory.congr_hom
    (ι_colimMap (Functor.whiskerLeft (Functor.Elements.π Φ.fiber).op f)
      (op (Φ.fiber.elementsMk X x))) a

/-- The identity of a presheaf of groups induces the identity of its stalk. -/
@[simp]
theorem grpStalkMap_id : Φ.grpStalkMap (𝟙 P) = MonoidHom.id _ :=
  Φ.grpStalk_hom_ext P fun X x a ↦ by simp

/-- Taking stalks of presheaves of groups is functorial. -/
@[simp]
theorem grpStalkMap_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    Φ.grpStalkMap (f ≫ g) = (Φ.grpStalkMap g).comp (Φ.grpStalkMap f) :=
  Φ.grpStalk_hom_ext P fun X x a ↦ by simp

end CategoryTheory.GrothendieckTopology.Point
