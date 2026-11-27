/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Grothendieck structure on modules over a preadditive category

The additive Yoneda lemma shows that the representable modules separate morphisms. On a small
preadditive category their coproduct is a projective separator, and every module is a quotient of
a coproduct of copies of this separator. This gives enough projectives on any essentially small
preadditive category by passing to a small model.

Filtered colimits of additive functors are exact because they are computed pointwise in abelian
groups. Together with the separator this makes the module category Grothendieck abelian, so
Mathlib's Grothendieck category API supplies `Ext` in the value universe.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §3.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A morphism from the module represented by `X` to `F` corresponds to its value on `𝟙 X`. -/
def yonedaHomEquiv {X : C} {F : ModCat.{v} C} :
    ((yoneda C).obj X ⟶ F) ≃+ F.obj.obj (op X) := by
  refine
    { toFun := fun f ↦ f.hom.app (op X) (𝟙 X)
      invFun := fun x ↦ ObjectProperty.homMk
        { app Y := AddCommGrpCat.ofHom
            (AddMonoidHom.mk' (fun f ↦ F.obj.map f.op x) (by
              intro f g
              rw [op_add, Functor.map_add]
              exact AddCommGrpCat.hom_add_apply _ _ _) : (Y.unop ⟶ X) →+ F.obj.obj Y)
          naturality Y Z g := by
            ext (f : Y.unop ⟶ X)
            exact ConcreteCategory.congr_hom (F.obj.map_comp f.op g) x }
      left_inv := fun f ↦ ObjectProperty.hom_ext _ (preadditiveYoneda_obj_hom_ext ?_)
      right_inv := fun x ↦ ConcreteCategory.congr_hom (F.obj.map_id (op X)) x
      map_add' := fun _ _ ↦ rfl }
  exact ConcreteCategory.congr_hom (F.obj.map_id (op X)) (f.hom.app (op X) (𝟙 X))

/-- The Yoneda equivalence evaluates the morphism at the representing identity. -/
@[simp]
theorem yonedaHomEquiv_apply {X : C} {F : ModCat.{v} C} (f : (yoneda C).obj X ⟶ F) :
    yonedaHomEquiv f = f.hom.app (op X) (𝟙 X) :=
  (rfl)

/-- The morphism associated to an element acts on arrows by the module action. -/
theorem yonedaHomEquiv_symm_app_apply {X : C} {F : ModCat.{v} C} (x : F.obj.obj (op X))
    (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    (yonedaHomEquiv.symm x).hom.app Y f = F.obj.map f.op x :=
  (rfl)

/-- The Yoneda equivalence is natural in the target module. -/
theorem yonedaHomEquiv_comp {X : C} {F G : ModCat.{v} C}
    (f : (yoneda C).obj X ⟶ F) (g : F ⟶ G) :
    yonedaHomEquiv (f ≫ g) = g.hom.app (op X) (yonedaHomEquiv f) :=
  (rfl)

/-- The representable modules separate morphisms of modules. -/
theorem isSeparating_yoneda :
    (ObjectProperty.ofObj (yoneda C).obj).IsSeparating := by
  intro F G f g h
  apply ObjectProperty.hom_ext
  ext X x
  have hx := congrArg (yonedaHomEquiv (X := X.unop) (F := G))
    (h _ ⟨X.unop⟩ ((yonedaHomEquiv (X := X.unop) (F := F)).symm x))
  simpa only [yonedaHomEquiv_comp, AddEquiv.apply_symm_apply] using hx

/-- Modules on an essentially small preadditive category have a projective separator, obtained
from the coproduct of the representables of a small model. -/
theorem exists_projective_separator [EssentiallySmall.{w} C] :
    ∃ G : ModCat.{w} C, Projective G ∧ IsSeparator G := by
  let e := equivSmallModel.{w} C
  let : Preadditive (SmallModel.{w} C) := Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  have : e.inverse.Additive := e.fullyFaithfulInverse.additive_ofFullyFaithful
  have : e.functor.Additive := e.symm.additive_inverse_of_FullyFaithful
  have : e.functor.op.Additive := Functor.op_additive e.functor
  let E := e.op.symm.congrLeft (E := AddCommGrpCat.{w})
  let M : ModCat.{w} (SmallModel.{w} C) ≌ ModCat.{w} C := E.congrFullSubcategory (by
    ext F
    simp only [ObjectProperty.prop_inverseImage_iff, additiveFunctor_iff]
    -- The functor of the ambient equivalence acts by precomposition with `e.functor.op`.
    change (e.functor.op ⋙ F).Additive ↔ F.Additive
    exact ⟨fun _ ↦ e.functor.op.additive_of_full_essSurj_comp F, fun _ ↦ inferInstance⟩)
  let G := ∐ (yoneda (SmallModel.{w} C)).obj
  have hsep : IsSeparator G := isSeparating_yoneda.isSeparator_coproduct
  exact ⟨M.functor.obj G, (M.map_projective_iff G).2 inferInstance, hsep.of_equivalence M⟩

/-- For an essentially `w`-small source, natural transformations of modules with values in
`AddCommGrpCat.{w}` form `w`-small types. -/
instance [EssentiallySmall.{w} C] : LocallySmall.{w} (ModCat.{w} C) :=
  locallySmall_of_faithful
    ((additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).ι ⋙ (equivSmallModel.{w} C).op.congrLeft.functor)

/-- The module category has filtered colimits in the value universe. -/
instance : HasFilteredColimitsOfSize.{w, w} (ModCat.{w} C) where
  HasColimitsOfShape := inferInstance

/-- Filtered colimits in the module category are exact, even for a large source category. -/
noncomputable instance : AB5OfSize.{w, w} (ModCat.{w} C) where
  ofShape J _ _ := by
    let P := additiveFunctor Cᵒᵖ AddCommGrpCat.{w}
    have : PreservesFiniteLimits P.ι := ⟨fun _ _ _ ↦ inferInstance⟩
    exact HasExactColimitsOfShape.domain_of_functor J P.ι

/-- The category of modules over an essentially small preadditive category is Grothendieck
abelian in the value universe. -/
noncomputable instance [EssentiallySmall.{w} C] : IsGrothendieckAbelian.{w} (ModCat.{w} C) where
  hasSeparator := by
    obtain ⟨G, _, hG⟩ := exists_projective_separator (C := C)
    exact ⟨G, hG⟩

/-- Modules over an essentially small preadditive category admit epimorphisms from projectives. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (ModCat.{w} C) where
  presentation F := by
    obtain ⟨G, hG, hsep⟩ := exists_projective_separator (C := C)
    have (M : ModCat.{w} C) := hasCoproductsOfShape_of_small.{w} (ModCat.{w} C) (G ⟶ M)
    have := (isSeparator_iff_epi G).1 hsep F
    exact ⟨{ p := ∐ fun _ : G ⟶ F ↦ G, f := Sigma.desc fun f : G ⟶ F ↦ f }⟩

end TauCeti.ModCat
