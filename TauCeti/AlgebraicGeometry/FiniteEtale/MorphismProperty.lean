/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.CategoryTheory.MorphismProperty.Over
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import TauCeti.AlgebraicGeometry.FiniteEtale.Faithful

/-!
# Comparing the finite étale over categories

`TauCeti.FiniteEtaleScheme S` uses an object-property full subcategory of `Over S`, whereas
Mathlib's `(@IsFinite ⊓ @Etale).Over ⊤ S` uses a morphism-property over category. Their canonical
equivalence preserves the underlying schemes and morphisms and commutes with pullback along
every base morphism. In particular it commutes with restriction to any open subscheme.

This comparison transports base-change results between the two presentations. As an application,
faithfulness of dominant base change holds for `TauCeti.FiniteEtaleScheme.pullback` itself.
The base-change comparison lifts Mathlib's `MorphismProperty.Over.pullbackCompForgetIso`
through the fully faithful forgetful functor.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

/-- The canonical comparison with Mathlib's finite étale morphism-property over category.
Both functors leave the underlying schemes and morphisms unchanged. -/
abbrev equivOver (S : Scheme.{u}) :
    FiniteEtaleScheme S ≌ (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ S :=
  (MorphismProperty.overEquivFullSubcategory (@IsFinite ⊓ @Etale) S
    (finiteEtaleSchemeProperty S) (fun Y ↦ finiteEtaleSchemeProperty_iff Y)).symm

/-- The finite étale carrier comparison commutes with arbitrary base change, hence also with
restriction along an open immersion. Its components are identity maps on the pullback schemes. -/
noncomputable def pullbackCompEquivOver (f : T ⟶ S) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    pullback f ⋙ (equivOver T).functor ≅
      (equivOver S).functor ⋙ MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f := by
  letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  -- Compare the two functors in `Over T`, where Mathlib's pullback comparison applies.
  apply Functor.fullyFaithfulCancelRight
    (MorphismProperty.Over.forget (@IsFinite ⊓ @Etale) ⊤ T)
  refine eqToIso ?_ ≪≫
    (Functor.isoWhiskerLeft (equivOver S).functor
      (MorphismProperty.Over.pullbackCompForgetIso
        (P := @IsFinite ⊓ @Etale) (Q := ⊤) f)).symm ≪≫
    (Functor.associator _ _ _).symm
  calc
    _ = pullback f ⋙ (finiteEtaleSchemeProperty T).ι := by
      rw [Functor.assoc]
      simp
    _ = (finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f := pullback_comp_ι f
    _ = _ := by rw [← Functor.assoc]; simp

/-- The forward base-change comparison is the identity on the pullback scheme.
The `eqToHom` identifies the propositionally equal carrier presentations. -/
@[simp]
theorem pullbackCompEquivOver_hom_app_left (f : T ⟶ S) (X : FiniteEtaleScheme S) :
    ((pullbackCompEquivOver f).hom.app X).left = eqToHom (by
      have hS : ((equivOver S).functor.obj X).toComma = X.obj :=
        MorphismProperty.overEquivFullSubcategory_inverse_obj_toComma _ _ _ _ X
      have hT : ((equivOver T).functor.obj ((pullback f).obj X)).toComma =
          ((pullback f).obj X).obj :=
        MorphismProperty.overEquivFullSubcategory_inverse_obj_toComma _ _ _ _ _
      exact congrArg (fun Y : Over T ↦ Y.left)
        (hT.trans (congrArg (Over.pullback f).obj hS).symm)) := by
  -- View the scheme map through the forgetful functor to apply `Functor.map_preimage`.
  change ((MorphismProperty.Over.forget (@IsFinite ⊓ @Etale) ⊤ T).map
    ((pullbackCompEquivOver f).hom.app X)).left = _
  simp only [pullbackCompEquivOver, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    MorphismProperty.Over.pullbackCompForgetIso_inv_app_left, Functor.associator_inv_app,
    Over.comp_left, Over.eqToHom_left, Category.comp_id]
  exact Category.comp_id _

/-- The inverse base-change comparison is the identity on the pullback scheme.
The `eqToHom` identifies the propositionally equal carrier presentations. -/
@[simp]
theorem pullbackCompEquivOver_inv_app_left (f : T ⟶ S) (X : FiniteEtaleScheme S) :
    ((pullbackCompEquivOver f).inv.app X).left = eqToHom (by
      have hS : ((equivOver S).functor.obj X).toComma = X.obj :=
        MorphismProperty.overEquivFullSubcategory_inverse_obj_toComma _ _ _ _ X
      have hT : ((equivOver T).functor.obj ((pullback f).obj X)).toComma =
          ((pullback f).obj X).obj :=
        MorphismProperty.overEquivFullSubcategory_inverse_obj_toComma _ _ _ _ _
      exact congrArg (fun Y : Over T ↦ Y.left)
        ((congrArg (Over.pullback f).obj hS).trans hT.symm)) := by
  -- View the scheme map through the forgetful functor to apply `Functor.map_preimage`.
  change ((MorphismProperty.Over.forget (@IsFinite ⊓ @Etale) ⊤ T).map
    ((pullbackCompEquivOver f).inv.app X)).left = _
  simp only [pullbackCompEquivOver, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, eqToIso.inv, NatTrans.comp_app,
    eqToHom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    MorphismProperty.Over.pullbackCompForgetIso_hom_app_left, Functor.associator_hom_app,
    Over.comp_left, Over.eqToHom_left, Category.id_comp]
  exact Category.id_comp _

/-- Pullback of finite étale schemes along a dominant morphism is faithful, without any
reducedness assumption on the base. -/
instance faithful_pullback (f : T ⟶ S) [IsDominant f] : (pullback f).Faithful := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  have := f.finiteEtalePullback_faithful
  have : (pullback f ⋙ (equivOver T).functor).Faithful :=
    Functor.Faithful.of_iso (pullbackCompEquivOver f).symm
  exact Functor.Faithful.of_comp (pullback f) (equivOver T).functor

end TauCeti.FiniteEtaleScheme
