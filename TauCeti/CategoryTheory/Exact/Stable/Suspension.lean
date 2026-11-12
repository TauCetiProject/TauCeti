/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Presentation

/-!
# Suspension on a Frobenius stable category

Let `E` be a Frobenius exact structure. For every object `X`, choose a conflation

`X ⟶ I(X) ⟶ ΣX`

with injective middle term. A morphism `f : X ⟶ Y` extends to a map `I(X) ⟶ I(Y)`, hence
induces a map `ΣX ⟶ ΣY`. Neither extension is unique in the original category, but any
two choices differ by a morphism through an injective, which is projective under the Frobenius
hypothesis. The induced map is therefore canonical in the projective stable quotient.

This file carries out that construction and obtains the additive suspension endofunctor of the
stable category. The loop functor and the proof that the two are quasi-inverse are developed
separately.

The choice of conflation is immaterial: the cokernel term of *any* relative injective
presentation of `X` is canonically isomorphic to `ΣX` in the stable category, naturally in `X`.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.suspensionPresentation`: the chosen injective conflation.
* `TauCeti.ExactStructure.IsFrobenius.suspensionObj`: its cokernel term `ΣX`.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspension`: the additive suspension endofunctor of
  the projective stable category.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj`: the comparison of the
  cokernel term of an arbitrary relative injective presentation with `ΣX`.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspensionIsoOfPresentations`: stable suspension is
  naturally the image of an endofunctor computed by a family of relative injective presentations.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspensionCompIsoOfFactorization`: such a comparison
  transported along a functor out of the stable category.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The chosen conflation `X ⟶ I(X) ⟶ ΣX` used to construct suspension. -/
noncomputable def suspensionPresentation (X : C) : E.InjectivePresentation X :=
  hE.enoughInjectives.injectivePresentation X

/-- The chosen injective object in the suspension presentation of `X`. -/
noncomputable abbrev suspensionInjective (X : C) : C :=
  (hE.suspensionPresentation X).I

/-- The suspension object `ΣX`, defined as the third term of the chosen injective conflation. -/
noncomputable abbrev suspensionObj (X : C) : C :=
  (hE.suspensionPresentation X).K

/-- The inflation `X ⟶ I(X)` in the chosen suspension presentation. -/
noncomputable abbrev suspensionInflation (X : C) : X ⟶ hE.suspensionInjective X :=
  (hE.suspensionPresentation X).i

/-- The deflation `I(X) ⟶ ΣX` in the chosen suspension presentation. -/
noncomputable abbrev suspensionDeflation (X : C) :
    hE.suspensionInjective X ⟶ hE.suspensionObj X :=
  (hE.suspensionPresentation X).p

/-- The inflation of the chosen suspension presentation of `X` is an inflation of `E`. -/
theorem isInflation_suspensionInflation (X : C) :
    E.IsInflation (hE.suspensionInflation X) :=
  E.isInflation_f (hE.suspensionPresentation X).conflation

/-- Suspension from the exact category to its stable quotient, built from the chosen injective
presentations. -/
public noncomputable def suspensionToStable : C ⥤ E.ProjectiveStableCategory :=
  E.suspensionToStableOfPresentations hE.suspensionPresentation
    (fun X ↦ hE.isProjective_I (hE.suspensionPresentation X))

/-- Suspension to the stable quotient sends `X` to the image of `ΣX`. -/
@[simp]
public theorem suspensionToStable_obj (X : C) :
    hE.suspensionToStable.obj X =
      E.projectiveStableFunctor.obj (hE.suspensionObj X) :=
  E.suspensionToStableOfPresentations_obj _ _ X

/-- Suspension to the stable quotient sends `f` to the image of the map induced between the
chosen injective presentations. -/
@[simp]
public theorem suspensionToStable_map {X Y : C} (f : X ⟶ Y) :
    hE.suspensionToStable.map f =
      eqToHom (hE.suspensionToStable_obj X) ≫
        E.projectiveStableFunctor.map
          ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f) ≫
          eqToHom (hE.suspensionToStable_obj Y).symm :=
  E.suspensionToStableOfPresentations_map _ _ f

public noncomputable instance suspensionToStable_additive : (hE.suspensionToStable).Additive := by
  rw [suspensionToStable]
  infer_instance

/-- The suspension of a projective object is projective. Thus suspension sends every object
killed by the stable quotient to another object killed by it. -/
theorem isProjective_suspensionObj {X : C} (hX : E.isProjective X) :
    E.isProjective (hE.suspensionObj X) := by
  let s := E.splittingOfInjective (hE.suspensionPresentation X).conflation
    ((hE.projective_iff_injective X).mp hX)
  exact E.isProjective.prop_of_retract
    ⟨s.s, hE.suspensionDeflation X, s.s_g⟩
    ((hE.projective_iff_injective _).mpr
      (hE.suspensionPresentation X).isInjective)

/-- The functor from the exact category to the stable category kills the projective stable ideal,
so it descends to an endofunctor of the stable category. -/
theorem suspensionToStable_kills_projectiveStableIdeal :
    E.projectiveStableIdeal ≤ (hE.suspensionToStable).kerIdeal := by
  intro X Y f hf
  rw [Functor.mem_kerIdeal_hom]
  obtain ⟨P, hP, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff E.isProjective _).mp
    ((ExactStructure.mem_projectiveStableIdeal_iff E).mp hf)
  rw [Functor.map_comp]
  have hzero : IsZero ((hE.suspensionToStable).obj P) := by
    rw [hE.suspensionToStable_obj P]
    exact (ExactStructure.isZero_projectiveStableFunctor_obj_iff E _).mpr
      (hE.isProjective_suspensionObj hP)
  rw [hzero.eq_of_tgt ((hE.suspensionToStable).map i) 0, zero_comp]

/-- The additive suspension endofunctor on the stable category of a Frobenius exact structure. -/
public noncomputable def stableSuspension :
    E.ProjectiveStableCategory ⥤ E.ProjectiveStableCategory :=
  E.projectiveStableIdeal.lift hE.suspensionToStable
    hE.suspensionToStable_kills_projectiveStableIdeal

/-- Stable suspension preserves addition of morphisms. -/
public noncomputable instance stableSuspension_additive : (hE.stableSuspension).Additive := by
  rw [stableSuspension]
  infer_instance

/-- On objects represented by `X`, stable suspension is represented by `ΣX`. -/
@[simp]
public theorem stableSuspension_obj_projectiveStableFunctor_obj (X : C) :
    hE.stableSuspension.obj (E.projectiveStableFunctor.obj X) =
      E.projectiveStableFunctor.obj (hE.suspensionObj X) :=
  by
    simp only [stableSuspension, CategoryTheory.Quotient.lift_obj_functor_obj,
      hE.suspensionToStable_obj]

/-- On represented morphisms, stable suspension is induced by the chosen injective
presentations. -/
@[simp]
public theorem stableSuspension_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    hE.stableSuspension.map (E.projectiveStableFunctor.map f) =
      eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj X) ≫
        E.projectiveStableFunctor.map
          ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f) ≫
          eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _
    (hE.stableSuspension_obj_projectiveStableFunctor_obj X)
    (hE.stableSuspension_obj_projectiveStableFunctor_obj Y)).2
    ((heq_of_eq (CategoryTheory.Quotient.lift_map_functor_map _ hE.suspensionToStable
        (fun _ _ _ _ hrel ↦ E.projectiveStableIdeal.map_eq_of_rel _
          hE.suspensionToStable_kills_projectiveStableIdeal hrel) f)).trans
      ((conj_eqToHom_iff_heq _ _ (hE.suspensionToStable_obj X)
        (hE.suspensionToStable_obj Y)).1 (hE.suspensionToStable_map f)))

/-- The cokernel term of an arbitrary relative injective presentation of `X` represents the
suspension `ΣX` in the projective stable category: the chosen presentation enjoys no privilege
there. -/
noncomputable def projectiveStableIsoSuspensionObj {X : C} (P : E.InjectivePresentation X) :
    E.projectiveStableFunctor.obj P.K ≅ E.projectiveStableFunctor.obj (hE.suspensionObj X) :=
  P.projectiveStableIso (hE.suspensionPresentation X) (hE.isProjective_I P)
    (hE.isProjective_I (hE.suspensionPresentation X))

/-- The comparison with the suspension is induced by the identity of the presented object. -/
@[simp]
theorem projectiveStableIsoSuspensionObj_hom {X : C} (P : E.InjectivePresentation X) :
    (hE.projectiveStableIsoSuspensionObj P).hom =
      E.projectiveStableFunctor.map (P.cokernelMap (hE.suspensionPresentation X) (𝟙 X)) :=
  P.projectiveStableIso_hom (hE.suspensionPresentation X) (hE.isProjective_I P)
    (hE.isProjective_I (hE.suspensionPresentation X))

/-- The inverse comparison with the suspension is the one induced in the other direction. -/
@[simp]
theorem projectiveStableIsoSuspensionObj_inv {X : C} (P : E.InjectivePresentation X) :
    (hE.projectiveStableIsoSuspensionObj P).inv =
      E.projectiveStableFunctor.map ((hE.suspensionPresentation X).cokernelMap P (𝟙 X)) :=
  P.projectiveStableIso_inv (hE.suspensionPresentation X) (hE.isProjective_I P)
    (hE.isProjective_I (hE.suspensionPresentation X))

/-- Representing the suspension by an arbitrary relative injective presentation is natural: it
carries the morphism induced by `f` on cokernel terms to the suspension of `f`. -/
@[reassoc]
theorem projectiveStableIsoSuspensionObj_hom_naturality {X Y : C}
    (P : E.InjectivePresentation X) (Q : E.InjectivePresentation Y) (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (P.cokernelMap Q f) ≫
        (hE.projectiveStableIsoSuspensionObj Q).hom =
      (hE.projectiveStableIsoSuspensionObj P).hom ≫
        E.projectiveStableFunctor.map
          ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f) :=
  ExactStructure.projectiveStableIso_hom_naturality
    P (hE.suspensionPresentation X) Q (hE.suspensionPresentation Y) (hE.isProjective_I P)
    (hE.isProjective_I (hE.suspensionPresentation X)) (hE.isProjective_I Q)
    (hE.isProjective_I (hE.suspensionPresentation Y)) f

/-- **Stable suspension from a family of presentations.** If every object `X` has a relative
injective presentation `P X` whose cokernel term represents `G.obj X` in the stable category,
naturally in `X`, then stable suspension is naturally the image of `G`. -/
noncomputable def stableSuspensionIsoOfPresentations (G : C ⥤ C)
    (P : ∀ X, E.InjectivePresentation X)
    (e : ∀ X, E.projectiveStableFunctor.obj (P X).K ≅ E.projectiveStableFunctor.obj (G.obj X))
    (he : ∀ {X Y : C} (f : X ⟶ Y),
      E.projectiveStableFunctor.map ((P X).cokernelMap (P Y) f) ≫ (e Y).hom =
        (e X).hom ≫ E.projectiveStableFunctor.map (G.map f)) :
    E.projectiveStableFunctor ⋙ hE.stableSuspension ≅ G ⋙ E.projectiveStableFunctor :=
  NatIso.ofComponents (fun X ↦
    eqToIso (hE.stableSuspension_obj_projectiveStableFunctor_obj X) ≪≫
      (hE.projectiveStableIsoSuspensionObj (P X)).symm ≪≫ e X) (fun {X Y} f ↦ by
    have h : (hE.projectiveStableIsoSuspensionObj (P X)).inv ≫
        E.projectiveStableFunctor.map ((P X).cokernelMap (P Y) f) =
          E.projectiveStableFunctor.map
            ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f) ≫
            (hE.projectiveStableIsoSuspensionObj (P Y)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc,
        ← hE.projectiveStableIsoSuspensionObj_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    simp only [Functor.comp_obj, Functor.comp_map,
      stableSuspension_map_projectiveStableFunctor_map, Iso.trans_hom, eqToIso.hom,
      Iso.symm_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← he, reassoc_of% h])

/-- The component of `stableSuspensionIsoOfPresentations` at `X` is the cokernel map induced by
the identity of `X`, from the chosen suspension presentation to the presentation `P X`, followed
by the comparison `e X` from `(P X).K` to `G.obj X`. -/
@[simp]
theorem stableSuspensionIsoOfPresentations_hom_app (G : C ⥤ C)
    (P : ∀ X, E.InjectivePresentation X)
    (e : ∀ X, E.projectiveStableFunctor.obj (P X).K ≅ E.projectiveStableFunctor.obj (G.obj X))
    (he : ∀ {X Y : C} (f : X ⟶ Y),
      E.projectiveStableFunctor.map ((P X).cokernelMap (P Y) f) ≫ (e Y).hom =
        (e X).hom ≫ E.projectiveStableFunctor.map (G.map f)) (X : C) :
    (hE.stableSuspensionIsoOfPresentations G P e he).hom.app X =
      eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj X) ≫
        E.projectiveStableFunctor.map
          ((hE.suspensionPresentation X).cokernelMap (P X) (𝟙 X)) ≫ (e X).hom := by
  simp [stableSuspensionIsoOfPresentations]

/-- The inverse component of `stableSuspensionIsoOfPresentations` at `X` is the inverse of the
comparison `e X`, followed by the cokernel map induced by the identity of `X`, from the
presentation `P X` to the chosen suspension presentation. -/
@[simp]
theorem stableSuspensionIsoOfPresentations_inv_app (G : C ⥤ C)
    (P : ∀ X, E.InjectivePresentation X)
    (e : ∀ X, E.projectiveStableFunctor.obj (P X).K ≅ E.projectiveStableFunctor.obj (G.obj X))
    (he : ∀ {X Y : C} (f : X ⟶ Y),
      E.projectiveStableFunctor.map ((P X).cokernelMap (P Y) f) ≫ (e Y).hom =
        (e X).hom ≫ E.projectiveStableFunctor.map (G.map f)) (X : C) :
    (hE.stableSuspensionIsoOfPresentations G P e he).inv.app X =
      (e X).inv ≫ E.projectiveStableFunctor.map
          ((P X).cokernelMap (hE.suspensionPresentation X) (𝟙 X)) ≫
        eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj X).symm := by
  simp [stableSuspensionIsoOfPresentations]

section Factorization

variable {D : Type u'} [Category.{v'} D] {F : E.ProjectiveStableCategory ⥤ D} {Q : C ⥤ D}
  (hF : E.projectiveStableFunctor ⋙ F = Q) {G : C ⥤ C} {T : D ⥤ D}

/-- **Transporting a suspension comparison along a factorization.** Let `F` be a functor out of
the stable category through which `Q` factors. If stable suspension is naturally the image of an
endofunctor `G`, and `Q` intertwines `G` with an endofunctor `T` of the target, then `F`
intertwines stable suspension with `T`. -/
noncomputable def stableSuspensionCompIsoOfFactorization
    (σ : E.projectiveStableFunctor ⋙ hE.stableSuspension ≅ G ⋙ E.projectiveStableFunctor)
    (β : G ⋙ Q ≅ Q ⋙ T) :
    hE.stableSuspension ⋙ F ≅ F ⋙ T :=
  CategoryTheory.Quotient.natIsoLift _ <|
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ F ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G (eqToIso hF) ≪≫ β ≪≫
      Functor.isoWhiskerRight (eqToIso hF.symm) T ≪≫ Functor.associator _ _ _

/-- On a represented object, the transported suspension comparison is the image of `σ`, followed
by `β`. -/
@[simp]
theorem stableSuspensionCompIsoOfFactorization_hom_app
    (σ : E.projectiveStableFunctor ⋙ hE.stableSuspension ≅ G ⋙ E.projectiveStableFunctor)
    (β : G ⋙ Q ≅ Q ⋙ T) (X : C) :
    (hE.stableSuspensionCompIsoOfFactorization hF σ β).hom.app
        (E.projectiveStableFunctor.obj X) =
      F.map (σ.hom.app X) ≫ eqToHom (by rw [← hF]; rfl) ≫ β.hom.app X ≫
        eqToHom (by rw [← hF]; rfl) := by
  simp [stableSuspensionCompIsoOfFactorization, eqToHom_map]

/-- On a represented object, the inverse transported suspension comparison is the inverse of `β`,
followed by the image of the inverse of `σ`. -/
@[simp]
theorem stableSuspensionCompIsoOfFactorization_inv_app
    (σ : E.projectiveStableFunctor ⋙ hE.stableSuspension ≅ G ⋙ E.projectiveStableFunctor)
    (β : G ⋙ Q ≅ Q ⋙ T) (X : C) :
    (hE.stableSuspensionCompIsoOfFactorization hF σ β).inv.app
        (E.projectiveStableFunctor.obj X) =
      eqToHom (by rw [← hF]; rfl) ≫ β.inv.app X ≫ eqToHom (by rw [← hF]; rfl) ≫
        F.map (σ.inv.app X) := by
  simp [stableSuspensionCompIsoOfFactorization, eqToHom_map]

end Factorization

end ExactStructure.IsFrobenius

end TauCeti
