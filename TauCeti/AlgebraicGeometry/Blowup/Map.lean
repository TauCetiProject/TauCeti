/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback

/-!
# Functoriality of blowup maps and the flat base-change isomorphism

The canonical maps of blowups respect identities and composition, with transport along the
corresponding equalities of inverse-image ideals. For flat morphisms the comparison morphism
is an isomorphism; we package it with equations for both projections and its inverse.

## References

* The Stacks Project, Section 31.33, *Blowing up* (tag 01OF), especially Lemma 31.33.3
  (flat base change) and Lemma 31.33.5 (the universal property).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}}

/-- The map of blowups induced by the identity is transport along `comap_id`. -/
@[simp]
theorem blowupMap_id (I : X.IdealSheafData) :
    I.blowupMap (𝟙 X) = eqToHom (congrArg blowup I.comap_id) := by
  apply I.blowup_hom_ext
  · simpa using eqToHom_naturality (fun J : X.IdealSheafData ↦ J.blowupToBase) I.comap_id
  · rw [blowupMap_blowupToBase]
    exact I.isEffectiveCartier_comap_blowupToBase_comp (𝟙 X)

/-- Canonical maps of blowups respect composition of maps of bases. -/
@[reassoc]
theorem blowupMap_comp (K : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (K.comap g).blowupMap f ≫ K.blowupMap g =
      eqToHom (congrArg blowup (K.comap_comp f g).symm) ≫ K.blowupMap (f ≫ g) := by
  apply K.blowup_hom_ext
  · simp only [Category.assoc, blowupMap_blowupToBase, blowupMap_blowupToBase_assoc]
    simpa using congrArg (fun b ↦ b ≫ f ≫ g)
      (eqToHom_naturality (fun J : X.IdealSheafData ↦ J.blowupToBase)
        (K.comap_comp f g).symm)
  · rw [Category.assoc, blowupMap_blowupToBase, blowupMap_blowupToBase_assoc,
      comap_comp, comap_comp]
    exact ((K.comap g).comap f).isEffectiveCartier_comap_blowupToBase

/-- The blowup of the inverse-image centre is canonically the base change of the blowup
along a flat morphism. -/
def blowupBaseChangeIso (J : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    (J.comap f).blowup ≅ pullback f J.blowupToBase :=
  asIso (J.blowupBaseChangeHom f)

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_hom_fst (J : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    (J.blowupBaseChangeIso f).hom ≫ pullback.fst _ _ = (J.comap f).blowupToBase :=
  J.blowupBaseChangeHom_fst f

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_hom_snd (J : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    (J.blowupBaseChangeIso f).hom ≫ pullback.snd _ _ = J.blowupMap f :=
  J.blowupBaseChangeHom_snd f

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_inv_blowupToBase (J : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    (J.blowupBaseChangeIso f).inv ≫ (J.comap f).blowupToBase = pullback.fst _ _ :=
  (Iso.inv_comp_eq _).mpr (J.blowupBaseChangeIso_hom_fst f).symm

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_inv_blowupMap (J : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    (J.blowupBaseChangeIso f).inv ≫ J.blowupMap f = pullback.snd _ _ :=
  (Iso.inv_comp_eq _).mpr (J.blowupBaseChangeIso_hom_snd f).symm

end AlgebraicGeometry.Scheme.IdealSheafData
