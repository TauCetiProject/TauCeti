/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor

/-!
# Maps of blowups and flat base change

A morphism along which one centre is the inverse image of another induces a canonical map
of blowups. These maps respect identities and composition. For flat morphisms the resulting
square is cartesian; in particular a blowup restricts to the blowup of the restricted centre
on every open subscheme. The equality of ideal sheaves in the interface permits using any
specified representative of the inverse image, without transporting the blowup carrier.

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

/-- The canonical map of blowups when the centre on the source is the inverse image of the
centre on the target. No flatness or finiteness hypothesis is needed to construct the map. -/
def blowupMap (J : Y.IdealSheafData) (I : X.IdealSheafData) (f : X ⟶ Y)
    (h : J.comap f = I) : I.blowup ⟶ J.blowup :=
  J.blowupLift (I.blowupToBase ≫ f) (by
    rw [comap_comp, h]
    exact I.isEffectiveCartier_comap_blowupToBase)

/-- The canonical map of blowups lies over the specified map of bases. -/
@[reassoc (attr := simp)]
theorem blowupMap_blowupToBase (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) (h : J.comap f = I) :
    J.blowupMap I f h ≫ J.blowupToBase = I.blowupToBase ≫ f :=
  J.blowupLift_blowupToBase _ _

/-- The map of blowups induced by the identity is the identity. -/
@[simp]
theorem blowupMap_id (I : X.IdealSheafData) :
    I.blowupMap I (𝟙 X) (I.comap_id) = 𝟙 _ := by
  apply I.blowup_hom_ext
  · simp
  · simpa using I.isEffectiveCartier_comap_blowupToBase

/-- Canonical maps of blowups respect composition of maps of bases. -/
@[reassoc (attr := simp)]
theorem blowupMap_comp (K : Z.IdealSheafData) (J : Y.IdealSheafData)
    (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : J.comap f = I) (hg : K.comap g = J) :
    J.blowupMap I f hf ≫ K.blowupMap J g hg =
      K.blowupMap I (f ≫ g) (by rw [comap_comp, hg, hf]) := by
  apply K.blowup_hom_ext
  · simp
  · rw [Category.assoc, blowupMap_blowupToBase, blowupMap_blowupToBase_assoc,
      comap_comp, comap_comp, hg, hf]
    exact I.isEffectiveCartier_comap_blowupToBase

/-- On the flat base change of a blowup, the inverse image of the centre is Cartier. -/
private theorem isEffectiveCartier_comap_pullback_fst (J : Y.IdealSheafData)
    (I : X.IdealSheafData) (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    (I.comap (pullback.fst f J.blowupToBase)).IsEffectiveCartier := by
  rw [← h, ← comap_comp, pullback.condition, comap_comp]
  exact J.isEffectiveCartier_comap_blowupToBase.comap _

/-- The blowup of the inverse-image centre is canonically the base change of the blowup
along a flat morphism. -/
def blowupBaseChangeIso (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    I.blowup ≅ pullback f J.blowupToBase where
  hom := pullback.lift I.blowupToBase (J.blowupMap I f h)
    (J.blowupMap_blowupToBase I f h).symm
  inv := I.blowupLift _ (isEffectiveCartier_comap_pullback_fst J I f h)
  hom_inv_id := by
    apply I.blowup_hom_ext
    · simp
    · simpa using I.isEffectiveCartier_comap_blowupToBase
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · apply J.blowup_hom_ext
      · simp [pullback.condition]
      · simp only [Category.assoc, pullback.lift_snd, blowupMap_blowupToBase,
          blowupLift_blowupToBase_assoc, comap_comp, h]
        exact isEffectiveCartier_comap_pullback_fst J I f h

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_hom_fst (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    (J.blowupBaseChangeIso I f h).hom ≫ pullback.fst _ _ = I.blowupToBase :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_hom_snd (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    (J.blowupBaseChangeIso I f h).hom ≫ pullback.snd _ _ = J.blowupMap I f h :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_inv_blowupToBase (J : Y.IdealSheafData)
    (I : X.IdealSheafData) (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    (J.blowupBaseChangeIso I f h).inv ≫ I.blowupToBase = pullback.fst _ _ :=
  (Iso.inv_comp_eq _).mpr (J.blowupBaseChangeIso_hom_fst I f h).symm

@[reassoc (attr := simp)]
theorem blowupBaseChangeIso_inv_blowupMap (J : Y.IdealSheafData)
    (I : X.IdealSheafData) (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    (J.blowupBaseChangeIso I f h).inv ≫ J.blowupMap I f h = pullback.snd _ _ :=
  (Iso.inv_comp_eq _).mpr (J.blowupBaseChangeIso_hom_snd I f h).symm

/-- Blowing up commutes with flat base change on arbitrary schemes. -/
theorem isPullback_blowupMap (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) [Flat f] (h : J.comap f = I) :
    IsPullback I.blowupToBase (J.blowupMap I f h) f J.blowupToBase :=
  .of_iso_pullback ⟨(J.blowupMap_blowupToBase I f h).symm⟩
    (J.blowupBaseChangeIso I f h) (J.blowupBaseChangeIso_hom_fst I f h)
    (J.blowupBaseChangeIso_hom_snd I f h)

/-- Restriction to an open subscheme gives an open immersion of blowups. -/
instance (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] (h : J.comap f = I) :
    IsOpenImmersion (J.blowupMap I f h) :=
  MorphismProperty.of_isPullback (J.isPullback_blowupMap I f h) inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData
