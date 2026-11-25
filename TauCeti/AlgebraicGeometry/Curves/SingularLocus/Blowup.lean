/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale

/-!
# Blowing up the singular subscheme of a relative curve

For a syntomic relative curve over an arbitrary commutative ring, blowing up the singular
subscheme is an isomorphism over the smooth locus. Thus modifications obtained by blowing up
the singular subscheme preserve the smooth part of the curve: two points of the blowup with the
same smooth image are equal, and exactly one point of the blowup lies over each smooth point.

An isomorphism `e : X ≅ Y` of relative curves over `Spec R` is étale, so it carries the singular
locus of `Y` back to that of `X`, and blowing up commutes with flat base change: `e` lifts to an
isomorphism of the blowups along the singular subschemes, the unique morphism lying over `e`.
More generally, base change of `X` along any ring homomorphism `R → R'` induces a canonical
morphism `singularLocusBlowupMap` between singular-locus blowups, which forms a cartesian square
when `R'` is flat over `R`.

## Main results

* `AlgebraicGeometry.Scheme.isIso_blowupToBase_singularLocus_restrict_smoothLocus` and
  `AlgebraicGeometry.Scheme.isIso_blowupToBase_singularLocus_of_smooth`: the blowup is an
  isomorphism over the smooth locus, and globally an isomorphism when the curve is smooth.
* `AlgebraicGeometry.Scheme.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus` and
  `AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_eq_one_of_mem_smoothLocus`:
  one point of the blowup lies over each smooth point.
* `AlgebraicGeometry.Scheme.singularLocusBlowupIso`: the isomorphism of the blowups of two
  isomorphic relative curves along their singular subschemes, lying over the isomorphism of curves
  (`AlgebraicGeometry.Scheme.singularLocusBlowupIso_hom_blowupToBase`) and the unique such
  morphism (`AlgebraicGeometry.Scheme.eq_singularLocusBlowupIso_hom`).
* `AlgebraicGeometry.Scheme.singularLocusBlowupMap` and
  `AlgebraicGeometry.Scheme.isPullback_singularLocusBlowupMap`: base-change morphism of
  singular-locus blowups along `Spec R' ⟶ Spec R`, forming a cartesian square when `R'` is `R`-flat.

## References

* The Stacks Project, Lemma 31.32.4, Tag 02OG (blowups away from their centre).
* The lift `singularLocusBlowupIso` of an isomorphism of curves to the blowups follows mo271's
  `blowupSingularLocusMap` in https://github.com/TauCetiProject/TauCeti/pull/42297 and
  https://github.com/TauCetiProject/TauCeti/pull/42356.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Blowing up the singular subscheme of a syntomic relative curve changes nothing over its
smooth locus. -/
theorem isIso_blowupToBase_singularLocus_restrict_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    IsIso ((X.singularLocus R).blowupToBase ∣_ (X ↘ Spec (.of R)).smoothLocus) := by
  apply IdealSheafData.isIso_blowupToBase_restrict_of_disjoint_support
  rw [X.support_singularLocus_eq_compl_smoothLocus]
  exact disjoint_compl_right

/-- **Blowing up the singular subscheme is injective over the smooth locus.** Two points of the
blowup of a syntomic relative curve along its singular subscheme with the same smooth image are
equal. -/
theorem eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] {b b' : (X.singularLocus R).blowup}
    (h : (X.singularLocus R).blowupToBase b = (X.singularLocus R).blowupToBase b')
    (hb : (X.singularLocus R).blowupToBase b ∈ (X ↘ Spec (.of R)).smoothLocus) : b = b' := by
  let U := (X ↘ Spec (.of R)).smoothLocus
  let f := (X.singularLocus R).blowupToBase
  have := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := R)
  have hb' : f b' ∈ U := h ▸ hb
  have := (f ∣_ U).homeomorph.injective (a₁ := ⟨b, hb⟩) (a₂ := ⟨b', hb'⟩)
    (Subtype.ext ((morphismRestrict_base_coe f U ⟨b, hb⟩).trans
      (h.trans (morphismRestrict_base_coe f U ⟨b', hb'⟩).symm)))
  exact congr(($this).val)

/-- **One point of the blowup lies over each smooth point.** Blowing up the singular subscheme of
a syntomic relative curve changes nothing over its smooth locus. -/
theorem natCard_preimage_blowupToBase_singularLocus_eq_one_of_mem_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] {x : X}
    (hx : x ∈ (X ↘ Spec (.of R)).smoothLocus) :
    Nat.card ((X.singularLocus R).blowupToBase ⁻¹' {x}) = 1 := by
  let f := (X.singularLocus R).blowupToBase
  have := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := R)
  obtain ⟨⟨b, hb⟩, hbx⟩ := (f ∣_ (X ↘ Spec (.of R)).smoothLocus).homeomorph.surjective ⟨x, hx⟩
  have hbx : f b = x := (morphismRestrict_base_coe f _ ⟨b, hb⟩).symm.trans congr(($hbx).val)
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨b, hbx⟩, fun b' ↦ Subtype.ext ?_⟩
  have hb' : f b'.val = x := b'.property
  exact X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus (hb'.trans hbx.symm)
    (by rwa [hb'])

/-! ### Isomorphisms of relative curves -/

noncomputable section Iso

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (Y ↘ Spec (.of R))] [LocallyOfFinitePresentation (Y ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of R))]
  (e : X ≅ Y) (he : e.hom ≫ Y ↘ Spec (.of R) = X ↘ Spec (.of R))

include he in
/-- An isomorphism of relative curves over `Spec R` carries the singular locus of the target back
to that of the source: an isomorphism is étale. -/
private theorem singularLocus_eq_comap_of_iso :
    X.singularLocus R = (Y.singularLocus R).comap e.hom :=
  have : e.hom.IsOver (Spec (.of R)) := ⟨he⟩
  singularLocus_eq_comap_of_etale e.hom

/-- An isomorphism `e : X ≅ Y` of relative curves over `Spec R` lifts to an isomorphism of the
blowups of `X` and `Y` along their singular subschemes: the singular locus of `X` is the inverse
image of that of `Y`, as `e` is étale, so this is `IdealSheafData.blowupIso`. It lies over `e`
(`singularLocusBlowupIso_hom_blowupToBase`), and is the unique morphism doing so
(`eq_singularLocusBlowupIso_hom`). This follows mo271's `blowupSingularLocusMap`
(https://github.com/TauCetiProject/TauCeti/pull/42297). -/
def singularLocusBlowupIso : (X.singularLocus R).blowup ≅ (Y.singularLocus R).blowup :=
  IdealSheafData.blowupIso e (singularLocus_eq_comap_of_iso e he)

/-- The isomorphism of blowups lies over the isomorphism of curves. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_hom_blowupToBase :
    (singularLocusBlowupIso e he).hom ≫ (Y.singularLocus R).blowupToBase =
      (X.singularLocus R).blowupToBase ≫ e.hom :=
  IdealSheafData.blowupIso_hom_blowupToBase _ _

/-- The inverse of the isomorphism of blowups lies over the inverse of the isomorphism of curves.
-/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_inv_blowupToBase :
    (singularLocusBlowupIso e he).inv ≫ (X.singularLocus R).blowupToBase =
      (Y.singularLocus R).blowupToBase ≫ e.inv :=
  IdealSheafData.blowupIso_inv_blowupToBase _ _

/-- The isomorphism of blowups lies over the isomorphism of curves, on points. -/
@[simp]
theorem blowupToBase_singularLocusBlowupIso_hom_apply (b : (X.singularLocus R).blowup) :
    (Y.singularLocus R).blowupToBase ((singularLocusBlowupIso e he).hom b) =
      e.hom ((X.singularLocus R).blowupToBase b) := by
  rw [← Scheme.Hom.comp_apply, singularLocusBlowupIso_hom_blowupToBase, Scheme.Hom.comp_apply]

/-- The inverse of the isomorphism of blowups lies over the inverse of the isomorphism of curves,
on points. -/
@[simp]
theorem blowupToBase_singularLocusBlowupIso_inv_apply (b : (Y.singularLocus R).blowup) :
    (X.singularLocus R).blowupToBase ((singularLocusBlowupIso e he).inv b) =
      e.inv ((Y.singularLocus R).blowupToBase b) := by
  rw [← Scheme.Hom.comp_apply, singularLocusBlowupIso_inv_blowupToBase, Scheme.Hom.comp_apply]

/-- **Uniqueness of the isomorphism of blowups.** Every morphism of the blowups along the singular
subschemes lying over `e` is `singularLocusBlowupIso e he` (`IdealSheafData.eq_blowupIso_hom`). -/
theorem eq_singularLocusBlowupIso_hom {h : (X.singularLocus R).blowup ⟶ (Y.singularLocus R).blowup}
    (hh : h ≫ (Y.singularLocus R).blowupToBase = (X.singularLocus R).blowupToBase ≫ e.hom) :
    h = (singularLocusBlowupIso e he).hom :=
  IdealSheafData.eq_blowupIso_hom _ _ hh

/-- The isomorphism of blowups induced by the identity is the identity. -/
@[simp]
theorem singularLocusBlowupIso_refl :
    singularLocusBlowupIso (R := R) (Iso.refl X) (Category.id_comp _) = Iso.refl _ :=
  IdealSheafData.blowupIso_refl _

/-- The isomorphism of blowups induced by the inverse isomorphism is the inverse. The
compatibility of `e.symm` with the structure morphisms is derived from `he`. -/
theorem singularLocusBlowupIso_symm :
    singularLocusBlowupIso e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, he]) =
      (singularLocusBlowupIso e he).symm :=
  IdealSheafData.blowupIso_symm e _

variable [Flat (Z ↘ Spec (.of R))] [LocallyOfFinitePresentation (Z ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Z ↘ Spec (.of R))] in
/-- The isomorphism of blowups induced by a composite of isomorphisms is the composite. The
compatibility of `e ≪≫ e'` with the structure morphisms is derived from `he` and `he'`. -/
theorem singularLocusBlowupIso_trans (e' : Y ≅ Z)
    (he' : e'.hom ≫ Z ↘ Spec (.of R) = Y ↘ Spec (.of R)) :
    singularLocusBlowupIso (e ≪≫ e') (by rw [Iso.trans_hom, Category.assoc, he', he]) =
      singularLocusBlowupIso e he ≪≫ singularLocusBlowupIso e' he' :=
  IdealSheafData.blowupIso_trans e _ e' _

end Iso

/-- For a smooth relative curve of relative dimension one, the singular subscheme is empty (`⊤`), so
blowing up the singular subscheme is an isomorphism. -/
instance isIso_blowupToBase_singularLocus_of_smooth
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    IsIso (X.singularLocus R).blowupToBase :=
  (X.singularLocus R).isIso_blowupToBase_iff.mpr
    (X.singularLocus_eq_top R ▸ IdealSheafData.isEffectiveCartier_top X)

/-! ### Base change of the singular-locus blowup -/

noncomputable section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  {X X' : Scheme.{u}} [X.Over (Spec (.of R))] [X'.Over (Spec (.of R'))] {g : X' ⟶ X}
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (X' ↘ Spec (.of R'))] [LocallyOfFinitePresentation (X' ↘ Spec (.of R'))]
  [PureRelativeDimension 1 (X' ↘ Spec (.of R'))]
  (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- Induced morphism `Bl_{Sing(X'/R')} X' ⟶ Bl_{Sing(X/R)} X` under base change of `X`. -/
def singularLocusBlowupMap : (X'.singularLocus R').blowup ⟶ (X.singularLocus R).blowup :=
  (X.singularLocus R).blowupLift ((X'.singularLocus R').blowupToBase ≫ g) (by
    rw [IdealSheafData.comap_comp, ← Scheme.singularLocus_eq_comap_of_isPullback H]
    exact (X'.singularLocus R').isEffectiveCartier_comap_blowupToBase)

/-- The base-change morphism of blowups lies over the base-change morphism of curves. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupMap_blowupToBase :
    singularLocusBlowupMap H ≫ (X.singularLocus R).blowupToBase =
      (X'.singularLocus R').blowupToBase ≫ g :=
  (X.singularLocus R).blowupLift_blowupToBase _ _

/-- The base-change morphism of blowups lies over `g`, on points. -/
@[simp]
theorem blowupToBase_singularLocusBlowupMap_apply (b : (X'.singularLocus R').blowup) :
    (X.singularLocus R).blowupToBase (singularLocusBlowupMap H b) =
      g ((X'.singularLocus R').blowupToBase b) := by
  rw [← Scheme.Hom.comp_apply, singularLocusBlowupMap_blowupToBase, Scheme.Hom.comp_apply]

/-- Every morphism of singular-locus blowups lying over `g` equals `singularLocusBlowupMap H`. -/
theorem eq_singularLocusBlowupMap
    {h : (X'.singularLocus R').blowup ⟶ (X.singularLocus R).blowup}
    (hh : h ≫ (X.singularLocus R).blowupToBase = (X'.singularLocus R').blowupToBase ≫ g) :
    h = singularLocusBlowupMap H :=
  (X.singularLocus R).eq_blowupLift _ hh

/-- The singular-locus blowup commutes with flat base change. -/
theorem isPullback_singularLocusBlowupMap [Module.Flat R R'] :
    IsPullback (X'.singularLocus R').blowupToBase (singularLocusBlowupMap H)
      g (X.singularLocus R).blowupToBase := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  have : Flat g := MorphismProperty.of_isPullback H.flip ‹_›
  suffices ∀ (J : X'.IdealSheafData) (_ : J = (X.singularLocus R).comap g)
      (hcart : ((X.singularLocus R).comap (J.blowupToBase ≫ g)).IsEffectiveCartier),
      IsPullback J.blowupToBase ((X.singularLocus R).blowupLift (J.blowupToBase ≫ g) hcart)
        g (X.singularLocus R).blowupToBase from
    this _ (Scheme.singularLocus_eq_comap_of_isPullback H) _
  rintro J rfl hcart
  rw [(X.singularLocus R).eq_blowupMap g ((X.singularLocus R).blowupLift_blowupToBase _ _)]
  exact (X.singularLocus R).isPullback_blowupMap_of_flat g

end BaseChange

/-- The blowup of a relative curve over a Noetherian ring along its singular subscheme is locally
Noetherian. -/
instance isLocallyNoetherian_blowup_singularLocus {R : Type u} [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) [X.Over (Spec (.of R))] [Flat (X ↘ Spec (.of R))]
    [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
    [PureRelativeDimension 1 (X ↘ Spec (.of R))] :
    IsLocallyNoetherian (X.singularLocus R).blowup :=
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of R))
  LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus R).blowupToBase

end AlgebraicGeometry.Scheme
