/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Blowup.Pullback
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

## Main results

* `AlgebraicGeometry.Scheme.isIso_blowupToBase_singularLocus_restrict_smoothLocus`: the blowup is
  an isomorphism over the smooth locus.
* `AlgebraicGeometry.Scheme.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus` and
  `AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_eq_one_of_mem_smoothLocus`:
  one point of the blowup lies over each smooth point.
* `AlgebraicGeometry.Scheme.singularLocusBlowupIso`: the isomorphism of the blowups of two
  isomorphic relative curves along their singular subschemes, lying over the isomorphism of curves
  (`AlgebraicGeometry.Scheme.singularLocusBlowupIso_hom_blowupToBase`) and the unique such
  morphism (`AlgebraicGeometry.Scheme.eq_singularLocusBlowupIso_hom`).

## References

* The Stacks Project, Lemma 31.32.4, Tag 02OG (blowups away from their centre).
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
image of that of `Y`, as `e` is étale, and blowing up commutes with flat base change. It lies over
`e` (`singularLocusBlowupIso_hom_blowupToBase`), and is the unique morphism doing so
(`eq_singularLocusBlowupIso_hom`). -/
def singularLocusBlowupIso : (X.singularLocus R).blowup ≅ (Y.singularLocus R).blowup :=
  have : IsIso ((Y.singularLocus R).blowupMap e.hom) :=
    ((Y.singularLocus R).isPullback_blowupMap_of_flat e.hom).isIso_snd_of_isIso
  eqToIso (congrArg IdealSheafData.blowup (singularLocus_eq_comap_of_iso e he)) ≪≫
    asIso ((Y.singularLocus R).blowupMap e.hom)

/-- The isomorphism of blowups lies over the isomorphism of curves. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_hom_blowupToBase :
    (singularLocusBlowupIso e he).hom ≫ (Y.singularLocus R).blowupToBase =
      (X.singularLocus R).blowupToBase ≫ e.hom := by
  simp only [singularLocusBlowupIso, Iso.trans_hom, eqToIso.hom, asIso_hom, Category.assoc,
    IdealSheafData.blowupMap_blowupToBase]
  rw [IdealSheafData.eqToHom_blowupToBase_assoc (singularLocus_eq_comap_of_iso e he)]

/-- The inverse of the isomorphism of blowups lies over the inverse of the isomorphism of curves.
-/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_inv_blowupToBase :
    (singularLocusBlowupIso e he).inv ≫ (X.singularLocus R).blowupToBase =
      (Y.singularLocus R).blowupToBase ≫ e.inv := by
  rw [Iso.inv_comp_eq, singularLocusBlowupIso_hom_blowupToBase_assoc, Iso.hom_inv_id,
    Category.comp_id]

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
subschemes lying over `e` is `singularLocusBlowupIso e he`: the singular locus of `Y` pulls back
to the exceptional divisor of the blowup of `X`. -/
theorem eq_singularLocusBlowupIso_hom {h : (X.singularLocus R).blowup ⟶ (Y.singularLocus R).blowup}
    (hh : h ≫ (Y.singularLocus R).blowupToBase = (X.singularLocus R).blowupToBase ≫ e.hom) :
    h = (singularLocusBlowupIso e he).hom := by
  refine (Y.singularLocus R).blowup_hom_ext (hh.trans
    (singularLocusBlowupIso_hom_blowupToBase e he).symm) ?_
  rw [hh, IdealSheafData.comap_comp, ← singularLocus_eq_comap_of_iso e he]
  exact (X.singularLocus R).isEffectiveCartier_comap_blowupToBase

/-- The isomorphism of blowups induced by the identity is the identity. -/
theorem singularLocusBlowupIso_refl :
    singularLocusBlowupIso (R := R) (Iso.refl X) (Category.id_comp _) = Iso.refl _ :=
  Iso.ext (eq_singularLocusBlowupIso_hom _ _ (by simp)).symm

/-- The isomorphism of blowups induced by the inverse isomorphism is the inverse. -/
theorem singularLocusBlowupIso_symm (he' : e.inv ≫ X ↘ Spec (.of R) = Y ↘ Spec (.of R)) :
    singularLocusBlowupIso e.symm he' = (singularLocusBlowupIso e he).symm :=
  Iso.ext (eq_singularLocusBlowupIso_hom _ _ (by simp)).symm

variable [Flat (Z ↘ Spec (.of R))] [LocallyOfFinitePresentation (Z ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Z ↘ Spec (.of R))] in
/-- The isomorphism of blowups induced by a composite of isomorphisms is the composite. -/
theorem singularLocusBlowupIso_trans (e' : Y ≅ Z)
    (he' : e'.hom ≫ Z ↘ Spec (.of R) = Y ↘ Spec (.of R))
    (hee' : (e ≪≫ e').hom ≫ Z ↘ Spec (.of R) = X ↘ Spec (.of R)) :
    singularLocusBlowupIso (e ≪≫ e') hee' =
      singularLocusBlowupIso e he ≪≫ singularLocusBlowupIso e' he' :=
  Iso.ext (eq_singularLocusBlowupIso_hom _ _ (by simp)).symm

end Iso

end AlgebraicGeometry.Scheme
