/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.Valuation
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Units

/-!
# The stalks of the presentation-limit presheaf are local

Let `x` be a point of `X = Spa(A,A⁺)` and let `v_x` be the valuation on the stalk `𝒪_{X,x}` of
the presentation-limit presheaf constructed in `Stalk.Valuation`. This file proves that a germ is a
unit exactly when `v_x` does not vanish on it. Since the support of `v_x` is a prime ideal, the
nonunits of `𝒪_{X,x}` then form an ideal: the stalk is a local ring whose maximal ideal is the
support of `v_x`. Consequently `v_x` factors through the residue field of `𝒪_{X,x}`, which is the
form in which the valuations at the points of a pre-adic space are recorded.

The nontrivial direction is Wedhorn's argument in §8.1. A germ `f` off the support of `v_x` comes
from an element of the coordinate ring `A⟨T/s⟩` of some rational neighbourhood `R(T/s)` of `x`
which does not vanish at the point of `Spa (A⟨T/s⟩, A_U⁺)` over `x`. By
`notMem_supp_iff_exists_isUnit_ringHomOfRationalSubsetSubset` it becomes a unit in the coordinate
ring of a smaller rational neighbourhood, so its germ is a unit.

As in `Stalk.Valuation`, `A⁺` is assumed to consist of power-bounded elements and to contain the
ring of definition of the chosen pair of definition.

## Main results

* `TauCeti.ValuationSpectrum.isUnit_iff_notMem_supp_presentationLimitStalkValuation`: a germ is a
  unit exactly when it lies outside the support of the stalk valuation.
* `TauCeti.ValuationSpectrum.isLocalRing_stalk_presentationLimitPresheafInCommRingCat`: every stalk
  of the presentation-limit presheaf is a local ring.
* `TauCeti.ValuationSpectrum.supp_presentationLimitStalkValuation`: its maximal ideal is the
  support of the stalk valuation.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitStalkResidueValuation`: the valuation on the residue
  field of the stalk through which the stalk valuation factors, characterised by
  `comap_residue_presentationLimitStalkResidueValuation` and
  `eq_presentationLimitStalkResidueValuation`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.2.
-/

namespace TauCeti.ValuationSpectrum

open AlgebraicGeometry CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- A germ that does not vanish at `x` is a unit: it becomes a unit in the coordinate ring of a
small enough rational neighbourhood of `x`. -/
private theorem isUnit_of_notMem_supp_presentationLimitStalkValuation {x : spa Aplus}
    {t : (presentationLimitPresheafInCommRingCat P Aplus).stalk x}
    (ht : t ∉ (presentationLimitStalkValuation hAplus hP x).supp) : IsUnit t := by
  obtain ⟨p, hp, hx, a, rfl⟩ := exists_presentationLimitRationalGerm_eq hAplus x t
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  -- `a` does not vanish at the point of `Spa (A⟨p⟩, A_p⁺)` over `x`
  have ha : (Presentation.completionLocObjCommRingCatIso p).hom a ∉
      supp ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
        p.hasDenominatorPower).symm ⟨x, mem_spaBasicOpen.mp hx⟩).1 := by
    refine fun hmem ↦ ht ?_
    have hle : (rationalLocalizationPoint hP p x hx).toValuativeRel.vle a 0 := by
      rw [rationalLocalizationPoint_def, comap_vle, map_zero]
      exact (mem_supp_iff _ _).mp hmem
    rw [← comap_presentationLimitRationalGerm_presentationLimitStalkValuation hAplus hP p hp x hx,
      comap_vle, map_zero] at hle
    exact (mem_supp_iff _ _).mpr hle
  -- so it becomes a unit on a smaller rational neighbourhood `R(q)` of `x`
  obtain ⟨q, hq, hxq, hsub, hunit⟩ :=
    (notMem_supp_iff_exists_isUnit_ringHomOfRationalSubsetSubset P Aplus hP hAplus p.num p.den hp
      _ p.hasDenominatorPower ⟨x, mem_spaBasicOpen.mp hx⟩ _).mp ha
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den :=
    spaBasicOpen_le_spaBasicOpen_iff.mpr hsub
  -- the restriction of `a` to `A⟨q⟩` is a unit, hence so is its germ
  have heq : (Presentation.completionLocObjCommRingCatIso q).hom
      (((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus hsub)).hom a) =
      ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower q.num q.den
        _ q.hasDenominatorPower hsub ((Presentation.completionLocObjCommRingCatIso p).hom a) := by
    rw [← CommRingCat.comp_apply,
      map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom,
      CommRingCat.comp_apply, CommRingCat.ofHom_apply]
  have hunit' := hunit.map (Presentation.completionLocObjCommRingCatIso q).inv.hom
  rw [← heq, Iso.hom_inv_id_apply] at hunit'
  rw [← presentationLimitRationalGerm_res hAplus p q hp hq h x (mem_spaBasicOpen.mpr hxq),
    CommRingCat.comp_apply]
  exact hunit'.map _

/-- **A germ is a unit exactly when the stalk valuation does not vanish on it**: an element of the
stalk at `x` of the presentation-limit presheaf is a unit if and only if it lies outside the
support of `presentationLimitStalkValuation`. -/
theorem isUnit_iff_notMem_supp_presentationLimitStalkValuation {x : spa Aplus}
    (t : (presentationLimitPresheafInCommRingCat P Aplus).stalk x) :
    IsUnit t ↔ t ∉ (presentationLimitStalkValuation hAplus hP x).supp :=
  ⟨fun ht hmem ↦ Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem _ hmem ht),
    isUnit_of_notMem_supp_presentationLimitStalkValuation hAplus hP⟩

include hAplus hP in
/-- **The stalks of the presentation-limit presheaf are local rings**: its nonunits form the
support of the stalk valuation, which is a proper ideal. -/
theorem isLocalRing_stalk_presentationLimitPresheafInCommRingCat (x : spa Aplus) :
    IsLocalRing ((presentationLimitPresheafInCommRingCat P Aplus).stalk x) := by
  have hnonunit (t) : t ∈ nonunits _ ↔ t ∈ (presentationLimitStalkValuation hAplus hP x).supp := by
    rw [mem_nonunits_iff, isUnit_iff_notMem_supp_presentationLimitStalkValuation, not_not]
  -- the stalk is nontrivial, since `1` lies outside the proper ideal `supp v_x`
  have : Nontrivial ((presentationLimitPresheafInCommRingCat P Aplus).stalk x) :=
    nontrivial_of_ne 0 1 fun h ↦ (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance)
      (h ▸ zero_mem (presentationLimitStalkValuation hAplus hP x).supp)
  exact .of_nonunits_add fun a b ha hb ↦ (hnonunit _).mpr <|
    add_mem ((hnonunit a).mp ha) ((hnonunit b).mp hb)

/-- **The maximal ideal of the stalk is the support of the stalk valuation**: the valuation `v_x`
on the stalk at `x` vanishes exactly on the maximal ideal. -/
theorem supp_presentationLimitStalkValuation (x : spa Aplus) :
    letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
    (presentationLimitStalkValuation hAplus hP x).supp =
      IsLocalRing.maximalIdeal ((presentationLimitPresheafInCommRingCat P Aplus).stalk x) := by
  let _ := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
  ext t
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_notMem_supp_presentationLimitStalkValuation, not_not]

/-- **The stalk valuation on the residue field**: the point of the valuation spectrum of the
residue field of the stalk at `x` through which `presentationLimitStalkValuation` factors. It
exists because the stalk valuation vanishes on the maximal ideal. -/
noncomputable def presentationLimitStalkResidueValuation (x : spa Aplus) :
    letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
    Spv (IsLocalRing.ResidueField ((presentationLimitPresheafInCommRingCat P Aplus).stalk x)) :=
  letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
  -- `IsLocalRing.ResidueField R` is by definition `R ⧸ maximalIdeal R`
  quotientLift _ (supp_presentationLimitStalkValuation hAplus hP x).ge

/-- **The stalk valuation factors through the residue field**: pulled back along the residue map,
`presentationLimitStalkResidueValuation` is the stalk valuation at `x`. -/
@[simp]
theorem comap_residue_presentationLimitStalkResidueValuation (x : spa Aplus) :
    letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
    comap (IsLocalRing.residue ((presentationLimitPresheafInCommRingCat P Aplus).stalk x))
        (presentationLimitStalkResidueValuation hAplus hP x) =
      presentationLimitStalkValuation hAplus hP x :=
  -- `IsLocalRing.residue` is by definition `Ideal.Quotient.mk` (see `IsLocalRing.residue_def`)
  comap_quotientLift _ _

/-- **Uniqueness of the residue-field valuation**: a point of the valuation spectrum of the residue
field of the stalk at `x` which pulls back to the stalk valuation is
`presentationLimitStalkResidueValuation`. -/
theorem eq_presentationLimitStalkResidueValuation {x : spa Aplus}
    (w : letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
      Spv (IsLocalRing.ResidueField ((presentationLimitPresheafInCommRingCat P Aplus).stalk x)))
    (hw : letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
      comap (IsLocalRing.residue ((presentationLimitPresheafInCommRingCat P Aplus).stalk x)) w =
        presentationLimitStalkValuation hAplus hP x) :
    w = presentationLimitStalkResidueValuation hAplus hP x :=
  letI := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
  comap_injective IsLocalRing.residue_surjective <|
    hw.trans (comap_residue_presentationLimitStalkResidueValuation hAplus hP x).symm

end

end TauCeti.ValuationSpectrum
