/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison

/-!
# Points on completed rational localizations

A point of a rational subset of `Spa(A,A⁺)` determines a point of its completed rational
localization through Wedhorn's Proposition 8.2(2). These points agree along the comparison maps
of Proposition 8.2(1).

## Main definitions

* `TauCeti.ValuationSpectrum.rationalLocalizationPoint`: the point of `A⟨p⟩` determined by
  `x ∈ R(p)`.

## Main results

* `TauCeti.ValuationSpectrum.comap_rationalLocalizationPoint`: the rational point lies over `x`.
* `TauCeti.ValuationSpectrum.comap_homOfRationalSubsetSubset_rationalLocalizationPoint`: the
  rational points agree along comparison maps.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

/-- The point of the rational coordinate ring `A⟨p⟩` determined by a point `x` of the rational
subset `R(p)`: the preimage of `x` under the homeomorphism `Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)` of
Wedhorn's Proposition 8.2(2), read on the underlying ring of `p.completionLocObj`. -/
noncomputable def rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    Spv ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
      p.completionLocObj) :=
  letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  comap (Presentation.completionLocObjCommRingCatIso p).hom.hom
    ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
      ⟨x, mem_spaBasicOpen.mp hx⟩).1

/-- The rational point is the point supplied by the completed-localization homeomorphism,
transported to the underlying ring of `p.completionLocObj`. -/
theorem rationalLocalizationPoint_def (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    rationalLocalizationPoint hP p x hx =
      comap (Presentation.completionLocObjCommRingCatIso p).hom.hom
        ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
          ⟨x, mem_spaBasicOpen.mp hx⟩).1 :=
  by rw [rationalLocalizationPoint]

/-- **The rational point lies over `x`**: pulled back along the structure map `A → A⟨p⟩`, the
point of `A⟨p⟩` determined by `x ∈ R(p)` is `x` itself. -/
@[simp]
theorem comap_rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P)
    (x : spa Aplus) (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    comap (CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (forget₂ TopCommRingCat CommRingCat).map
          (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm)).hom
      (rationalLocalizationPoint hP p x hx) = x := by
  simp only [← Presentation.completionLocObjCommRingCatIso_inv]
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  set w := (spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
    ⟨x, mem_spaBasicOpen.mp hx⟩
  have hw := spaCompletedLocalizationHomeomorph_apply P Aplus hP p.num p.den _
    p.hasDenominatorPower w
  rw [Homeomorph.apply_symm_apply] at hw
  rw [rationalLocalizationPoint, comap_hom_comap_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, CommRingCat.hom_ofHom]
  have hxw := congrArg (fun y ↦ y.1.1) hw
  simp only [spaLocToRationalSubset_val, spaComapLoc_val] at hxw
  exact hxw.symm

/-- The comparison map `A⟨p⟩ → A⟨q⟩` of a containment `R(q) ⊆ R(p)` pulls the point of `A⟨q⟩`
determined by `x ∈ R(q)` back to the point of `A⟨p⟩` determined by `x`. This is
`spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset` read through the
inverse homeomorphisms. -/
private theorem comap_ringHomOfRationalSubsetSubset_symm (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus q.num q.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    comap (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower
        q.num q.den _ q.hasDenominatorPower h)
      ((spaCompletedLocalizationHomeomorph P Aplus hP q.num q.den _ q.hasDenominatorPower).symm
        ⟨x, mem_spaBasicOpen.mp hx⟩).1 =
      ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
        ⟨x, h (mem_spaBasicOpen.mp hx)⟩).1 := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P q.num q.den _ q.hasDenominatorPower
  set w := (spaCompletedLocalizationHomeomorph P Aplus hP q.num q.den _ q.hasDenominatorPower).symm
    ⟨x, mem_spaBasicOpen.mp hx⟩
  have key := spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset P Aplus hP
    hAplus p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower h w
  rw [Homeomorph.apply_symm_apply, ← Homeomorph.eq_symm_apply] at key
  rw [← key, Huber.Pair.Hom.spaComap_val, pairHomOfRationalSubsetSubset_toRingHom]

/-- **The rational points are compatible with the comparison maps**: for a containment
`R(q) ⊆ R(p)` and `x ∈ R(q)`, the comparison map `A⟨p⟩ → A⟨q⟩` pulls the point of `A⟨q⟩`
determined by `x` back to the point of `A⟨p⟩` determined by `x`. -/
@[simp]
theorem comap_homOfRationalSubsetSubset_rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus q.num q.den) :
    comap ((forget₂ TopCommRingCat CommRingCat).map
        (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h)).hom).hom
      (rationalLocalizationPoint hP q x hx) = rationalLocalizationPoint hP p x (h hx) := by
  simp only [← Functor.comp_map, ← ObjectProperty.ι_map]
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  rw [rationalLocalizationPoint, rationalLocalizationPoint, comap_hom_comap_hom,
    map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom, ← comap_hom_comap_hom,
    CommRingCat.hom_ofHom, comap_ringHomOfRationalSubsetSubset_symm hP hAplus p q _ x hx]

end

end TauCeti.ValuationSpectrum
