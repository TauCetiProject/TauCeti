/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalks
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Point
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.OfDirected

/-!
# The valuation on a stalk of the presentation-limit presheaf

Let `x` be a point of `X = Spa(A,A⁺)`. Every rational neighbourhood `R(p)` of `x` has coordinate
ring `A⟨p⟩`, and `x` determines a point of `Spa (A⟨p⟩, A_p⁺)` through the homeomorphism
`Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)` of Wedhorn's Proposition 8.2(2). This file glues these points along
the germ maps into a point of the valuation spectrum of the presentation-limit presheaf stalk.
It is the presheaf-stalk version of the valuation `v_x` which Wedhorn attaches to `x` in §8.1.
No comparison with the adic-space structure sheaf is established here.

The gluing is `TauCeti.ValuationSpectrum.ofDirected`. Its hypotheses are supplied here: every germ
is the germ of an element of some `A⟨p⟩`; a germ vanishes only if some restriction to a smaller
rational neighbourhood does. The compatibility of the points of `x` on the rings `A⟨p⟩` with the
comparison maps of Wedhorn's Proposition 8.2(1) comes from `Spa.Localization.Point`. Two lifts of
one germ therefore differ, on a common rational neighbourhood, by an element of the support of the
point of `x`, and so they have the same value.

The stalk is the ring colimit of `presentationLimitPresheafInCommRingCat`; no topology on it is
used. `A⁺` is assumed to consist of power-bounded elements, as for every ring of integral
elements, and to contain the ring of definition of the chosen pair of definition, as
`spaCompletedLocalizationHomeomorph` requires.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitStalkValuation`: the valuation on the stalk at `x`.

## Main results

* `TauCeti.ValuationSpectrum.comap_presentationLimitRationalGerm_presentationLimitStalkValuation`:
  pulled back along the germ map of a rational neighbourhood `R(p)`, the stalk valuation is the
  point of `A⟨p⟩` determined by `x`.
* `TauCeti.ValuationSpectrum.eq_presentationLimitStalkValuation`: it is the only point of the
  valuation spectrum of the stalk with this property.
* `TauCeti.ValuationSpectrum.comap_presentationLimitStalkValuation`: pulled back to `A`, the stalk
  valuation is `x` itself.

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

variable (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)

/-! ### The stalk valuation -/

variable (P) in
/-- The rational neighbourhoods of `x`: admissible presentations whose rational subset contains
`x`. They index the rational germ maps into the stalk at `x`. -/
private abbrev RationalNhd (x : spa Aplus) : Type v :=
  {i : PresentationIndex (P := P) Aplus ⊤ //
    x ∈ spaBasicOpen Aplus i.pres.num i.pres.den}

/-- The rational germ map of a rational neighbourhood of `x`, as a ring homomorphism. -/
private noncomputable abbrev rationalNhdGerm {x : spa Aplus} (i : RationalNhd P x) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        i.1.pres.completionLocObj →+* (presentationLimitPresheafInCommRingCat P Aplus).stalk x :=
  (presentationLimitRationalGerm hAplus i.1.pres i.1.isOpen_span x i.2).hom

/-- The comparison map between the coordinate rings of two rational neighbourhoods of `x`, as a
ring homomorphism. -/
private noncomputable abbrev rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.pres.num j.1.pres.den ≤
      spaBasicOpen Aplus i.1.pres.num i.1.pres.den) :
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        i.1.pres.completionLocObj →+*
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).obj
        j.1.pres.completionLocObj :=
  ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
    (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h))).hom

omit hAplus in
/-- Two rational neighbourhoods of `x` contain a third, the rational subset of their common
refinement. -/
private theorem exists_rationalNhd_le_le {x : spa Aplus} (i j : RationalNhd P x) :
    ∃ k : RationalNhd P x,
      spaBasicOpen Aplus k.1.pres.num k.1.pres.den ≤
        spaBasicOpen Aplus i.1.pres.num i.1.pres.den ∧
      spaBasicOpen Aplus k.1.pres.num k.1.pres.den ≤
        spaBasicOpen Aplus j.1.pres.num j.1.pres.den := by
  refine ⟨⟨i.1.commonRefinement j.1, ?_⟩, ?_, ?_⟩
  · rw [PresentationIndex.commonRefinement_pres, spaBasicOpen_commonRefinement]
    exact ⟨i.2, j.2⟩
  · rw [PresentationIndex.commonRefinement_pres, spaBasicOpen_commonRefinement]
    exact inf_le_left
  · rw [PresentationIndex.commonRefinement_pres, spaBasicOpen_commonRefinement]
    exact inf_le_right

/-- Rational germs are compatible with the comparison maps. -/
private theorem rationalNhdGerm_rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.pres.num j.1.pres.den ≤
      spaBasicOpen Aplus i.1.pres.num i.1.pres.den) (a) :
    rationalNhdGerm hAplus j (rationalNhdMap hAplus h a) = rationalNhdGerm hAplus i a := by
  rw [rationalNhdGerm, rationalNhdGerm, rationalNhdMap, ← CommRingCat.comp_apply,
    presentationLimitRationalGerm_res hAplus i.1.pres j.1.pres
      i.1.isOpen_span j.1.isOpen_span h x j.2]

/-- The germ maps of the rational neighbourhoods of `x` have directed images. -/
private theorem directed_range_rationalNhdGerm (x : spa Aplus) :
    Directed (· ≤ ·) fun i : RationalNhd P x ↦ (rationalNhdGerm hAplus i).range := by
  intro i j
  obtain ⟨k, hki, hkj⟩ := exists_rationalNhd_le_le i j
  refine ⟨k, ?_, ?_⟩ <;> rintro _ ⟨a, rfl⟩
  · exact ⟨_, rationalNhdGerm_rationalNhdMap hAplus hki a⟩
  · exact ⟨_, rationalNhdGerm_rationalNhdMap hAplus hkj a⟩

/-- The germ maps of the rational neighbourhoods of `x` jointly cover the stalk. -/
private theorem exists_mem_range_rationalNhdGerm (x : spa Aplus)
    (t : (presentationLimitPresheafInCommRingCat P Aplus).stalk x) :
    ∃ i : RationalNhd P x, t ∈ (rationalNhdGerm hAplus i).range := by
  obtain ⟨p, hp, hx, a, rfl⟩ := exists_presentationLimitRationalGerm_eq hAplus x t
  exact ⟨⟨⟨p, hp, le_top⟩, hx⟩, a, rfl⟩

variable (hP : P.ringOfDefinition ≤ Aplus)

/-- The point of a rational neighbourhood is a pullback of the point of any smaller one. -/
private theorem comap_rationalNhdMap {x : spa Aplus} {i j : RationalNhd P x}
    (h : spaBasicOpen Aplus j.1.pres.num j.1.pres.den ≤
      spaBasicOpen Aplus i.1.pres.num i.1.pres.den) :
    comap (rationalNhdMap hAplus h) (rationalLocalizationPoint hP j.1.pres x j.2) =
      rationalLocalizationPoint hP i.1.pres x i.2 :=
  comap_homOfRationalSubsetSubset_rationalLocalizationPoint hP hAplus i.1.pres j.1.pres h x j.2

/-- An element of a rational coordinate ring with zero germ at `x` is in the support of the point
of `x`. -/
private theorem vle_zero_of_rationalNhdGerm_eq_zero {x : spa Aplus} {i : RationalNhd P x} {a}
    (ha : rationalNhdGerm hAplus i a = 0) :
    (rationalLocalizationPoint hP i.1.pres x i.2).toValuativeRel.vle a 0 := by
  obtain ⟨q, hq, hxq, h, hqa⟩ := exists_map_homOfRationalSubsetSubset_eq_zero hAplus ha
  -- `rationalNhdMap` is an `abbrev`; this is `hqa` after reducible unfolding.
  have hqa' : rationalNhdMap hAplus (j := ⟨⟨q, hq, le_top⟩, hxq⟩) h a = 0 := hqa
  rw [← comap_rationalNhdMap hAplus hP (j := ⟨⟨q, hq, le_top⟩, hxq⟩) h, comap_vle, map_zero, hqa']
  exact (rationalLocalizationPoint hP q x hxq).toValuativeRel.vle_refl 0

/-- Elements with the same germ compare in the same way under the points of their rational
neighbourhoods. -/
private theorem rationalNhd_compat {x : spa Aplus} (i j : RationalNhd P x) (a b) (a' b')
    (ha : rationalNhdGerm hAplus i a = rationalNhdGerm hAplus j a')
    (hb : rationalNhdGerm hAplus i b = rationalNhdGerm hAplus j b')
    (hab : (rationalLocalizationPoint hP i.1.pres x i.2).toValuativeRel.vle a b) :
    (rationalLocalizationPoint hP j.1.pres x j.2).toValuativeRel.vle a' b' := by
  obtain ⟨k, hki, hkj⟩ := exists_rationalNhd_le_le i j
  set w := rationalLocalizationPoint hP k.1.pres x k.2
  -- in the common neighbourhood `k`, the two lifts of each germ differ by an element of the
  -- support, so they have the same value
  have hsupp {c c' : _} (hc : rationalNhdGerm hAplus i c = rationalNhdGerm hAplus j c') :
      w.valuation (rationalNhdMap hAplus hkj c') = w.valuation (rationalNhdMap hAplus hki c) := by
    have hmem : rationalNhdMap hAplus hkj c' - rationalNhdMap hAplus hki c ∈ w.supp := by
      rw [mem_supp_iff]
      refine vle_zero_of_rationalNhdGerm_eq_zero hAplus hP ?_
      rw [map_sub, rationalNhdGerm_rationalNhdMap, rationalNhdGerm_rationalNhdMap, hc, sub_self]
    rw [supp_eq_valuation_supp] at hmem
    simpa using w.valuation.map_add_supp (rationalNhdMap hAplus hki c) hmem
  rw [← comap_rationalNhdMap hAplus hP hki, comap_vle, ← valuation_le_iff] at hab
  rw [← comap_rationalNhdMap hAplus hP hkj, comap_vle, ← valuation_le_iff, hsupp ha, hsupp hb]
  exact hab

/-- **The valuation on the stalk** of the presentation-limit presheaf at a point `x` of
`Spa(A,A⁺)`: the point of its valuation spectrum which, on the germs of every rational neighbourhood
`R(p)` of `x`, is the point of `A⟨p⟩` that `x` determines under
`Spa (A⟨p⟩, A_p⁺) ≃ₜ R(p)`. -/
noncomputable def presentationLimitStalkValuation (x : spa Aplus) :
    Spv ((presentationLimitPresheafInCommRingCat P Aplus).stalk x) :=
  ofDirected (fun i : RationalNhd P x ↦ rationalNhdGerm hAplus i)
    (w := fun i ↦ rationalLocalizationPoint hP i.1.pres x i.2) (rationalNhd_compat hAplus hP)
    (directed_range_rationalNhdGerm hAplus x) (exists_mem_range_rationalNhdGerm hAplus x)

/-- **The stalk valuation restricts to the rational points**: its pullback along the germ map of
a rational neighbourhood `R(p)` of `x` is the point of `A⟨p⟩` determined by `x`. -/
@[simp]
theorem comap_presentationLimitRationalGerm_presentationLimitStalkValuation (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    comap (presentationLimitRationalGerm hAplus p hp x hx).hom
        (presentationLimitStalkValuation hAplus hP x) =
      rationalLocalizationPoint hP p x hx :=
  comap_ofDirected (fun i : RationalNhd P x ↦ rationalNhdGerm hAplus i) _ _ _ ⟨⟨p, hp, le_top⟩, hx⟩

/-- **Uniqueness of the stalk valuation**: a point of the valuation spectrum of the stalk at `x`
whose pullback along the germ map of every rational neighbourhood `R(p)` of `x` is the point of
`A⟨p⟩` determined by `x` is `presentationLimitStalkValuation`. -/
theorem eq_presentationLimitStalkValuation {x : spa Aplus}
    {v : Spv ((presentationLimitPresheafInCommRingCat P Aplus).stalk x)}
    (hv : ∀ (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
      (hx : x ∈ spaBasicOpen Aplus p.num p.den),
      comap (presentationLimitRationalGerm hAplus p hp x hx).hom v =
        rationalLocalizationPoint hP p x hx) :
    v = presentationLimitStalkValuation hAplus hP x :=
  eq_ofDirected _ _ _ _ fun i ↦ hv i.1.pres i.1.isOpen_span i.2

/-- **The stalk valuation lies over `x`**: pulled back to `A` along the structure map `A → A⟨p⟩`
and the germ map of a rational neighbourhood `R(p)` of `x`, the stalk valuation at `x` is `x`. -/
@[simp]
theorem comap_presentationLimitStalkValuation (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    comap (CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (Presentation.completionLocObjCommRingCatIso p).inv ≫
          presentationLimitRationalGerm hAplus p hp x hx).hom
        (presentationLimitStalkValuation hAplus hP x) = x := by
  rw [← Category.assoc, ← comap_hom_comap_hom,
    comap_presentationLimitRationalGerm_presentationLimitStalkValuation,
    comap_rationalLocalizationPoint]

end

end TauCeti.ValuationSpectrum
