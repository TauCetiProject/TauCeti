/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Support

/-!
# Units of a rational coordinate ring near a point

Let `U = R(T/s)` be a rational subset of `Spa (A, A⁺)` with coordinate ring `A⟨T/s⟩`. For a point
`x ∈ U`, write `x_U` for the point of `Spa (A⟨T/s⟩, A_U⁺)` lying over `x` under the homeomorphism
`spaCompletedLocalizationHomeomorph` of Wedhorn's Proposition 8.2 (2). This file proves that
`f ∈ A⟨T/s⟩` does not vanish at `x_U`, that is `f ∉ supp x_U`, exactly when `f` becomes a unit in
the coordinate ring of some rational neighbourhood `R(T'/s') ⊆ R(T/s)` of `x`.

This criterion supplies the local unit calculation for proving that the stalk of the structure
presheaf at `x` is a local ring whose maximal ideal is the support of the point valuation.

## Main results

* `ringHomOfRationalSubsetSubset_mem_supp_iff`: vanishing at `x` is compatible with restriction —
  for `R(T'/s') ⊆ R(T/s)`, `f` vanishes at `x_U` exactly when its image in `A⟨T'/s'⟩` vanishes
  at `x_U'`.
* `notMem_supp_of_isUnit_ringHomOfRationalSubsetSubset`: an element that
  becomes a unit on a rational neighbourhood of `x` does not vanish at `x`.
* `notMem_supp_iff_exists_isUnit_ringHomOfRationalSubsetSubset`: the
  criterion — `f` does not vanish at `x` exactly when it becomes a unit on a rational
  neighbourhood of `x`, which may be taken with an admissible presentation.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 7.52 and 8.2, and
  §8.1.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The points over `x` are compatible with restriction: for a containment `R(T'/s') ⊆ R(T/s)`
and a point `x ∈ R(T'/s')`, the map of adic spectra induced by the comparison map
`A⟨T/s⟩ → A⟨T'/s'⟩` sends the point of `Spa (A⟨T'/s'⟩, A_U'⁺)` over `x` to the point of
`Spa (A⟨T/s⟩, A_U⁺)` over `x`. This is
`spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset` read through the
inverse homeomorphisms, in the form `ringHomOfRationalSubsetSubset_mem_supp_iff` consumes. -/
private theorem spaComap_pairHomOfRationalSubsetSubset_spaCompletedLocalizationHomeomorph_symm
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s)
    (x : (Subtype.val ⁻¹' rationalSubset Aplus T' s' : Set (spa Aplus))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := isHuberRing_completion_locTopology P T' s' S' hden'
    (pairHomOfRationalSubsetSubset P Aplus (fun j _ ↦ hP j.property) hAplus T s S hden
        T' s' S' hden' hsub).spaComap
        ((spaCompletedLocalizationHomeomorph P Aplus hP T' s' S' hden').symm x) =
      (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm
        (Set.inclusion (Set.preimage_mono (f := Subtype.val) hsub) x) := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  rw [Homeomorph.eq_symm_apply,
    spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset,
    Homeomorph.apply_symm_apply]

/-- **Vanishing at `x` is compatible with restriction.** For a containment `R(T'/s') ⊆ R(T/s)` and
a point `x ∈ R(T'/s')`, the image of `f ∈ A⟨T/s⟩` in `A⟨T'/s'⟩` lies in the support of the point
over `x` exactly when `f` does. -/
@[simp] theorem ringHomOfRationalSubsetSubset_mem_supp_iff
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s)
    (x : (Subtype.val ⁻¹' rationalSubset Aplus T' s' : Set (spa Aplus))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ f : Completion S,
      ((spaCompletedLocalizationHomeomorph P Aplus hP T' s' S' hden').symm x).1.toValuativeRel.vle
          (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub f) 0 ↔
        ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm
          (Set.inclusion (Set.preimage_mono (f := Subtype.val) hsub) x)).1.toValuativeRel.vle
          f 0 := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  intro f
  rw [← spaComap_pairHomOfRationalSubsetSubset_spaCompletedLocalizationHomeomorph_symm P Aplus hP
      hAplus T s S hden T' s' S' hden' hsub x, Huber.Pair.Hom.spaComap_val, comap_vle, map_zero,
    pairHomOfRationalSubsetSubset_toRingHom]

/-- If `f ∈ A⟨T/s⟩` becomes a unit in the coordinate ring of a rational subset `R(T'/s') ⊆ R(T/s)`,
then `f` vanishes at no point of `R(T'/s')`. -/
theorem notMem_supp_of_isUnit_ringHomOfRationalSubsetSubset
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s)
    (x : (Subtype.val ⁻¹' rationalSubset Aplus T' s' : Set (spa Aplus))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ f : Completion S,
      IsUnit (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub f) →
        f ∉ supp ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm
          (Set.inclusion (Set.preimage_mono (f := Subtype.val) hsub) x)).1 := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro f hf hsupp
  have hval := (mem_supp_iff _ _).mp hsupp
  have hval' := (ringHomOfRationalSubsetSubset_mem_supp_iff P Aplus hP hAplus T s S hden T' s'
    S' hden' hsub x f).mpr hval
  exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _
    ((mem_supp_iff _ _).mpr hval') hf)

/-- The nontrivial direction of `notMem_supp_iff_exists_isUnit_ringHomOfRationalSubsetSubset`. -/
private theorem exists_isUnit_ringHomOfRationalSubsetSubset_of_notMem_supp
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (x : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ f : Completion S,
      f ∉ supp ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm x).1 →
        ∃ q : Presentation P, IsOpen (Ideal.span (q.num : Set A) : Set A) ∧
          x.1.1 ∈ rationalSubset Aplus q.num q.den ∧
          ∃ hsub : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus T s,
            letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
            letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
            letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
            IsUnit (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden q.num q.den _
              q.hasDenominatorPower hsub f) := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro f hf
  set e := spaCompletedLocalizationHomeomorph P Aplus hP T s S hden
  -- the points of `Spa (A⟨T/s⟩, A_U⁺)` off the support of `f` form an open neighbourhood of the
  -- point over `x`, which therefore contains a rational neighbourhood `W`
  have hN : IsOpen {w : spa (completedPlusSubring P Aplus T s S hden) | f ∉ supp w.1} := by
    have : {w : spa (completedPlusSubring P Aplus T s S hden) | f ∉ supp w.1} =
        Subtype.val ⁻¹' basicOpen f f := by
      ext w
      simp [ValuativeRel.vle_refl]
    rw [this]
    exact (isOpen_basicOpen f f).preimage continuous_subtype_val
  obtain ⟨W, hW, hxW, hWN⟩ :=
    (isTopologicalBasis_spaRationalFamily _).exists_subset_of_mem_open hf hN
  -- its image in `Spa (A, A⁺)` is a rational subset `R(T'/s')`, necessarily inside `R(T/s)`
  obtain ⟨T', s', hT', hV⟩ := mem_spaRationalFamily_iff.mp
    (spaCompletedLocalizationHomeomorph_image_mem_spaRationalFamily P Aplus hP T s hT S hden W hW)
  have hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s := by
    intro v hv
    have hmem : (⟨v, rationalSubset_subset_spa Aplus T' s' hv⟩ : spa Aplus) ∈
        Subtype.val '' (e '' W) := hV ▸ hv
    obtain ⟨_, ⟨u, -, rfl⟩, hu⟩ := hmem
    have h : ((e u : spa Aplus) : Spv A) ∈ rationalSubset Aplus T s := (e u).2
    rwa [hu] at h
  refine ⟨⟨T', s', P.hasDenominatorPower_of_isOpen_span T' s' _ hT'⟩, hT', ?_, hsub, ?_⟩
  · have hmem : x.1 ∈ Subtype.val '' (e '' W) :=
      ⟨x, ⟨e.symm x, hxW, e.apply_symm_apply x⟩, rfl⟩
    rw [hV] at hmem
    exact hmem
  -- on `R(T'/s')` every point is off the support of `f`, so its image is a unit
  have hden' := P.hasDenominatorPower_of_isOpen_span T' s' (Localization.Away s') hT'
  let _ := locUniformSpace P T' s' _ hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' _ hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' _ hden'
  have _ := isHuberRing_completion_locTopology P T' s' _ hden'
  set e' := spaCompletedLocalizationHomeomorph P Aplus hP T' s' _ hden'
  refine (isUnit_iff_forall_mem_spa_notMem_supp _ (isRingOfIntegralElements_completedPlusSubring
    P Aplus (fun j _ ↦ hP j.property) hAplus T' s' _ hden') _).mpr fun w hw ↦ ?_
  have hmem : (e' ⟨w, hw⟩).1 ∈ Subtype.val '' (e '' W) := hV.symm ▸ (e' ⟨w, hw⟩).2
  obtain ⟨_, ⟨u, huW, rfl⟩, hu⟩ := hmem
  have hincl : e.symm (Set.inclusion (Set.preimage_mono (f := Subtype.val) hsub) (e' ⟨w, hw⟩)) =
      u := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hu.symm
  intro hsupp
  have hsupp' : ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' _ hden' hsub f ∈
      supp ((spaCompletedLocalizationHomeomorph P Aplus hP T' s' _ hden').symm (e' ⟨w, hw⟩)).1 := by
    rwa [Homeomorph.symm_apply_apply]
  have hval := (mem_supp_iff _ _).mp hsupp'
  have hval' := (ringHomOfRationalSubsetSubset_mem_supp_iff P Aplus hP hAplus T s S hden T' s' _
    hden' hsub (e' ⟨w, hw⟩) f).mp hval
  have hfu := (mem_supp_iff _ _).mpr hval'
  rw [hincl] at hfu
  exact hWN huW hfu

/-- **An element of `A⟨T/s⟩` is nonzero at `x` exactly when it is a unit near `x`.** Let
`R(T/s)` be a rational subset of `Spa (A, A⁺)` with open numerator ideal and `x ∈ R(T/s)`. Then
`f ∈ A⟨T/s⟩` lies outside the support of the point of `Spa (A⟨T/s⟩, A_U⁺)` over `x` if and only if
there is a rational subset `R(q) ⊆ R(T/s)` containing `x`, presented by an admissible presentation
`q`, such that the image of `f` in `A⟨q⟩` is a unit. -/
theorem notMem_supp_iff_exists_isUnit_ringHomOfRationalSubsetSubset
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (x : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ f : Completion S,
      f ∉ supp ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm x).1 ↔
        ∃ q : Presentation P, IsOpen (Ideal.span (q.num : Set A) : Set A) ∧
          x.1.1 ∈ rationalSubset Aplus q.num q.den ∧
          ∃ hsub : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus T s,
            letI := locUniformSpace P q.num q.den _ q.hasDenominatorPower
            letI := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
            letI := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
            IsUnit (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden q.num q.den _
              q.hasDenominatorPower hsub f) := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  refine fun f ↦ ⟨exists_isUnit_ringHomOfRationalSubsetSubset_of_notMem_supp P Aplus hP hAplus
    T s hT S hden x f, ?_⟩
  rintro ⟨q, -, hxq, hsub, hunit⟩
  exact notMem_supp_of_isUnit_ringHomOfRationalSubsetSubset P Aplus hP hAplus T s S hden q.num
    q.den _ q.hasDenominatorPower hsub ⟨x.1, hxq⟩ f hunit

end TauCeti.ValuationSpectrum

end
