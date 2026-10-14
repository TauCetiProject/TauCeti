/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Flat

/-!
# Flatness of the comparison maps between rational localisations

**Wedhorn's Proposition 8.30**: let `A` be a strongly noetherian Tate ring, and let
`R(T'/s') ⊆ R(T/s)` be rational subsets of `Spa(A, A⁺)`. Then the comparison map
`A⟨T/s⟩ → A⟨T'/s'⟩` of Proposition 8.2(1) is flat.

`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHom` proves this when `(T', s')` refines
`(T, s)` syntactically. A containment of rational subsets reduces to that case. The common
refinement `(T'', s s')`, with `T'' = (T ∪ {s}) · (T' ∪ {s'})`, presents
`R(T/s) ∩ R(T'/s') = R(T'/s')` (`TauCeti.ValuationSpectrum.rationalSubset_inter`). So the
comparison map is the restriction map `A⟨T/s⟩ → A⟨T''/(s s')⟩` of a refinement, followed by the
presentation-independence isomorphism `A⟨T''/(s s')⟩ ≅ A⟨T'/s'⟩`. Both maps are continuous and
compatible with the structure maps from `A`, so by the uniqueness in Proposition 8.2(1) their
composite is the comparison map.

## Main results

* `TauCeti.ValuationSpectrum.flat_ringHomOfRationalSubsetSubset`: **Wedhorn's Proposition 8.30**,
  for an arbitrary containment of rational subsets.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.30 and
  Proposition 8.2(1).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn's Proposition 8.30.** Over a strongly noetherian Tate ring `A`, a containment
`R(T'/s') ⊆ R(T/s)` of rational subsets induces a flat comparison map `A⟨T/s⟩ → A⟨T'/s'⟩`, the map
`ringHomOfRationalSubsetSubset` of Proposition 8.2(1). The numerators `T` together with the
denominator `s` must generate the unit ideal, which holds for every rational subset of a Tate ring.
Nothing is asked of `(T', s')` beyond the standing hypothesis `HasDenominatorPower`.

When `(T', s')` refines `(T, s)` syntactically, this is
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHom`. -/
theorem flat_ringHomOfRationalSubsetSubset [IsTateRing A] [IsStronglyNoetherian A]
    (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s)
    (hspan : Ideal.span (insert s (T : Set A)) = ⊤) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub).Flat := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  -- a common refinement `(T'', s s')` of the two presentations, presenting `R(T'/s')`
  obtain ⟨T'', heq, hT, hT'⟩ := exists_refinement_of_subset Aplus T T' s s' hsub
  have hden'' : HasDenominatorPower P T'' (s * s') (Localization.Away (s * s')) :=
    hasDenominatorPower_mul P T T' T'' s s' S S' _ hT hT' hden hden'
  let _ := locUniformSpace P T'' (s * s') _ hden''
  have _ := isUniformAddGroup_locUniformSpace P T'' (s * s') _ hden''
  have _ := isTopologicalRing_locUniformSpace P T'' (s * s') _ hden''
  let e := presentationRingEquivOfEq P Aplus hAplus T'' (s * s') _ hden'' T' s' S' hden' heq.symm
  let ρ := restrictionRingHom P T s S hden T'' (s * s') _ hden'' s' rfl hT
  -- the comparison map is the restriction to the refinement followed by `e`: both are continuous
  -- and compatible with the structure maps, which by Proposition 8.2(1) determines the map
  have hcomp : ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub =
      (e : _ →+* _).comp ρ := by
    refine (eq_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub _
      ((continuous_presentationRingEquivOfEq P Aplus hAplus T'' (s * s') _ hden'' T' s' S' hden'
        heq.symm).comp (continuous_restrictionRingHom P T s S hden T'' (s * s') _ hden'' s' rfl hT))
      ?_).symm
    rw [RingHom.comp_assoc, restrictionRingHom_comp_toCompletionLoc,
      presentationRingEquivOfEq_coe_comp_toCompletionLoc]
  rw [hcomp]
  exact (flat_restrictionRingHom P T s S hden T'' (s * s') _ hden'' s' rfl hT hspan).comp
    (.of_bijective e.bijective)

end TauCeti.ValuationSpectrum
