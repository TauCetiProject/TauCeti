/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
public import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete

/-!
# Comparison maps of rational subsets of a discrete Huber pair

Let `A` be a ring with the discrete topology. For every presentation `(T, s)` the completed
localisation `A⟨T/s⟩` is the discrete ring `A_s` itself
(`TauCeti.Huber.PairOfDefinition.completionLocEquivOfDiscreteTopology`). This file identifies the
comparison maps between these rings. If `R(T'/s') ⊆ R(T/s)` in `Spa(A, A⁺)`, then `s` is a unit
of `A_{s'}` (`TauCeti.ValuationSpectrum.isUnit_algebraMap_of_rationalSubset_subset`, every prime
of a discrete ring being open), so there is a localisation map `A_s → A_{s'}` over `A`. Wedhorn's
comparison map `A⟨T/s⟩ → A⟨T'/s'⟩` of Proposition 8.2(1) is this localisation map.

Together, these say that on the rational subsets of a discrete Huber pair, the coordinate rings
and their comparison maps are those of the presheaf `D(s) ↦ A_s` of `Spec A`. This is the
description used in Wedhorn's proof of Theorem 8.28 for discrete Huber pairs, which reduces
sheafiness on rational covers to the exactness of Čech complexes of localisations
(`TauCeti.cechComplexLocalization_exact`).

## Main results

* `TauCeti.ValuationSpectrum.ringHomOfRationalSubsetSubset_coe_of_discreteTopology`: over a
  discrete ring, the comparison map `A⟨T/s⟩ → A⟨T'/s'⟩` sends the image of `x ∈ A_s` to the image
  of its localisation in `A_{s'}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(1) and
  Theorem 8.28, case (c).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- **Over a discrete ring the comparison map is the localisation map.** Let `A` be discrete and
`R(T'/s') ⊆ R(T/s)` in `Spa(A, A⁺)`. Then `s` is a unit of `A_{s'}`, and the comparison map
`A⟨T/s⟩ → A⟨T'/s'⟩` of Wedhorn's Proposition 8.2(1) sends the image of `x ∈ A_s` to the image of
`IsLocalization.Away.lift s _ x ∈ A_{s'}`. Since `A_s → A⟨T/s⟩` is bijective
(`completionLocEquivOfDiscreteTopology`), this determines the comparison map. -/
@[simp]
theorem ringHomOfRationalSubsetSubset_coe_of_discreteTopology (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) (x : S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub
        (x : UniformSpace.Completion S) =
      (IsLocalization.Away.lift s (isUnit_algebraMap_of_rationalSubset_subset S'
        (fun _ _ ↦ isOpen_discrete _) hsub) x : UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ : DiscreteTopology S := by
    rw [locUniformSpace_toTopologicalSpace]
    exact discreteTopology_locTopology P T s S hden
  set f := IsLocalization.Away.lift (S := S) s (isUnit_algebraMap_of_rationalSubset_subset S'
    (fun _ _ ↦ isOpen_discrete _) hsub)
  -- every map out of the discrete ring `A_s` is continuous, hence uniformly continuous
  have hf : Continuous f := continuous_of_discreteTopology
  have hfu : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  -- the completion of the localisation map is continuous and compatible with the structure maps,
  -- so it is the comparison map
  have hg := eq_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub
    (UniformSpace.Completion.mapRingHom f hf) UniformSpace.Completion.continuous_map
    (RingHom.ext fun a ↦ by
      simp [UniformSpace.Completion.map_coe hfu, f, IsLocalization.Away.lift_eq])
  rw [← hg, UniformSpace.Completion.mapRingHom_apply, UniformSpace.Completion.map_coe hfu]

end TauCeti.ValuationSpectrum
