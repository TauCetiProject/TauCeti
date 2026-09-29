/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.Topology.Spectral.SpectralMap

import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Spectral maps of adic spectra

A continuous morphism of Huber pairs induces a continuous map of adic spectra. The map is
spectral when the image of every open ideal again generates an open ideal:
the preimage of each rational open is then rational, hence quasi-compact. For a Tate source,
every open ideal is the unit ideal, so this condition holds for every morphism into a Huber
ring. These statements give the compact-open control needed when pulling back the rational
basis along morphisms.

It suffices to test openness on the image of one ideal of definition of the source. The
criterion does not require the underlying ring map to be open or surjective.

## Main results

* `spaComap_preimage_mem_spaRationalFamily_of_isOpen_map_extendedIdealOfDefinition`: the
  rational-preimage result under the ideal-of-definition criterion.
* `spaComap_preimage_mem_spaRationalFamily_of_isTateRing`: the rational-preimage result for a
  Tate source.
* `isSpectralMap_spaComap`: the resulting map on adic spectra is spectral.
* `isSpectralMap_spaComap_of_isOpen_map_extendedIdealOfDefinition`: it suffices to test one
  extended ideal of definition.
* `isSpectralMap_spaComap_of_isTateRing`: every morphism from a Tate Huber pair is spectral.

The unbundled rational-preimage criterion is in `Spa/RationalSubset/Basis.lean`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §6.5 for related adic homomorphisms and
  Proposition 6.25 on maps from Tate rings, Definition 7.14(4) for morphisms of Huber pairs,
  Remark and Definition 7.28 for their induced maps on `Spa`, and Theorem 7.35 for the rational
  basis of quasi-compact opens used here.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), §3, for adic spectra and their
  rational subsets.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

section General

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {T : Pair B}

/-- Under the openness hypothesis, the preimage of a rational open under a Huber-pair morphism
is again rational. -/
theorem spaComap_preimage_mem_spaRationalFamily (f : Hom S T)
    (hopen : ∀ J : Ideal A, IsOpen (J : Set A) →
      IsOpen (Ideal.map f.toRingHom J : Set B))
    {U : Set (spa S.plus)} (hU : U ∈ spaRationalFamily S.plus) :
    f.spaComap ⁻¹' U ∈ spaRationalFamily T.plus := by
  rw [f.spaComap_def]
  exact ValuationSpectrum.spaComap_preimage_mem_spaRationalFamily
    f.toRingHom f.continuous_toRingHom S.plus T.plus f.map_mem_plus hopen hU

/-- The adic-spectrum map of a Huber-pair morphism is spectral when images of open ideals
are open. -/
theorem isSpectralMap_spaComap (f : Hom S T)
    (hopen : ∀ J : Ideal A, IsOpen (J : Set A) →
      IsOpen (Ideal.map f.toRingHom J : Set B)) :
    IsSpectralMap f.spaComap := by
  apply TauCeti.isSpectralMap_of_isTopologicalBasis
    (isTopologicalBasis_spaRationalFamily S.plus) f.continuous_spaComap
  intro U hU
  exact isCompact_of_mem_spaRationalFamily
    (f.spaComap_preimage_mem_spaRationalFamily hopen hU)

/-- It is enough to check openness on the image of one ideal of definition: openness of every
other source ideal then transports along the ring homomorphism. Rational opens therefore pull
back to rational opens. -/
theorem spaComap_preimage_mem_spaRationalFamily_of_isOpen_map_extendedIdealOfDefinition
    (f : Hom S T) (P : PairOfDefinition A)
    (hP : IsOpen (Ideal.map f.toRingHom P.extendedIdealOfDefinition : Set B))
    {U : Set (spa S.plus)} (hU : U ∈ spaRationalFamily S.plus) :
    f.spaComap ⁻¹' U ∈ spaRationalFamily T.plus := by
  exact f.spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ P.isOpen_map_of_isOpen_map_extendedIdealOfDefinition_of_isHuberRing
      f.toRingHom hP hJ) hU

/-- Openness of the image of one ideal of definition makes the induced map spectral. -/
theorem isSpectralMap_spaComap_of_isOpen_map_extendedIdealOfDefinition
    (f : Hom S T) (P : PairOfDefinition A)
    (hP : IsOpen (Ideal.map f.toRingHom P.extendedIdealOfDefinition : Set B)) :
    IsSpectralMap f.spaComap :=
  f.isSpectralMap_spaComap (fun _ hJ ↦
    P.isOpen_map_of_isOpen_map_extendedIdealOfDefinition_of_isHuberRing f.toRingHom hP hJ)

end General

section Tate

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {T : Pair B}

/-- Rational opens pull back to rational opens for a morphism from a Tate Huber pair. No Tate
assumption is needed on the target. -/
theorem spaComap_preimage_mem_spaRationalFamily_of_isTateRing (f : Hom S T)
    {U : Set (spa S.plus)} (hU : U ∈ spaRationalFamily S.plus) :
    f.spaComap ⁻¹' U ∈ spaRationalFamily T.plus :=
  f.spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ IsTateRing.isOpen_map_of_isOpen f.toRingHom hJ) hU

/-- A morphism from a Tate Huber pair induces a spectral map of adic spectra. -/
theorem isSpectralMap_spaComap_of_isTateRing (f : Hom S T) :
    IsSpectralMap f.spaComap :=
  f.isSpectralMap_spaComap (fun _ hJ ↦ IsTateRing.isOpen_map_of_isOpen f.toRingHom hJ)

end Tate

end TauCeti.Huber.Pair.Hom

end
