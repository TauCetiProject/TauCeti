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
spectral when the image of every finite set spanning an open ideal again spans an open ideal:
the preimage of each rational open is then rational, hence quasi-compact. For a Tate source,
every open ideal is the unit ideal, so this condition holds for every morphism into a Huber
ring. These statements give the compact-open control needed when pulling back the rational
basis along morphisms.

It suffices to test openness on the image of one ideal of definition of the source. The
criterion does not require the underlying ring map to be open or surjective.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23 and Theorem 7.35.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

section General

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {T : Pair B}

open scoped Classical in
/-- The adic-spectrum map of a Huber-pair morphism is spectral when images of finite open-ideal
generating sets again generate open ideals. The computed preimage of each rational basis open is
then itself a rational open. -/
theorem isSpectralMap_spaComap (f : Hom S T)
    (hopen : ∀ U : Finset A, IsOpen (Ideal.span (U : Set A) : Set A) →
      IsOpen (Ideal.span (U.image f.toRingHom : Set B) : Set B)) :
    IsSpectralMap f.spaComap := by
  classical
  apply TauCeti.isSpectralMap_of_isTopologicalBasis
    (isTopologicalBasis_spaRationalFamily S.plus) f.continuous_spaComap
  intro U hU
  obtain ⟨V, s, hV, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  rw [f.spaComap_preimage_rationalSubset]
  exact isCompact_of_mem_spaRationalFamily
    (mem_spaRationalFamily_iff.mpr ⟨V.image f.toRingHom, f.toRingHom s, hopen V hV, rfl⟩)

/-- It is enough to check openness on the image of one ideal of definition: openness of every
other source ideal then transports along the ring homomorphism. -/
theorem isSpectralMap_spaComap_of_isOpen_map_idealOfDefinition
    (f : Hom S T) (P : PairOfDefinition A) (Q : PairOfDefinition B)
    (hP : IsOpen (Ideal.map f.toRingHom P.extendedIdealOfDefinition : Set B)) :
    IsSpectralMap f.spaComap := by
  classical
  apply f.isSpectralMap_spaComap
  intro U hU
  rw [Finset.coe_image, ← Ideal.map_span]
  exact P.isOpen_map_of_isOpen_map_extendedIdealOfDefinition Q f.toRingHom hP hU

end General

section Tate

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {T : Pair B}

/-- A morphism from a Tate Huber pair induces a spectral map of adic spectra. In a Tate ring an
open ideal is the unit ideal, and a ring homomorphism sends a finite generating set of the unit
ideal to another such set. No Tate assumption is needed on the target. -/
theorem isSpectralMap_spaComap_of_isTateRing (f : Hom S T) :
    IsSpectralMap f.spaComap := by
  classical
  apply f.isSpectralMap_spaComap
  intro U hU
  have htop : Ideal.span (U : Set A) = ⊤ := IsTateRing.eq_top_of_isOpen hU
  have htop' : Ideal.span (U.image f.toRingHom : Set B) = ⊤ := by
    rw [Finset.coe_image, ← Ideal.map_span, htop, Ideal.map_top]
  rw [htop']
  exact isOpen_univ

end Tate

end TauCeti.Huber.Pair.Hom

end
