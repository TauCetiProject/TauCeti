/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.RingTheory.Flat.GenericRank

/-!
# Rank and function field degree for finite flat affine morphisms

For a finite flat morphism between affine integral schemes, the rank at every point of the
target equals the degree of the extension of fraction fields. The fraction fields may be
realized by any compatible pair of fraction rings; this is useful when the field extension
is expressed through the function fields of projective curves and affine charts.

The local rank is Mathlib's `Scheme.Hom.finrank`. Its affine formula reduces the result to
the generic-rank calculation for finite flat modules and the invariance of dimension under
passage to fraction rings.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA).
-/

public section

open AlgebraicGeometry

universe u v w

namespace TauCeti.AlgebraicGeometry

/-- The rank of a finite flat morphism of integral affine schemes is the degree of the induced
extension of fraction fields. The algebra structures on `K` and `L` record the compatibility
of this extension with the map of coordinate rings. -/
theorem finrank_SpecMap_eq_finrank_fractionRing
    {R S : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [CommRing S]
    [CommRing K] [CommRing L] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L] [Module.Flat R S] [Module.Finite R S]
    (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank p = Module.finrank K L := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (TauCeti.rankAtStalk_eq_finrank_of_isDomain p).trans
    (IsFractionRing.finrank_eq R K S L).symm

end TauCeti.AlgebraicGeometry
