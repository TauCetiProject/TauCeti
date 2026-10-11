/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Rank and fraction-ring dimension for finite flat affine morphisms

For a finite flat affine morphism with integral target, the rank at every target point equals
the dimension after passing to compatible fraction rings. When the source is also integral,
these fraction rings are fields, and the dimension is the function-field extension degree.

The local rank is Mathlib's `Scheme.Hom.finrank`. Its affine formula reduces the result to
Mathlib's fibre-rank calculation for finite flat modules and the invariance of dimension under
passage to fraction rings.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA).
-/

public section

open AlgebraicGeometry

universe u v w

namespace TauCeti.AlgebraicGeometry

/-- The rank of a finite flat affine morphism with integral target is the dimension after
passing to fraction rings. If `S` is a domain, `K` and `L` are fields and this is the degree
of the induced function-field extension. The algebra structures record compatibility with the
map of coordinate rings. -/
theorem finrank_SpecMap_eq_finrank_fractionRing
    {R S : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [CommRing S]
    [CommRing K] [CommRing L] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L] [Module.Flat R S] [Module.Finite R S]
    (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank p = Module.finrank K L := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  exact ((Module.rankAtStalk_eq p).trans p.asIdeal.finrank_fiber_eq_finrank).trans
    (IsFractionRing.finrank_eq R K S L).symm

end TauCeti.AlgebraicGeometry
