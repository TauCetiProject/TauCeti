/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Rep.InvariantsCoproducts
public import TauCeti.RepresentationTheory.Smooth.Colimits
public import TauCeti.RepresentationTheory.Smooth.Invariants

/-!
# Invariants of smooth representations commute with direct sums

Let `G` be a topological group, `A` a commutative ring and `U` a subgroup of `G` (in practice a
compact open subgroup of a locally profinite group). The functor
`TauCeti.SmoothRep.invariantsFunctor A U` of `U`-invariants on smooth representations preserves
coproducts, that is, `(⨁ i, V i)^U = ⨁ i, (V i)^U`. No hypothesis on `U` is needed.

The functor is the inclusion into `Rep A G`, which preserves colimits
(`TauCeti.SmoothRep.preservesColimitsOfSize_ι`), followed by restriction to `U`, a left adjoint,
and Mathlib's invariants functor, which preserves coproducts by
`Rep.preservesColimitsOfShape_discrete_invariantsFunctor`. Since `invariantsFunctor A U` is an
abbreviation for this composite, instance search finds the coproduct preservation from these
instances, with no further declaration; the `example` below records it. Together with
`TauCeti.SmoothRep.preservesFilteredColimits_invariantsFunctor` (for compact `U`) this is the
statement that invariants commute with direct sums and filtered colimits.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §3.3, Proposition 10(2), p. 17.
-/

public section

open CategoryTheory Limits

universe w u v

namespace TauCeti

namespace SmoothRep

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- **Invariants commute with direct sums**: for any subgroup `U`, the functor of `U`-invariants
on smooth representations preserves coproducts. -/
example (α : Type w) (U : Subgroup G) :
    PreservesColimitsOfShape (Discrete α) (invariantsFunctor.{w} A U) :=
  inferInstance

end SmoothRep

end TauCeti
