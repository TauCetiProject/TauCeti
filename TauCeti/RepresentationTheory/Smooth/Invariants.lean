/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Smooth.Abelian

/-!
# Invariants of smooth representations under subgroups

For a subgroup `U` of a topological group `G`, in practice a compact open subgroup of a locally
profinite group, the `U`-invariants of a representation `V` of `G` are Mathlib's invariants of the
restriction, `V^U = (ρ.comp U.subtype).invariants`. On smooth representations this is the functor
`TauCeti.SmoothRep.invariantsFunctor U : SmoothRep A G ⥤ ModuleCat A`: the inclusion into
`Rep A G`, then restriction to `U`, then Mathlib's `Rep.invariantsFunctor`. It is `A`-linear and
left exact, since the inclusion of the smooth representations preserves kernels and the other two
functors preserve limits.

Invariants may be taken in stages. For a normal subgroup `S` of `G`, the `G`-invariants of `V` are
the `G ⧸ S`-invariants of the representation `Representation.quotientToInvariants ρ S` on `V^S`.
Applied to the restriction to `U`, for `U' ≤ U` with `U'` normal in `U`, this is
`V^U = (V^{U'})^{U/U'}`: the invariants of the restriction of `ρ|_U` to `U'.subgroupOf U` are the
`U'`-invariants of `ρ` (`Representation.invariants_comp_subtype_subgroupOf`). These statements
use no topology, so they live with the other generic results on invariants in
`TauCeti.RepresentationTheory.Invariants`, as
`Representation.map_subtype_invariants_quotientToInvariants` and
`Representation.quotientToInvariantsInvariantsEquiv`.

## Main definitions

* `TauCeti.SmoothRep.invariantsFunctor U`: the functor `V ↦ V^U` on smooth representations.

## Main results

* `TauCeti.SmoothRep.preservesFiniteLimits_invariantsFunctor`: taking `U`-invariants of smooth
  representations is left exact.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.2, Proposition 6(1) and its proof, p. 14.
-/

public section

open CategoryTheory Limits

universe w u v

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]

/-- The functor `V ↦ V^U` of `U`-invariants on smooth representations, for a subgroup `U` of `G`
(in practice compact open): the inclusion into `Rep A G`, then restriction to `U`, then Mathlib's
`Rep.invariantsFunctor`. Morphisms act by restriction. -/
noncomputable abbrev invariantsFunctor (U : Subgroup G) : SmoothRep.{w} A G ⥤ ModuleCat.{w} A :=
  ι A G ⋙ Rep.resFunctor U.subtype ⋙ Rep.invariantsFunctor A U

variable {A}

/-- **Invariants are left exact.** The inclusion `SmoothRep A G ⥤ Rep A G` preserves kernels,
hence finite limits, while restriction preserves limits and Mathlib's invariants functor is a
right adjoint. -/
instance preservesFiniteLimits_invariantsFunctor [SeparatelyContinuousMul G] (U : Subgroup G) :
    PreservesFiniteLimits (invariantsFunctor.{w} A U) :=
  haveI : PreservesFiniteLimits (ι.{w} A G) := Functor.preservesFiniteLimits_of_preservesKernels _
  inferInstance

end SmoothRep

end TauCeti
