/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso

/-!
# Cardinalities of the explicit cohomology of a discrete representation

For a discrete representation `X : TopRep k G` the explicit groups `H⁰(G, X.V)`, `H¹(G, X.V)` and
`H²(G, X.V)` are in bijection with the continuous cohomology `continuousCohomology n X` in degrees
`0`, `1` and `2`, so they have the same cardinality. The bijection in degree `1` needs the action
of `G` on `X.V` to be continuous, and the one in degree `2` needs in addition `G` to be locally
compact. These cardinality comparisons are what one
needs to transport counting arguments about the explicit long exact sequence to the canonical
cohomology.

## Main results

* `TopRep.natCard_H0_eq_natCard_continuousCohomology`,
  `TopRep.natCard_H1_eq_natCard_continuousCohomology`,
  `TopRep.natCard_H2_eq_natCard_continuousCohomology`: the cardinality of the explicit `Hⁿ` of a
  discrete representation is that of `continuousCohomology n X`, for `n = 0, 1, 2`; degrees `1`
  and `2` assume that `G` acts continuously on `X.V`, and degree `2` that `G` is locally compact.
-/

public section

open CategoryTheory TauCeti.ContCohomology

attribute [local instance] TopRep.distribMulAction

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k : Type v} [Ring k] [TopologicalSpace k] (X : TopRep.{u, v, u} k G) [DiscreteTopology X.V]

/-- The explicit `H⁰` of the carrier of a discrete representation has the cardinality of the
continuous cohomology `H⁰`. -/
theorem TopRep.natCard_H0_eq_natCard_continuousCohomology :
    Nat.card (H0 G X.V) = Nat.card (continuousCohomology 0 X) :=
  Nat.card_congr
    (((explicitH0IsoContinuousCohomology G X.V).toContinuousLinearEquiv.toAddEquiv).trans
      (ofDiscreteModuleRestrictScalarsIntEquiv X 0)).toEquiv

/-- The explicit `H¹` of the carrier of a discrete representation has the cardinality of the
continuous cohomology `H¹`, when `G` acts continuously on it. -/
theorem TopRep.natCard_H1_eq_natCard_continuousCohomology [ContinuousSMul G X.V] :
    Nat.card (H1 G X.V) = Nat.card (continuousCohomology 1 X) :=
  Nat.card_congr X.explicitH1AddEquivContinuousCohomologyOfDiscrete.toEquiv

/-- The explicit `H²` of the carrier of a discrete representation has the cardinality of the
continuous cohomology `H²`, when `G` acts continuously on it and is locally compact. -/
theorem TopRep.natCard_H2_eq_natCard_continuousCohomology [ContinuousSMul G X.V]
    [LocallyCompactSpace G] :
    Nat.card (H2 G X.V) = Nat.card (continuousCohomology 2 X) :=
  Nat.card_congr X.explicitH2AddEquivContinuousCohomologyOfDiscrete.toEquiv
