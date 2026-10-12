/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Cohomological dimension read on the explicit cohomology

The vanishing predicate `CohomologicalDimensionLE p G n` is stated against Mathlib's continuous
cohomology `continuousCohomology i (ofDiscreteModule ℤ G M)`, while the low-degree theory of
`LowDegree.lean` works with the explicit cocycle models `H¹(G, M)` and `H²(G, M)`. This file
transfers the vanishing through the comparison of `CohomologyComparison.lean`: for a locally
compact group `G` with `cd_p G ≤ 1`, the explicit `H²(G, A)` of every discrete `p`-primary
`G`-module `A` is trivial.

The coefficients live in the universe of `G`: the continuous-cohomology side needs them in a
universe containing that of `G`, and the explicit comparison is stated for coefficients in
exactly that universe.

## Main results

* `TauCeti.CohomologicalDimensionLE.subsingleton_H2`: `cd_p G ≤ 1` kills the explicit `H²` of
  every discrete `p`-primary `G`-module.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- **`cd_p G ≤ 1` kills the explicit `H²`** of every discrete `p`-primary `G`-module. -/
theorem CohomologicalDimensionLE.subsingleton_H2 (hcd : CohomologicalDimensionLE.{u} p G 1)
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
    [ContinuousSMul G A] (hA : IsPPrimaryTorsion p A) : Subsingleton (H2 G A) :=
  have := cohomologicalDimensionLE_iff.mp hcd A hA 2 one_lt_two
  (explicitH2AddEquivContinuousCohomology G A).toEquiv.subsingleton

end TauCeti
