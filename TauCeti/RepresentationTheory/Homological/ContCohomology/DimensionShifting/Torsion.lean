/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DimensionShifting.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion

/-!
# Primary torsion under dimension shifting

For a compact group and a subgroup `U`, the quotient `Coind_U^G M ⧸ M` by the image of the unit of
coinduction, in particular the dimension-shifting quotient `Coind_1^G M ⧸ M`, preserves `p`-primary
torsion. This lets the dimension-shifting sequence stay within the coefficient class used to
define `p`-cohomological dimension.

The compactness assumption matters: a locally constant map on an infinite discrete space may
take values of unbounded `p`-power order.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §3, (3.3.2).
-/

public section

namespace TauCeti.ContCohomology

variable {p : ℕ} (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G] [CompactSpace G]
  (U : Subgroup G) (M : Type*) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The quotient `Coind_U^G M ⧸ M` remains `p`-primary torsion whenever `M` is `p`-primary
torsion. -/
theorem isPPrimaryTorsion_coindQuotient (hM : IsPPrimaryTorsion p M) :
    IsPPrimaryTorsion p (CoindQuotient G U M) :=
  (isPPrimaryTorsion_discreteCoind G U M hM).of_surjective
    (CoindQuotient.mk G U M) CoindQuotient.mk_surjective

end TauCeti.ContCohomology
