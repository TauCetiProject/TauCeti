/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Quotient
public import TauCeti.Topology.Algebra.Group.Torsion

/-!
# Primary torsion of discrete coinduction

Over a compact group, a locally constant function to a discrete group has finite image.
Consequently coinduction preserves `p`-primary torsion, even when the source group has unbounded
`p`-power exponent. The result applies to every subgroup, and passes to the cokernel
`Coind_U^G M ⧸ M` of the unit of coinduction, in particular to the dimension-shifting quotient
`Coind_1^G M ⧸ M`. This lets the dimension-shifting sequence stay within the coefficient class used
to define `p`-cohomological dimension.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §3, (3.3.2).
-/

public section

namespace TauCeti

variable {p : ℕ} (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
  (U : Subgroup G) (M : Type*) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

section DiscreteCoind

variable [DistribMulAction U M]

/-- Discrete coinduction from a subgroup preserves `p`-primary torsion over a compact group. -/
theorem isPPrimaryTorsion_discreteCoind (hM : IsPPrimaryTorsion p M) :
    IsPPrimaryTorsion p (DiscreteCoind G U M) := by
  refine isPPrimaryTorsion_iff.2 fun f ↦ ?_
  let cf : C(G, M) := ⟨⇑f,
    (IsLocallyConstant.iff_continuous _).1 (DiscreteCoind.isLocallyConstant f)⟩
  obtain ⟨k, hk⟩ := isPPrimaryTorsion_iff.1 (hM.continuousMap G) cf
  refine ⟨k, DiscreteCoind.ext fun g ↦ ?_⟩
  -- `cf` has the same values as `f`, so evaluating `hk` at `g` gives `p ^ k • f g = 0`.
  have hkg : p ^ k • f g = 0 := by
    simpa [cf] using DFunLike.congr_fun hk g
  rw [DiscreteCoind.coe_zero, Pi.zero_apply]
  exact (DiscreteCoind.coe_smul_scalar (p ^ k) f g).trans hkg

end DiscreteCoind

namespace ContCohomology

variable [ContinuousMul G] [DistribMulAction G M] [ContinuousSMul G M]

/-- The quotient `Coind_U^G M ⧸ M` remains `p`-primary torsion whenever `M` is `p`-primary
torsion. -/
theorem isPPrimaryTorsion_coindQuotient (hM : IsPPrimaryTorsion p M) :
    IsPPrimaryTorsion p (CoindQuotient G U M) :=
  (isPPrimaryTorsion_discreteCoind G U M hM).of_surjective
    (CoindQuotient.mk G U M) CoindQuotient.mk_surjective

end ContCohomology

end TauCeti
