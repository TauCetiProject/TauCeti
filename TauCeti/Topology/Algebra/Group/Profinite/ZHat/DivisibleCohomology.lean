/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Divisible
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.CohomologicalDimension

/-!
# Second cohomology of the profinite integers with divisible coefficients

The second continuous cohomology of `TauCeti.zHat` vanishes for every divisible discrete
module, with arbitrary continuous action. Both Mathlib's canonical continuous cohomology and
the explicit inhomogeneous quotient are covered. Together with the torsion-coefficient
calculation, this supplies the divisible case of the procyclic second-cohomology computation.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Proposition 2.
-/

public section

namespace TauCeti.zHat

open ContCohomology

universe u

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction zHat.{u} M] [ContinuousSMul zHat.{u} M] [DivisibleBy M ℕ]

/-- Second canonical continuous cohomology of the profinite integers vanishes for every
divisible discrete coefficient module, with arbitrary continuous action. -/
theorem subsingleton_continuousCohomology_two_of_divisible :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ zHat.{u} M)) :=
  ContinuousCohomology.subsingleton_continuousCohomology_of_divisible_of_forall_isAddTorsion 1
    (fun A _ _ _ _ _ hA ↦ subsingleton_continuousCohomology_two_of_isAddTorsion A hA) M

/-- Second explicit continuous cohomology of the profinite integers vanishes for every
divisible discrete coefficient module, with arbitrary continuous action. -/
theorem subsingleton_H2_of_divisible : Subsingleton (H2 zHat.{u} M) := by
  have := subsingleton_continuousCohomology_two_of_divisible M
  exact (explicitH2AddEquivContinuousCohomology zHat.{u} M).injective.subsingleton

end TauCeti.zHat
