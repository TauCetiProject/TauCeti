/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Cohomological dimension at most one passes to open subgroups

Let `G` be a profinite group and `U` an open subgroup. If `cd_p G ≤ 1`, then `cd_p U ≤ 1`.

This is the degree-one case of the monotonicity of `cd_p` in the subgroup, `cd_p H ≤ cd_p G` for
closed `H ≤ G` (NSW (3.3.5)). Only this case is proved here; it is what
`TauCeti.Topology.Algebra.Group.Profinite.Free.OpenSubgroup` uses to show that open subgroups of
free pro-`p` groups are again free pro-`p`.

## Main results

* `TauCeti.CohomologicalDimensionLE.one_of_openSubgroup`: the vanishing predicate `cd_p U ≤ 1` for
  an open subgroup `U` of a profinite group `G` with `cd_p G ≤ 1`.
* `TauCeti.cohomologicalDimensionAt_le_one_of_openSubgroup`: **`cd_p U ≤ 1` when `cd_p G ≤ 1`**,
  for `U` open in the profinite group `G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.5).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **`cd_p ≤ 1` passes to open subgroups**, as the vanishing predicate: for `U` open in a profinite
group `G` with `CohomologicalDimensionLE p G 1` and `p ≠ 0`, `CohomologicalDimensionLE p U 1`. -/
theorem CohomologicalDimensionLE.one_of_openSubgroup (hp : p ≠ 0)
    (h : CohomologicalDimensionLE.{u} p G 1) (U : OpenSubgroup G) :
    CohomologicalDimensionLE.{u} p U.toSubgroup 1 := by
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  -- `cd_p ≤ 1` is detected by the vanishing of `H²` on finite `p`-primary coefficients.
  rw [cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ hp] at h ⊢
  intro M _ _ _ _ _ _ hM
  -- `H²(G, Coind_U^G M)` vanishes, since `Coind_U^G M` is finite (`U` has finite index) and
  -- `p`-primary.
  have hcoind := h (DiscreteCoind G U.toSubgroup M)
    (isPPrimaryTorsion_discreteCoind G U.toSubgroup M hM)
  -- `H²(U, M) ≅ H²(G, Coind_U^G M)` by Shapiro's lemma in degree two.
  have : Subsingleton (H2 U.toSubgroup M) :=
    ((explicitShapiro2 G U.toSubgroup M U.isClosed).symm.trans
      (explicitH2AddEquivContinuousCohomology G
        (DiscreteCoind G U.toSubgroup M))).toEquiv.subsingleton
  exact (explicitH2AddEquivContinuousCohomology U.toSubgroup M).symm.toEquiv.subsingleton

/-- **`cd_p U ≤ 1` for an open subgroup `U` of a profinite group `G` with `cd_p G ≤ 1`**, for
`p ≠ 0`. This is the degree-one case of the monotonicity `cd_p H ≤ cd_p G` of the `p`-cohomological
dimension in a closed subgroup `H`. -/
theorem cohomologicalDimensionAt_le_one_of_openSubgroup (hp : p ≠ 0)
    (h : cohomologicalDimensionAt.{u} p G ≤ 1) (U : OpenSubgroup G) :
    cohomologicalDimensionAt.{u} p U.toSubgroup ≤ 1 :=
  mod_cast (cohomologicalDimensionAt_le_iff p U.toSubgroup 1).2
    (CohomologicalDimensionLE.one_of_openSubgroup hp
      ((cohomologicalDimensionAt_le_iff p G 1).1 (by exact_mod_cast h)) U)

end TauCeti
