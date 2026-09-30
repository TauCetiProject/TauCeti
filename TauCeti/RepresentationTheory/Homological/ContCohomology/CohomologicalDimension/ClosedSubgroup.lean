/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic

/-!
# Cohomological dimension at most one passes to closed subgroups

Let `G` be a profinite group and `U` a closed subgroup. If `cd_p G ≤ n` with `n ≤ 1`, then
`cd_p U ≤ n`.

For a discrete `p`-primary torsion `U`-module `M`, Shapiro's lemma identifies `Hⁿ⁺¹(U, M)` with
`Hⁿ⁺¹(G, Coind_U^G M)` in degrees one and two (`TauCeti.ContCohomology.explicitShapiro1`,
`TauCeti.ContCohomology.explicitShapiro2`), and the coinduced module is again a discrete `p`-primary
torsion `G`-module (`TauCeti.isPPrimaryTorsion_discreteCoind`), so `Hⁿ⁺¹(G, Coind_U^G M)` vanishes
when `cd_p G ≤ n`. Since the `p`-cohomological dimension of a compact group is detected in a single
degree (`TauCeti.cohomologicalDimensionLE_iff_forall_subsingleton_succ`), this vanishing of
`Hⁿ⁺¹(U, -)` is the statement `cd_p U ≤ n`. The coinduced module need not be finite when `U` is not
open, which is why the test on all discrete `p`-primary torsion modules is the one used.

This is the case `n ≤ 1` of the monotonicity of `cd_p` in a closed subgroup, `cd_p U ≤ cd_p G`
(NSW (3.3.5)); the general statement needs Shapiro's lemma in every degree. The case proved here is
what shows that closed subgroups of free pro-`p` groups are free pro-`p`.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isClosed_of_le_one`: the vanishing predicate `cd_p U ≤ n`
  for a closed subgroup `U` of a profinite group `G` with `cd_p G ≤ n`, when `n ≤ 1`.
* `TauCeti.cohomologicalDimensionAt_le_of_isClosed_of_le_one`: **`cd_p U ≤ n` when `cd_p G ≤ n`
  and `n ≤ 1`**, for `U` closed in the profinite group `G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.5).
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., Thm. 7.3.1.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **`cd_p ≤ n` passes to closed subgroups for `n ≤ 1`**, as the vanishing predicate: for `U`
closed in a profinite group `G` with `CohomologicalDimensionLE p G n` and `n ≤ 1`,
`CohomologicalDimensionLE p U n`. -/
theorem CohomologicalDimensionLE.of_isClosed_of_le_one {n : ℕ}
    (h : CohomologicalDimensionLE.{u} p G n) {U : Subgroup G} (hU : IsClosed (U : Set G))
    (hn : n ≤ 1) : CohomologicalDimensionLE.{u} p U n := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  rw [cohomologicalDimensionLE_iff_forall_subsingleton_succ] at h ⊢
  intro M _ _ _ _ _ hM
  -- `Hⁿ⁺¹(G, Coind_U^G M)` vanishes, since `Coind_U^G M` is discrete `p`-primary torsion.
  have hcoind := h (DiscreteCoind G U M) (isPPrimaryTorsion_discreteCoind G U M hM)
  -- `Hⁿ⁺¹(U, M) ≅ Hⁿ⁺¹(G, Coind_U^G M)` by Shapiro's lemma in degree `n + 1 ∈ {1, 2}`.
  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn
  · rw [Nat.zero_add] at hcoind
    have : Subsingleton (H1 U M) :=
      ((explicitShapiro1 G U M hU).symm.trans
        (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U M))).toEquiv.subsingleton
    exact (explicitH1AddEquivContinuousCohomology U M).symm.toEquiv.subsingleton
  · have : Subsingleton (H2 U M) :=
      ((explicitShapiro2 G U M hU).symm.trans
        (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U M))).toEquiv.subsingleton
    exact (explicitH2AddEquivContinuousCohomology U M).symm.toEquiv.subsingleton

/-- **`cd_p U ≤ n` for a closed subgroup `U` of a profinite group `G` with `cd_p G ≤ n`, when
`n ≤ 1`.** This is the monotonicity `cd_p U ≤ cd_p G` of the `p`-cohomological dimension in a
closed subgroup, in the range where Shapiro's lemma is available in the explicit low degrees. -/
theorem cohomologicalDimensionAt_le_of_isClosed_of_le_one {n : ℕ}
    (h : cohomologicalDimensionAt.{u} p G ≤ n) {U : Subgroup G} (hU : IsClosed (U : Set G))
    (hn : n ≤ 1) : cohomologicalDimensionAt.{u} p U ≤ n :=
  (cohomologicalDimensionAt_le_iff p U n).2
    (((cohomologicalDimensionAt_le_iff p G n).1 h).of_isClosed_of_le_one hU hn)

end TauCeti
