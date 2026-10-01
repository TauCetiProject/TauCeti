/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees

/-!
# Cohomological dimension passes to closed subgroups

Let `G` be a profinite group and `U` a closed subgroup. Then `cd_p U ≤ cd_p G`: the
`p`-cohomological dimension is monotone in a closed subgroup (NSW (3.3.5)).

For a discrete `p`-primary torsion `U`-module `M`, Shapiro's lemma identifies `Hⁿ⁺¹(U, M)` with
`Hⁿ⁺¹(G, Coind_U^G M)` in every degree (`TauCeti.ContinuousCohomology.bijective_shapiroMap`), and
the coinduced module is again a discrete `p`-primary torsion `G`-module
(`TauCeti.isPPrimaryTorsion_discreteCoind`), so `Hⁿ⁺¹(G, Coind_U^G M)` vanishes when `cd_p G ≤ n`.
Since the `p`-cohomological dimension of a compact group is detected in a single degree
(`TauCeti.cohomologicalDimensionLE_iff_forall_subsingleton_succ`), this vanishing of `Hⁿ⁺¹(U, -)`
is the statement `cd_p U ≤ n`. The coinduced module need not be finite when `U` is not open, which
is why the test on all discrete `p`-primary torsion modules is the one used.

The case `cd_p G ≤ 1` is what shows that closed subgroups of free pro-`p` groups are free pro-`p`.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isClosed`: the vanishing predicate `cd_p U ≤ n` for a closed
  subgroup `U` of a profinite group `G` with `cd_p G ≤ n`.
* `TauCeti.cohomologicalDimensionAt_le_of_isClosed`: **`cd_p U ≤ cd_p G`** in `ℕ∞`, for `U` closed
  in the profinite group `G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.5).
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., Thm. 7.3.1.
-/

public section

namespace TauCeti

open ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **`cd_p ≤ n` passes to closed subgroups**, as the vanishing predicate: for `U` closed in a
profinite group `G` with `CohomologicalDimensionLE p G n`, `CohomologicalDimensionLE p U n`. -/
theorem CohomologicalDimensionLE.of_isClosed {n : ℕ} (h : CohomologicalDimensionLE.{u} p G n)
    {U : Subgroup G} (hU : IsClosed (U : Set G)) : CohomologicalDimensionLE.{u} p U n := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  rw [cohomologicalDimensionLE_iff_forall_subsingleton_succ] at h ⊢
  intro M _ _ _ _ _ hM
  -- `Hⁿ⁺¹(G, Coind_U^G M)` vanishes, since `Coind_U^G M` is discrete `p`-primary torsion, and
  -- `Hⁿ⁺¹(U, M) ≅ Hⁿ⁺¹(G, Coind_U^G M)` by Shapiro's lemma.
  have := h (DiscreteCoind G U M) (isPPrimaryTorsion_discreteCoind G U M hM)
  exact (subsingleton_continuousCohomology_discreteCoind_iff U hU M (n + 1)).1 this

/-- **`cd_p U ≤ cd_p G` for a closed subgroup `U` of a profinite group `G`**: the `p`-cohomological
dimension is monotone in a closed subgroup, as an inequality in `ℕ∞`. -/
theorem cohomologicalDimensionAt_le_of_isClosed {U : Subgroup G} (hU : IsClosed (U : Set G)) :
    cohomologicalDimensionAt.{u} p U ≤ cohomologicalDimensionAt.{u} p G := by
  induction hcd : cohomologicalDimensionAt.{u} p G using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (cohomologicalDimensionAt_le_iff p U n).2
      (((cohomologicalDimensionAt_le_iff p G n).1 hcd.le).of_isClosed hU)

end TauCeti
