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

Let `G` be a profinite group and `U` a closed subgroup. Then `cd_p U ≤ cd_p G` and
`scd_p U ≤ scd_p G`: both the ordinary and the strict `p`-cohomological dimension are monotone in a
closed subgroup (NSW (3.3.5)).

For a discrete `p`-primary torsion `U`-module `M`, Shapiro's lemma identifies `Hⁿ⁺¹(U, M)` with
`Hⁿ⁺¹(G, Coind_U^G M)` in every degree (`TauCeti.ContinuousCohomology.bijective_shapiroMap`), and
the coinduced module is again a discrete `p`-primary torsion `G`-module
(`TauCeti.isPPrimaryTorsion_discreteCoind`), so `Hⁿ⁺¹(G, Coind_U^G M)` vanishes when `cd_p G ≤ n`.
Since the `p`-cohomological dimension of a compact group is detected in a single degree
(`TauCeti.cohomologicalDimensionLE_iff_forall_subsingleton_succ`), this vanishing of `Hⁿ⁺¹(U, -)`
is the statement `cd_p U ≤ n`. The coinduced module need not be finite when `U` is not open, which
is why the test on all discrete `p`-primary torsion modules is the one used.

The case `cd_p G ≤ 1` is what shows that closed subgroups of free pro-`p` groups are free pro-`p`.

The strict dimension uses Shapiro's lemma for all discrete coefficients rather than only the
`p`-primary torsion ones. For an arbitrary discrete `U`-module `M`, the inverse of Shapiro's
isomorphism `Hⁱ(G, Coind_U^G M) ≅ Hⁱ(U, M)` (`TauCeti.ContinuousCohomology.shapiroIso`) is additive
and injective, so it carries the `p`-primary component of `Hⁱ(U, M)` injectively into that of
`Hⁱ(G, Coind_U^G M)`, which vanishes for `i > n` when `scd_p G ≤ n`. Here no single-degree
reduction is needed, since the strict predicate already ranges over all discrete coefficients.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isClosed`: the vanishing predicate `cd_p U ≤ n` for a closed
  subgroup `U` of a profinite group `G` with `cd_p G ≤ n`.
* `TauCeti.cohomologicalDimensionAt_le_of_isClosed`: **`cd_p U ≤ cd_p G`** in `ℕ∞`, for `U` closed
  in the profinite group `G`.
* `TauCeti.StrictCohomologicalDimensionLE.of_isClosed`: the strict vanishing predicate
  `scd_p U ≤ n` for a closed subgroup `U` of a profinite group `G` with `scd_p G ≤ n`.
* `TauCeti.strictCohomologicalDimensionAt_le_of_isClosed`: **`scd_p U ≤ scd_p G`** in `ℕ∞`, for `U`
  closed in the profinite group `G`; in particular for every open subgroup.

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

/-- **`scd_p ≤ n` passes to closed subgroups**, as the vanishing predicate: for `U` closed in a
profinite group `G` with `StrictCohomologicalDimensionLE p G n`,
`StrictCohomologicalDimensionLE p U n`. -/
theorem StrictCohomologicalDimensionLE.of_isClosed {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{u} p G n) {U : Subgroup G} (hU : IsClosed (U : Set G)) :
    StrictCohomologicalDimensionLE.{u} p U n := by
  refine strictCohomologicalDimensionLE_iff.2 fun M _ _ _ _ _ i hi ↦ ?_
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun x ⟨k, hk⟩ ↦ ?_
  -- the inverse of Shapiro's isomorphism sends `x` into the `p`-primary component of
  -- `Hⁱ(G, Coind_U^G M)`, which vanishes
  set e := shapiroIso U hU M i
  have hx : e.inv x ∈ AddCommGroup.primaryComponent _ p :=
    ⟨k, by rw [← map_nsmul, hk, _root_.map_zero]⟩
  rw [strictCohomologicalDimensionLE_iff.1 h (DiscreteCoind G U M) i hi, AddSubgroup.mem_bot]
    at hx
  rw [← e.inv_hom_id_apply x, hx, _root_.map_zero]

/-- **`scd_p U ≤ scd_p G` for a closed subgroup `U` of a profinite group `G`** (NSW (3.3.5)): the
strict `p`-cohomological dimension is monotone in a closed subgroup, as an inequality in `ℕ∞`. In
particular it applies to every open subgroup, which is closed. -/
theorem strictCohomologicalDimensionAt_le_of_isClosed {U : Subgroup G}
    (hU : IsClosed (U : Set G)) :
    strictCohomologicalDimensionAt.{u} p U ≤ strictCohomologicalDimensionAt.{u} p G := by
  induction hcd : strictCohomologicalDimensionAt.{u} p G using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (strictCohomologicalDimensionAt_le_iff p U n).2
      (((strictCohomologicalDimensionAt_le_iff p G n).1 hcd.le).of_isClosed hU)

end TauCeti
