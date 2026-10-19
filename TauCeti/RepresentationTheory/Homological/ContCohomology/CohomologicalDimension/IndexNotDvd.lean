/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Annihilation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Restriction
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Cohomological dimension and subgroups of index prime to `p`

Let `G` be a profinite group and `p` a prime. Restriction to an open subgroup `U` of index prime to
`p` is injective on the cohomology of every discrete `p`-primary torsion `G`-module, in every
positive degree: a class killed by restriction to `U` is killed by `[G : U]`
(`TauCeti.ContinuousCohomology.index_nsmul_eq_zero_of_res_eq_zero`), and it is also killed by a
power of `p`, so it is zero. The same holds for a closed subgroup `H` all of whose open
neighbourhoods `V ⊇ H` have index prime to `p`: a class restricting to zero on `H` already
restricts to zero on some open `V ⊇ H`, by the colimit description of the cohomology of a closed
subgroup (`TauCeti.ContinuousCohomology.exists_openSubgroup_le_res_eq_zero`).

Consequently `cd_p G ≤ cd_p U` for an open subgroup `U` of index prime to `p` of a compact group,
and `cd_p G ≤ cd_p H` for such a closed subgroup `H` of a profinite group: both follow from the one
observation that vanishing transfers from a subgroup on which restriction is injective in every
positive degree (`TauCeti.CohomologicalDimensionLE.of_forall_res_injective`). Combined with
closed-subgroup monotonicity from Shapiro's lemma, this gives `cd_p G = cd_p H` for such a closed
subgroup, and in particular for an open subgroup of index prime to `p`. These equalities hold in
`ℕ∞`, including infinite cohomological dimension. The closed-subgroup statement is the one a
Sylow pro-`p` subgroup satisfies, since
each of its open neighbourhoods has index prime to `p`; the comparison of `cd_p G` with the
cohomological dimension of a Sylow pro-`p` subgroup is where these results are used.

## Main results

* `TauCeti.ContinuousCohomology.res_injective_of_not_dvd_index`: for a compact group `G`, an open
  subgroup `U` of index prime to `p` and a discrete `p`-primary torsion representation `X`,
  restriction `Hⁿ⁺¹(G, X) → Hⁿ⁺¹(U, X)` is injective.
* `TauCeti.ContinuousCohomology.res_injective_of_forall_not_dvd_index`: the same for a closed
  subgroup `H` of a profinite group all of whose open neighbourhoods have index prime to `p`, for
  smooth discrete `p`-primary torsion `X`.
* `TauCeti.cohomologicalDimensionAt_le_of_not_dvd_index`: **`cd_p G ≤ cd_p U`** for an open
  subgroup `U` of a compact group `G` with `[G : U]` prime to `p`.
* `TauCeti.cohomologicalDimensionAt_le_of_isClosed_of_forall_not_dvd_index`: **`cd_p G ≤ cd_p H`**
  for such a closed subgroup `H` of a profinite group `G`.
* `TauCeti.cohomologicalDimensionAt_eq_of_isClosed_of_forall_not_dvd_index`: **`cd_p G = cd_p H`**
  for such a closed subgroup, with no finiteness assumption on cohomological dimension.
* `TauCeti.cohomologicalDimensionAt_eq_of_not_dvd_index`: **`cd_p G = cd_p U`** for an open
  subgroup of index prime to `p` in a profinite group.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14 and its Corollary.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.5) and
  (3.3.6).
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

namespace ContinuousCohomology

open _root_.ContinuousCohomology

variable {p : ℕ} {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {X : TopRep k G}

/-- **Restriction to an open subgroup of index prime to `p` is injective** on the cohomology of a
discrete `p`-primary torsion representation `X` of a compact group `G`, in every positive degree. -/
theorem res_injective_of_not_dvd_index [DiscreteTopology X.V] (hp : p.Prime)
    (hX : IsPPrimaryTorsion p X.V) (U : OpenSubgroup G) (hU : ¬ p ∣ U.toSubgroup.index) (n : ℕ) :
    Function.Injective (res U.toSubgroup X (n + 1)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- a class killed by restriction to `U` is killed by `[G : U]` and by a power of `p`
  obtain ⟨m, hm⟩ := isPPrimaryTorsion_iff.1 (isPPrimaryTorsion_continuousCohomology X hX (n + 1)) x
  exact (nsmul_eq_zero_iff_of_coprime ((hp.coprime_iff_not_dvd.2 hU).pow_left m)).1
    ⟨hm, index_nsmul_eq_zero_of_res_eq_zero U.isOpen hx⟩

variable [TotallyDisconnectedSpace G]

/-- **Restriction to a closed subgroup whose open neighbourhoods all have index prime to `p` is
injective** on the cohomology of a smooth discrete `p`-primary torsion representation `X` of a
profinite group `G`, in every positive degree. -/
theorem res_injective_of_forall_not_dvd_index (hp : p.Prime) (hX : IsSmoothDiscrete k X)
    (hX' : IsPPrimaryTorsion p X.V) {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hind : ∀ V : OpenSubgroup G, H ≤ V → ¬ p ∣ V.toSubgroup.index) (n : ℕ) :
    Function.Injective (res H X (n + 1)).hom := by
  have := hX.discreteTopology
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- a class restricting to zero on `H` restricts to zero on some open `V ⊇ H`
  obtain ⟨V, hHV, hV⟩ := exists_openSubgroup_le_res_eq_zero hX hH hx
  exact (injective_iff_map_eq_zero _).1 (res_injective_of_not_dvd_index hp hX' V (hind V hHV) n) x
    hV

end ContinuousCohomology

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **`cd_p G ≤ cd_p U` for an open subgroup `U` of index prime to `p`**, as the vanishing
predicate: for `U` open in a compact group `G` with `¬ p ∣ [G : U]`,
`CohomologicalDimensionLE p U n` implies `CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_not_dvd_index (hp : p.Prime) (U : OpenSubgroup G)
    (hU : ¬ p ∣ U.toSubgroup.index) {n : ℕ} (h : CohomologicalDimensionLE.{v} p U.toSubgroup n) :
    CohomologicalDimensionLE.{v} p G n :=
  h.of_forall_res_injective fun _ _ _ _ _ _ hM i ↦
    ContinuousCohomology.res_injective_of_not_dvd_index hp hM U hU i

/-- **`cd_p G ≤ cd_p U` for an open subgroup `U` of index prime to `p`** (Serre, *Galois
Cohomology*, I §3.3, Prop. 14): for `U` open in a compact group `G` with `¬ p ∣ [G : U]`, the
`p`-cohomological dimension of `G` is at most that of `U`. -/
theorem cohomologicalDimensionAt_le_of_not_dvd_index (hp : p.Prime) (U : OpenSubgroup G)
    (hU : ¬ p ∣ U.toSubgroup.index) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p U.toSubgroup :=
  cohomologicalDimensionAt_le_of_forall_res_injective fun _ _ _ _ _ _ hM i ↦
    ContinuousCohomology.res_injective_of_not_dvd_index hp hM U hU i

variable [TotallyDisconnectedSpace G]

/-- **`cd_p G ≤ cd_p H` for a closed subgroup `H` whose open neighbourhoods all have index prime to
`p`**, as the vanishing predicate: for `H` closed in a profinite group `G` with every open `V ⊇ H`
of index prime to `p`, `CohomologicalDimensionLE p H n` implies `CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_isClosed_of_forall_not_dvd_index (hp : p.Prime)
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hind : ∀ V : OpenSubgroup G, H ≤ V → ¬ p ∣ V.toSubgroup.index) {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p H n) : CohomologicalDimensionLE.{v} p G n :=
  h.of_forall_res_injective fun M _ _ _ _ _ hM i ↦
    ContinuousCohomology.res_injective_of_forall_not_dvd_index hp
      (ofDiscreteModule_isSmoothDiscrete ℤ G M) hM hH hind i

/-- **`cd_p G ≤ cd_p H` for a closed subgroup `H` whose open neighbourhoods all have index prime to
`p`** (Serre, *Galois Cohomology*, I §3.3, Cor. to Prop. 14): for `H` closed in a profinite group
`G` with every open `V ⊇ H` of index prime to `p`, the `p`-cohomological dimension of `G` is at
most that of `H`. -/
theorem cohomologicalDimensionAt_le_of_isClosed_of_forall_not_dvd_index (hp : p.Prime)
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hind : ∀ V : OpenSubgroup G, H ≤ V → ¬ p ∣ V.toSubgroup.index) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p H :=
  cohomologicalDimensionAt_le_of_forall_res_injective fun M _ _ _ _ _ hM i ↦
    ContinuousCohomology.res_injective_of_forall_not_dvd_index hp
      (ofDiscreteModule_isSmoothDiscrete ℤ G M) hM hH hind i

/-- **`cd_p G = cd_p H` for a closed subgroup whose open neighbourhoods have index prime to
`p`**. The equality is in
`ℕ∞` and does not assume that either cohomological dimension is finite. -/
theorem cohomologicalDimensionAt_eq_of_isClosed_of_forall_not_dvd_index (hp : p.Prime)
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hind : ∀ V : OpenSubgroup G, H ≤ V → ¬ p ∣ V.toSubgroup.index) :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{u} p H :=
  le_antisymm (cohomologicalDimensionAt_le_of_isClosed_of_forall_not_dvd_index hp hH hind)
    (cohomologicalDimensionAt_le_of_isClosed hH)

/-- **An open subgroup of index prime to `p` has the same `p`-cohomological dimension as the
ambient profinite group** (NSW (3.3.5)). Unlike the equality for arbitrary open subgroups, this
holds even when the cohomological dimension is infinite. -/
theorem cohomologicalDimensionAt_eq_of_not_dvd_index (hp : p.Prime) (U : OpenSubgroup G)
    (hU : ¬ p ∣ U.toSubgroup.index) :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{u} p U.toSubgroup :=
  cohomologicalDimensionAt_eq_of_isClosed_of_forall_not_dvd_index hp U.isClosed
    fun _ hUV hdiv ↦ hU (hdiv.trans (Subgroup.index_dvd_of_le hUV))

end TauCeti
