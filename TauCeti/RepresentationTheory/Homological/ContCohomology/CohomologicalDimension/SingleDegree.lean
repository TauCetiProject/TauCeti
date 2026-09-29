/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DimensionShifting.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCoefficients

/-!
# Cohomological dimension is detected in a single degree

For a compact group `G`, the vanishing predicate `CohomologicalDimensionLE p G n`, which asks for
`Hⁱ(G, M) = 0` in every degree `i > n` and for every discrete `p`-primary torsion `G`-module `M`,
holds as soon as the single degree `n + 1` vanishes for every such `M`. Dimension shifting supplies
the induction step: `Hⁱ⁺¹(G, M) ≅ Hⁱ(G, Coind_1^G M ⧸ M)` for `i ≥ 1`
(`TauCeti.ContCohomology.dimensionShiftIso`), and the shifted module `Coind_1^G M ⧸ M` is again a
discrete `p`-primary torsion module
(`TauCeti.ContCohomology.isPPrimaryTorsion_dimensionShiftQuotient`), so vanishing in degree `i` for
every module of the class gives vanishing in degree `i + 1` for every module of the class. The
shifted module need not be finite even when `M` is, which is why the statement quantifies over all
discrete `p`-primary torsion modules; the single-degree test on the finite modules then follows
because, in each fixed degree, the vanishing of `Hⁱ(G, M)` for a discrete `p`-primary torsion `M`
is detected on the finite discrete `p`-primary `G`-modules
(`TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite`).

The two tests are recorded for the predicate and for the invariant `cd_p G`. They are the standard
reductions of Serre, *Galois Cohomology*, I §3.2, Prop. 11, and of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (3.3.2), before the passage to simple modules, which for a pro-`p`
group is the further reduction to the single module `𝔽_p`.

## Main results

* `TauCeti.cohomologicalDimensionLE_iff_forall_subsingleton_succ`: `CohomologicalDimensionLE p G n`
  holds exactly when `Hⁿ⁺¹(G, M)` vanishes for every discrete `p`-primary torsion `G`-module `M`.
* `TauCeti.cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ`: the same test on the
  finite modules, for `p ≠ 0`.
* `TauCeti.cohomologicalDimensionAt_le_iff_forall_subsingleton_succ` and
  `TauCeti.cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ`: the two tests for
  `cd_p G ≤ n`.
* `TauCeti.cohomologicalDimensionAt_eq_zero_iff_forall_subsingleton_one` and
  `TauCeti.cohomologicalDimensionAt_eq_zero_iff_forall_finite_subsingleton_one`: `cd_p G = 0` is
  detected by `H¹`, on all or only finite discrete `p`-primary torsion modules respectively.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.2, Prop. 11.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- **Vanishing in one degree gives vanishing above it.** For a compact group `G`, the predicate
`CohomologicalDimensionLE p G n` holds exactly when `Hⁿ⁺¹(G, M)` vanishes for every discrete
`p`-primary torsion `G`-module `M`: dimension shifting through `Coind_1^G M` carries vanishing in
degree `n + 1` upward, one degree at a time. -/
theorem cohomologicalDimensionLE_iff_forall_subsingleton_succ (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  refine ⟨fun h M _ _ _ _ _ hM ↦ cohomologicalDimensionLE_iff.mp h M hM (n + 1) n.lt_succ_self,
    fun h ↦ ?_⟩
  -- vanishing in degree `i` for every module of the class, by induction on `i ≥ n + 1`
  suffices H : ∀ i, n + 1 ≤ i →
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) from
    cohomologicalDimensionLE_iff.mpr fun M _ _ _ _ _ hM i hi ↦ H i hi M hM
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact h
  | succ i hi ih =>
    intro M _ _ _ _ _ hM
    have := ih (DimensionShiftQuotient G M) (isPPrimaryTorsion_dimensionShiftQuotient G M hM)
    exact (dimensionShiftIso G M i (by omega)).toContinuousLinearEquiv.toEquiv.subsingleton

/-- **The finite single-degree test.** For a compact group `G` and `p ≠ 0`, the predicate
`CohomologicalDimensionLE p G n` holds exactly when `Hⁿ⁺¹(G, M)` vanishes for every **finite**
discrete `p`-primary `G`-module `M`. -/
theorem cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ (hp : p ≠ 0) (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionLE_iff_forall_subsingleton_succ]
  exact ⟨fun h M _ _ _ _ _ _ hM ↦ h M hM, fun h M _ _ _ _ _ hM ↦
    ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite hp hM (n + 1) h⟩

variable (p G)

/-- **`cd_p G ≤ n` is detected in degree `n + 1`**: for a compact group `G`, `cd_p G ≤ n` exactly
when `Hⁿ⁺¹(G, M)` vanishes for every discrete `p`-primary torsion `G`-module `M`. -/
theorem cohomologicalDimensionAt_le_iff_forall_subsingleton_succ (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_forall_subsingleton_succ]

/-- **`cd_p G ≤ n` is detected in degree `n + 1` on finite coefficients**: for a compact group `G`
and `p ≠ 0`, `cd_p G ≤ n` exactly when `Hⁿ⁺¹(G, M)` vanishes for every finite discrete `p`-primary
`G`-module `M`. -/
theorem cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ (hp : p ≠ 0) (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff,
    cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ hp]

/-- **`cd_p G = 0` is detected in degree one.** For a compact group `G`, the vanishing of
`H¹(G, M)` for every discrete `p`-primary torsion `G`-module `M` is equivalent to the vanishing
of all positive-degree cohomology, and hence to `cd_p G = 0`. -/
theorem cohomologicalDimensionAt_eq_zero_iff_forall_subsingleton_one :
    cohomologicalDimensionAt.{u} p G = 0 ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G M)) := by
  simpa only [Nat.cast_zero, nonpos_iff_eq_zero, zero_add] using
    (cohomologicalDimensionAt_le_iff_forall_subsingleton_succ p G 0)

/-- **The finite degree-one test for `cd_p G = 0`.** For a compact group `G` and `p ≠ 0`, it is
enough to test the vanishing of `H¹(G, M)` on finite discrete `p`-primary torsion `G`-modules. -/
theorem cohomologicalDimensionAt_eq_zero_iff_forall_finite_subsingleton_one (hp : p ≠ 0) :
    cohomologicalDimensionAt.{u} p G = 0 ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
        Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G M)) := by
  simpa only [Nat.cast_zero, nonpos_iff_eq_zero, zero_add] using
    (cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ p G hp 0)

end TauCeti
