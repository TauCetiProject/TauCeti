/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup
import TauCeti.LinearAlgebra.Exact

/-!
# Testing cohomological dimension on finite modules killed by p

For a compact group `G`, vanishing of continuous cohomology in a fixed degree on finite
discrete modules killed by `p` implies vanishing on all finite discrete `p`-primary modules.
A finite `p`-primary module `M` is killed by some `p ^ k`. The sequence
`0 → pM → M → M / pM → 0` reduces this exponent: `pM` is killed by `p ^ (k - 1)`, and
`M / pM` is killed by `p`. Exactness in the middle of the cohomology sequence gives the induction.
The action need not be trivial, and `G` need not be pro-`p`.

Combined with the finite single-degree criterion, this gives a test for `cd_p G ≤ n` using
only degree `n + 1` and finite coefficients killed by `p`. These are finite vector spaces over
`ZMod p` when `p` is prime, so the criterion is the reduction preceding the test on simple
representations of finite quotients.

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite_nsmul_eq_zero`:
  the fixed-degree reduction from finite `p`-primary modules to finite modules killed by `p`.
* `TauCeti.cohomologicalDimensionLE_iff_forall_finite_nsmul_eq_zero` and
  `TauCeti.cohomologicalDimensionAt_le_iff_forall_finite_nsmul_eq_zero`: the resulting
  single-degree tests for the vanishing predicate and the dimension invariant.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.3.2), the reduction to finite simple `p`-primary coefficients.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

namespace ContinuousCohomology

/-- For a compact group, vanishing in a fixed degree on finite discrete modules killed by `p`
implies vanishing in that degree on every finite discrete `p`-primary module. No primality or
pro-`p` hypothesis is needed. -/
theorem subsingleton_continuousCohomology_of_forall_finite_nsmul_eq_zero (n : ℕ)
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, p • a = 0) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  obtain ⟨k, hk⟩ := hM.exists_pow_smul_eq_zero
  -- Induct on a common exponent, with the coefficient module allowed to vary.
  suffices H : ∀ (k : ℕ) (A : Type u) [AddCommGroup A] [TopologicalSpace A]
      [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
      (∀ a : A, p ^ k • a = 0) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)) from H k M hk
  intro k
  induction k with
  | zero =>
    intro A _ _ _ _ _ _ hA
    have : Subsingleton A := subsingleton_of_forall_eq 0 fun a ↦ by
      simpa using hA a
    exact subsingleton_continuousCohomology_ofDiscreteModule_of_subsingleton A n
  | succ k ih =>
    intro A _ _ _ _ _ _ hA
    let P : AddSubgroup A := (nsmulAddMonoidHom p : A →+ A).range
    have hP : ∀ g : G, ∀ a ∈ P, g • a ∈ P := by
      rintro g _ ⟨a, rfl⟩
      exact ⟨g • a, (smul_comm g p a).symm⟩
    let := P.restrictDistribMulAction hP
    let := P.quotientDistribMulAction hP
    have : ContinuousSMul G P := P.restrictDistribMulAction_continuousSMul hP
    have : ContinuousSMul G (A ⧸ P) := P.quotientDistribMulAction_continuousSMul hP
    have hPk : ∀ a : P, p ^ k • a = 0 := by
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmulAddMonoidHom_apply,
        smul_smul, ← pow_succ]
        using hA a
    have hQp : ∀ a : A ⧸ P, p • a = 0 := by
      intro a
      induction a using QuotientAddGroup.induction_on with
      | H a =>
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        exact ⟨a, rfl⟩
    have := ih P hPk
    have := h (A ⧸ P) hQp
    exact subsingleton_of_exact ((DiscreteShortExact.ofAddSubgroup P hP).longExact_exact₂ n)

end ContinuousCohomology

/-- `CohomologicalDimensionLE p G n` can be tested in degree `n + 1` on the finite discrete
`G`-modules killed by `p`. This holds for any nonzero `p`, without a pro-`p` hypothesis on `G`. -/
theorem cohomologicalDimensionLE_iff_forall_finite_nsmul_eq_zero (hp : p ≠ 0) (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], (∀ m : M, p • m = 0) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ hp]
  constructor
  · intro h M _ _ _ _ _ _ hM
    exact h M (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by simpa using hM m⟩)
  · intro h M _ _ _ _ _ _ hM
    exact ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite_nsmul_eq_zero
      (n + 1) h M hM

/-- For a compact group `G` and `p ≠ 0`, the bound `cd_p G ≤ n` is equivalent to the vanishing
of `Hⁿ⁺¹(G, M)` for every finite discrete `G`-module killed by `p`. -/
theorem cohomologicalDimensionAt_le_iff_forall_finite_nsmul_eq_zero (p : ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hp : p ≠ 0) (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], (∀ m : M, p • m = 0) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_forall_finite_nsmul_eq_zero hp]

end TauCeti
