/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCoefficients

/-!
# Testing cohomological dimension on modules of bounded exponent

For a compact group, the ordinary `p`-cohomological dimension can be tested on discrete modules
killed by a single power of `p`. Every such module is `p`-primary torsion. Conversely, the
finite-coefficient test of `TauCeti.cohomologicalDimensionLE_iff_forall_finite` applies: a finite
`p`-primary torsion group has one power of `p` that kills all its elements. Thus testing bounded
exponent coefficients suffices even for `p`-primary modules of unbounded exponent.

This is the bounded-exponent reduction in the dévissage of Neukirch--Schmidt--Wingberg,
*Cohomology of Number Fields*, 2nd ed., (3.3.2).
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- For `p ≠ 0`, vanishing above degree `n` on all discrete `p`-primary torsion modules is
equivalent to vanishing on discrete modules annihilated by one power of `p`. The exponent may
depend on the module. -/
theorem cohomologicalDimensionLE_iff_boundedExponent (hp : p ≠ 0) {n : ℕ} :
    CohomologicalDimensionLE.{v} p G n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M],
        (∃ k : ℕ, ∀ m : M, p ^ k • m = 0) →
        ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) := by
  constructor
  · intro h M _ _ _ _ _ ⟨k, hk⟩ i hi
    exact (cohomologicalDimensionLE_iff.1 h) M
      (isPPrimaryTorsion_iff.2 fun m ↦ ⟨k, hk m⟩) i hi
  · intro h
    apply (cohomologicalDimensionLE_iff_forall_finite hp).2
    intro M _ _ _ _ _ _ hM i hi
    classical
    have : Fintype M := Fintype.ofFinite M
    choose k hk using isPPrimaryTorsion_iff.1 hM
    have hbound : ∃ j : ℕ, ∀ m : M, p ^ j • m = 0 := by
      refine ⟨Finset.univ.sup k, fun m ↦ ?_⟩
      obtain ⟨c, hc⟩ := pow_dvd_pow p (Finset.le_sup (f := k) (Finset.mem_univ m))
      rw [hc, mul_comm (p ^ k m) c, mul_smul, hk, smul_zero]
    exact h M hbound i hi

/-- For `p ≠ 0`, `cd_p G ≤ n` can be checked using only discrete coefficient modules killed by
some fixed power of `p`. -/
theorem cohomologicalDimensionAt_le_iff_boundedExponent (hp : p ≠ 0) (n : ℕ) :
    cohomologicalDimensionAt.{v} p G ≤ n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M],
        (∃ k : ℕ, ∀ m : M, p ^ k • m = 0) →
        ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_boundedExponent hp]

end TauCeti
