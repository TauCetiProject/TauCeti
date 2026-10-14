/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Dirac measures and the norm topology

Dirac measures vary continuously in the weak topology. For a compact totally separated domain
and ultrametric field coefficients, distinct Dirac measures are at operator-norm distance one.
Consequently, on an infinite such domain the closed unit ball of the continuous dual is not
norm compact. This distinguishes the strong topology on bounded measures from the weak topology
used for integral measures.

All norms below are taken on the continuous dual through `AbstractMeasure.toCLMEquiv`;
no norm or topology is installed on the abstract measure carrier.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Definitions 3.5 and 3.8, Example 3.10, and Remark 3.28(3).
The measure carrier, Dirac measures, and the two topologies are Mathlib's.
-/

public section

open ContinuousMap
open scoped AbstractMeasure

namespace AbstractMeasure

variable {X R K : Type*} [TopologicalSpace X]

/-- The Dirac map is continuous for the weak topology of test-function evaluations. -/
theorem continuous_dirac_weak [NormedCommRing R] :
    @Continuous X D(X, R) _ WeakTopology (dirac R) := by
  apply continuous_induced_rng.2
  exact continuous_pi fun f ↦ by simpa using f.continuous

variable [CompactSpace X] [NontriviallyNormedField K]

/-- A Dirac measure has operator norm one. -/
@[simp]
theorem norm_dirac (x : X) : ‖toCLMEquiv (dirac K x)‖ = 1 := by
  have : Nonempty X := ⟨x⟩
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ ?_
    simpa using f.norm_coe_le_norm x
  · simpa using (toCLMEquiv (dirac K x)).unit_le_opNorm
      (x := (1 : C(X, K))) (by simp)

variable [TotallySeparatedSpace X] [IsUltrametricDist K]

/-- On a totally separated compact space, distinct Dirac measures are at operator-norm
distance one over an ultrametric field. -/
theorem norm_dirac_sub {x y : X} (hxy : x ≠ y) :
    ‖toCLMEquiv (dirac K x - dirac K y)‖ = 1 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ ?_
    simpa [dist_eq_norm] using (IsUltrametricDist.dist_triangle_max (f x) 0 (f y)).trans
      (max_le (by simpa using f.norm_coe_le_norm x)
        (by simpa using f.norm_coe_le_norm y))
  · obtain ⟨s, hs, hx, hy⟩ := exists_isClopen_of_totally_separated hxy
    let f : C(X, K) := (LocallyConstant.charFn K hs).toContinuousMap
    have hf : ‖f‖ ≤ 1 := by
      apply (ContinuousMap.norm_le _ zero_le_one).2
      intro z
      by_cases hz : z ∈ s
      · simp [f, (LocallyConstant.charFn_eq_one K z hs).2 hz]
      · simp [f, (LocallyConstant.charFn_eq_zero K z hs).2 hz]
    have hfx : f x = 1 := (LocallyConstant.charFn_eq_one K x hs).2 hx
    have hfy : f y = 0 := (LocallyConstant.charFn_eq_zero K y hs).2 hy
    simpa [hfx, hfy] using
      (toCLMEquiv (dirac K x - dirac K y)).unit_le_opNorm f hf

/-- The unit ball of the continuous dual on an infinite compact totally separated space
is not compact for the operator norm. The coefficient field need not be complete or proper. -/
theorem not_isCompact_measure_unitBall [Infinite X] :
    ¬ IsCompact {L : C(X, K) →L[K] K | ‖L‖ ≤ 1} := by
  intro h
  let e : ℕ ↪ X := Infinite.natEmbedding X
  let d : ℕ → C(X, K) →L[K] K := fun n ↦ toCLMEquiv (dirac K (e n))
  have hd : Topology.IsClosedEmbedding d := by
    refine Metric.isClosedEmbedding_of_pairwise_le_dist (f := d) (ε := 1) zero_lt_one ?_
    intro m n hmn
    simpa only [d, dist_eq_norm, map_sub] using
      (norm_dirac_sub (K := K) (e.injective.ne hmn)).ge
  have hc := hd.isCompact_preimage h
  have he : d ⁻¹' {L : C(X, K) →L[K] K | ‖L‖ ≤ 1} = Set.univ := by
    ext n
    simp [d]
  rw [he] at hc
  exact Set.infinite_univ hc.finite_of_discrete

end AbstractMeasure
