/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.LimitCriterion

import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Local separation from a closed subgroup

Let `K` be a closed subgroup of a finite-dimensional Lie group, and let `M` be a linear subspace
of its Lie algebra which is disjoint from `lieSubalgebraOfSubgroup K`. Then the only sufficiently
small `X ∈ M` whose exponential lies in `K` is `0`.

The proof is the compactness step in the closed-subgroup theorem. If there were arbitrarily small
nonzero counterexamples, normalize them to the unit sphere and take a convergent subsequence. The
closed-subgroup limit criterion puts its limit in `lieSubalgebraOfSubgroup K`, while closedness of
`M` puts the same unit vector in `M`, contradicting disjointness.

This is the local-separation input for the subgroup chart: when `M` is a complement of
`lieSubalgebraOfSubgroup K`, it forces the transverse coordinate of nearby points of `K` to vanish.

## Main result

* `TauCeti.Lie.exists_norm_lt_lieExp_mem_iff_eq_zero_of_disjoint`: exponential membership near
  zero characterizes the zero vector on any subspace disjoint from the subgroup Lie algebra.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

local instance finiteDimensionalLeftInvariantDerivationLocalSeparation :
    FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- Let `K` be a closed subgroup and `M` a linear subspace disjoint from its Lie algebra. In some
positive-radius ball about zero, an element of `M` has exponential in `K` exactly when it is zero.

This needs only disjointness; in the closed-subgroup chart construction it applies in particular
when `M` is chosen as a linear complement of `lieSubalgebraOfSubgroup K`. -/
theorem exists_norm_lt_lieExp_mem_iff_eq_zero_of_disjoint {K : Subgroup G}
    (hK : IsClosed (K : Set G)) (M : Submodule ℝ (LeftInvariantDerivation I G))
    (hM : Disjoint M (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) :
    ∃ ε > 0, ∀ X ∈ M, ‖X‖ < ε → (lieExp (I := I) X ∈ K ↔ X = 0) := by
  suffices ∃ ε > 0, ∀ X ∈ M, ‖X‖ < ε → lieExp (I := I) X ∈ K → X = 0 by
    obtain ⟨ε, hε, h⟩ := this
    refine ⟨ε, hε, fun X hXM hXnorm ↦ ⟨h X hXM hXnorm, ?_⟩⟩
    rintro rfl
    simpa only [lieExp_zero] using K.one_mem
  by_contra! h
  choose X hXM hXnorm hXexp hXne using fun n : ℕ =>
    h (1 / (n + 1 : ℝ)) (by positivity)
  let Y : ℕ → LeftInvariantDerivation I G := fun n => NormedSpace.normalize (X n)
  have hYnorm (n : ℕ) : ‖Y n‖ = 1 := NormedSpace.norm_normalize (hXne n)
  obtain ⟨Z, hZsphere, φ, hφmono, hφ⟩ :=
    (isCompact_sphere (0 : LeftInvariantDerivation I G) 1).tendsto_subseq
      (fun n => by simpa [Metric.mem_sphere, dist_eq_norm] using hYnorm n)
  have hZM : Z ∈ M := by
    apply M.closed_of_finiteDimensional.mem_of_tendsto hφ
    filter_upwards with n
    exact M.smul_mem _ (hXM (φ n))
  have hZlie : Z ∈ lieSubalgebraOfSubgroup (I := I) K := by
    apply mem_lieSubalgebraOfSubgroup_of_seq hK
      (t := fun n => ‖X (φ n)‖) (Xn := Y ∘ φ)
    · filter_upwards with n
      exact norm_pos_iff.mpr (hXne (φ n))
    · refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop)
      filter_upwards with n
      simpa only [Function.comp_apply] using (hXnorm (φ n)).le
    · exact hφ
    · filter_upwards with n
      change lieExp (I := I) (‖X (φ n)‖ • NormedSpace.normalize (X (φ n))) ∈ K
      rw [NormedSpace.norm_smul_normalize]
      exact hXexp (φ n)
  have hZzero : Z = 0 := Submodule.disjoint_def.mp hM Z hZM hZlie
  have : ‖Z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hZsphere
  simp [hZzero] at this

end TauCeti.Lie
