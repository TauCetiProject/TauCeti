/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.CompletelyContinuous

/-!
# Checks for the lattice criterion of complete continuity

The criterion `ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo` characterizes complete
continuity by finite-rank approximation on a bounded neighbourhood `M₀` of zero, up to an
arbitrary neighbourhood of zero in the target. We test it on the zero map, on the identity of the
scalar line with its closed unit ball, and after replacing `M₀` by a nonzero multiple `c • M₀`.
As a negative control, the identity of a complete normed space that is not finite-dimensional
fails the criterion on its closed unit ball.
-/

public section

open Filter Topology Pointwise

variable {K M N : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup M] [NormedSpace K M] [SeminormedAddCommGroup N] [NormedSpace K N]

/-- The zero map satisfies the lattice criterion on every bounded neighbourhood of zero. -/
example {M₀ : Set M} (hM₀ : M₀ ∈ 𝓝 0) (hbdd : Bornology.IsBounded M₀) :
    ∀ V ∈ 𝓝 (0 : N), ∃ g : M →L[K] N, (g : M →ₗ[K] N).IsFiniteRank ∧
      Set.MapsTo ((0 : M →L[K] N) - g) M₀ V :=
  (ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo hM₀ hbdd).mp
    ContinuousLinearMap.isCompletelyContinuous_zero

/-- On the scalar line, the identity satisfies the lattice criterion on the closed unit ball. -/
example : ∀ V ∈ 𝓝 (0 : K), ∃ g : K →L[K] K, (g : K →ₗ[K] K).IsFiniteRank ∧
    Set.MapsTo (ContinuousLinearMap.id K K - g) (Metric.closedBall 0 1) V :=
  (ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo
    (Metric.closedBall_mem_nhds 0 one_pos) Metric.isBounded_closedBall).mp
    (ContinuousLinearMap.isCompletelyContinuous_of_finite _)

/-- Replacing the bounded neighbourhood `M₀` by `c • M₀` for a nonzero scalar `c` does not change
the lattice criterion. -/
example {u : M →L[K] N} {M₀ : Set M} (hM₀ : M₀ ∈ 𝓝 0) (hbdd : Bornology.IsBounded M₀) {c : K}
    (hc : c ≠ 0) :
    (∀ V ∈ 𝓝 (0 : N), ∃ g : M →L[K] N, (g : M →ₗ[K] N).IsFiniteRank ∧
      Set.MapsTo (u - g) M₀ V) ↔
    (∀ V ∈ 𝓝 (0 : N), ∃ g : M →L[K] N, (g : M →ₗ[K] N).IsFiniteRank ∧
      Set.MapsTo (u - g) (c • M₀) V) := by
  rw [← ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo hM₀ hbdd,
    ← ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo
      ((set_smul_mem_nhds_zero_iff hc).mpr hM₀) (hbdd.smul₀ c)]

/-- The identity of a complete normed space which is not finite-dimensional fails the lattice
criterion: some neighbourhood of zero contains `(1 - g)(B)` for no continuous `g` of finite rank,
where `B` is the closed unit ball. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
    (hE : ¬Module.Finite K E) :
    ∃ V ∈ 𝓝 (0 : E), ∀ g : E →L[K] E, (g : E →ₗ[K] E).IsFiniteRank →
      ¬Set.MapsTo (ContinuousLinearMap.id K E - g) (Metric.closedBall 0 1) V := by
  rw [← ContinuousLinearMap.isCompletelyContinuous_id_iff,
    ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo
      (Metric.closedBall_mem_nhds 0 one_pos) Metric.isBounded_closedBall] at hE
  push Not at hE
  exact hE
