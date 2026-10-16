/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Algebra.Module.Pointwise

/-!
# Interpolation of parallel convex sets

For convex sets `A` and `B`, Minkowski addition and nonnegative scalar multiplication commute
with weighted interpolation:

`p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B`

when `p + q = 1`. Thus the family of outer parallel sets `A + t • B` is affine under
Minkowski interpolation. The specialization where `B` is the closed unit ball is the set identity
used to transfer Brunn--Minkowski concavity to the volumes of outer parallel bodies.

No nonemptiness or topological assumptions are needed: the result is an algebraic consequence of
convexity. We first record the underlying distributivity of scalar multiplication over pointwise
set addition, which also holds without convexity.

## Main results

* `Set.smul_set_add`: a scalar distributes over the Minkowski sum of two sets.
* `Convex.add_smul_interpolation`: interpolation of two parallel convex sets with
  arbitrary nonnegative weights summing to one.
* `Convex.add_smul_interpolation_sub`: the same identity with weights `1 - u` and `u`.
* `Convex.add_smul_closedBall_interpolation`: the outer-parallel-body specialization.
-/

public section

open Set
open scoped Pointwise

namespace Convex

section Convex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Weighted interpolation between the parallel convex sets `A + s • B` and `A + t • B`
is the parallel set at the correspondingly weighted parameter. -/
theorem add_smul_interpolation {A B : Set E} (hA : Convex 𝕜 A) (hB : Convex 𝕜 B)
    {p q s t : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B := by
  rw [Set.smul_set_add, Set.smul_set_add, smul_smul, smul_smul, add_add_add_comm,
    ← hA.add_smul hp hq, hpq, one_smul, ← hB.add_smul (mul_nonneg hp hs) (mul_nonneg hq ht)]

/-- Convex-combination form of `Convex.add_smul_interpolation`, parametrized by
`u ∈ [0, 1]`. -/
theorem add_smul_interpolation_sub {A B : Set E} (hA : Convex 𝕜 A)
    (hB : Convex 𝕜 B) {u s t : 𝕜} (hu : u ∈ Icc 0 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - u) • (A + s • B) + u • (A + t • B) =
      A + ((1 - u) * s + u * t) • B := by
  exact add_smul_interpolation hA hB (sub_nonneg.mpr hu.2) hu.1
    (sub_add_cancel 1 u) hs ht

end Convex

section ClosedBall

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Minkowski interpolation of the outer parallel sets of a convex set by the closed unit ball. -/
theorem add_smul_closedBall_interpolation {K : Set V} (hK : Convex ℝ K)
    {u s t : ℝ} (hu : u ∈ Icc 0 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - u) • (K + s • Metric.closedBall 0 1) +
        u • (K + t • Metric.closedBall 0 1) =
      K + ((1 - u) * s + u * t) • Metric.closedBall 0 1 :=
  add_smul_interpolation_sub hK (convex_closedBall 0 1) hu hs ht

end ClosedBall

end Convex
