/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic

/-!
# Interpolation of parallel convex sets

For convex sets `A` and `B`, Minkowski addition and nonnegative scalar multiplication commute
with weighted interpolation:

`p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B`

when `p + q = 1`. Thus the family of outer parallel sets `A + t • B` is affine under
Minkowski interpolation. The specialization where `B` is the closed unit ball is the set identity
used to transfer Brunn--Minkowski concavity to the volumes of outer parallel bodies.

No nonemptiness or topological assumptions are needed: the result is an algebraic consequence of
convexity, combined with Mathlib's distributivity `smul_add` of scalar multiplication over
pointwise set addition.

## Main results

* `Convex.add_smul_interpolation`: interpolation of two parallel convex sets with
  arbitrary nonnegative weights summing to one.
* `Convex.add_smul_interpolation_sub`: the same identity with weights `1 - u` and `u`.
-/

public section

open Set
open scoped Pointwise

namespace Convex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Weighted interpolation between the parallel convex sets `A + s • B` and `A + t • B`
is the parallel set at the correspondingly weighted parameter. -/
theorem add_smul_interpolation {A B : Set E} (hA : Convex 𝕜 A) (hB : Convex 𝕜 B)
    {p q s t : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B := by
  have hA' : p • A + q • A = A := by rw [← hA.add_smul hp hq, hpq, one_smul]
  have hB' : (p * s) • B + (q * t) • B = (p * s + q * t) • B :=
    (hB.add_smul (mul_nonneg hp hs) (mul_nonneg hq ht)).symm
  calc p • (A + s • B) + q • (A + t • B)
      = (p • A + q • A) + ((p * s) • B + (q * t) • B) := by
        simp only [smul_add, smul_smul]
        exact add_add_add_comm _ _ _ _
    _ = A + (p * s + q * t) • B := by rw [hA', hB']

/-- Convex-combination form of `Convex.add_smul_interpolation`, parametrized by
`u ∈ [0, 1]`. -/
theorem add_smul_interpolation_sub {A B : Set E} (hA : Convex 𝕜 A)
    (hB : Convex 𝕜 B) {u s t : 𝕜} (hu : u ∈ Icc 0 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - u) • (A + s • B) + u • (A + t • B) =
      A + ((1 - u) * s + u * t) • B := by
  exact add_smul_interpolation hA hB (sub_nonneg.mpr hu.2) hu.1
    (sub_add_cancel 1 u) hs ht

end Convex
