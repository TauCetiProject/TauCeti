/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence of roots under Frobenius

In a commutative ring `L` of exponential characteristic `p`, the iterated Frobenius `x ↦ x ^ p ^ n`
is additive and sends a scalar multiple `c • x` to `c ^ p ^ n • x ^ p ^ n`. So a linear relation
among a family `v` over a reduced ring `K` gives one among the `v i ^ p ^ n`, and the `v i` are
linearly independent over `K` as soon as their `p ^ n`-th powers are. Mathlib's
`LinearIndependent.map_pow_expChar_pow_of_isSeparable` is the converse for separable extensions.
-/

public section

/-- **Roots of an independent family are independent.** In a ring `L` of exponential
characteristic `p`, a family `v` is linearly independent over a reduced ring `K` whenever the
family of its `p ^ n`-th powers is. No separability hypothesis is needed. -/
theorem LinearIndependent.of_pow_expChar_pow {K L ι : Type*} [CommRing K] [IsReduced K]
    [CommRing L] [Algebra K L] (p n : ℕ) [ExpChar L p] {v : ι → L}
    (h : LinearIndependent K fun i ↦ v i ^ p ^ n) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  -- The `p ^ n`-th power of a relation among the `v i` is a relation among their powers.
  have h' := congrArg (iterateFrobenius L p n) hg
  rw [map_sum, map_zero] at h'
  refine IsNilpotent.eq_zero ⟨p ^ n, h s (fun j ↦ g j ^ p ^ n) ?_ i hi⟩
  simpa only [Algebra.smul_def, map_mul, iterateFrobenius_def, map_pow, mul_pow] using h'
