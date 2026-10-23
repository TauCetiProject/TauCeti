/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Additive submonoids of semirings

The binomial theorem gives a criterion for a power of a sum to lie in an additive submonoid:
it suffices that every product of powers in the expansion belongs to the submonoid.
This applies to additive subgroups as well, without requiring multiplicative closure.
-/

public section

/-- If every product `a ^ k * b ^ (n - k)` lies in an additive submonoid and `a` commutes with
`b`, then `(a + b) ^ n` lies in the submonoid. -/
theorem Commute.add_pow_mem_of_mul_pow_mem {R S : Type*} [Semiring R] [SetLike S R]
    [AddSubmonoidClass S R] {G : S} {a b : R} (hab : Commute a b) {n : ℕ}
    (h : ∀ k ≤ n, a ^ k * b ^ (n - k) ∈ G) : (a + b) ^ n ∈ G := by
  rw [hab.add_pow]
  refine sum_mem fun k hk ↦ ?_
  simpa only [nsmul_eq_mul, Nat.cast_comm] using
    nsmul_mem (h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) (n.choose k)
