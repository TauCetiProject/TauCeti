/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient

/-!
# Totients under multiplication without new prime factors

Enlarging a modulus without adding prime factors scales its totient by the same factor.
-/

public section

namespace Nat

/-- If every prime factor of `n` divides `m`, multiplying `m` by `n` multiplies its totient
by `n`. -/
theorem totient_mul_of_primeFactors_subset {m n : ℕ} (h : n.primeFactors ⊆ m.primeFactors) :
    (m * n).totient = m.totient * n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hfac : (m * n).primeFactors = m.primeFactors := by
    rw [primeFactors_mul hm hn, Finset.union_eq_left.mpr h]
  have hprod := totient_mul_prod_primeFactors (m * n)
  rw [hfac, mul_right_comm m n] at hprod
  have hcancel : (m * n).totient * ∏ p ∈ m.primeFactors, p =
      (m.totient * n) * ∏ p ∈ m.primeFactors, p := by
    rw [hprod, mul_right_comm m.totient n, totient_mul_prod_primeFactors]
  exact Nat.eq_of_mul_eq_mul_right (Finset.prod_pos fun p hp ↦ (prime_of_mem_primeFactors hp).pos)
    hcancel

end Nat
