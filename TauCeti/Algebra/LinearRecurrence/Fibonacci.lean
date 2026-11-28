/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Real.GoldenRatio
import TauCeti.Algebra.LinearRecurrence.Nondegenerate

/-!
# The Fibonacci recurrence is nondegenerate

A check of the nondegeneracy API of `TauCeti.Algebra.LinearRecurrence.Nondegenerate` on the
Fibonacci recurrence `Real.fibRec`, whose characteristic roots are the golden ratio and its
conjugate. It lives apart from the generic nondegeneracy module so that the latter does not
import the real golden-ratio theory.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 8,
  §8.4, pp. 172–175.
-/

open Polynomial

namespace LinearRecurrence

/-- The Fibonacci recurrence over `ℚ` has nonzero constant term, and the quotient of its two
distinct characteristic roots has infinite multiplicative order. -/
example : (Real.fibRec : LinearRecurrence ℚ).IsNondegenerate := by
  -- At a root `x`, the power `x ^ (k + 1)` equals `F (k + 1) * x + F k` for Fibonacci numbers `F`.
  have hpow {x : AlgebraicClosure ℚ}
      (hx : x ∈ (Real.fibRec : LinearRecurrence ℚ).charPoly.rootSet (AlgebraicClosure ℚ)) (k : ℕ) :
      x ^ (k + 1) = (Nat.fib (k + 1) : AlgebraicClosure ℚ) * x + Nat.fib k := by
    have hx2 : x ^ 2 - (x + 1) = 0 := by
      simpa [Real.fibRec_charPoly_eq] using aeval_eq_zero_of_mem_rootSet hx
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Nat.fib_add_two]
      push_cast
      linear_combination (Nat.fib (k + 1) : AlgebraicClosure ℚ) * hx2
  refine (isNondegenerate_iff_pow _).mpr
    ⟨by simp [Real.fibRec_charPoly_eq], fun {θ θ'} hθ hθ' hne n hn heq ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, hpow hθ, hpow hθ'] at heq
  have hfib : (Nat.fib (k + 1) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr k.succ_pos).ne'
  exact hne (mul_left_cancel₀ hfib (add_right_cancel heq))

end LinearRecurrence
