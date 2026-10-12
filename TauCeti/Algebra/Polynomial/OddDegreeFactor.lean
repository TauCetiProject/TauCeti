/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Odd-degree irreducible factors

An odd-degree polynomial has an irreducible factor of odd degree over any
commutative semiring without zero divisors in which strict divisibility is well-founded.
-/

public section

namespace Polynomial

variable {K : Type*} [CommSemiring K] [NoZeroDivisors K] [WfDvdMonoid K]

/-- An odd-degree polynomial has an odd-degree irreducible factor. -/
theorem exists_irreducible_factor_of_odd_natDegree (p : K[X]) (hp : Odd p.natDegree) :
    ∃ q : K[X], Irreducible q ∧ Odd q.natDegree ∧ q ∣ p := by
  revert hp
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit p hp => simp [natDegree_eq_zero_of_isUnit hp]
  | mul p q hp hq ih =>
    intro hodd
    by_cases hoddq : Odd q.natDegree
    · exact ⟨q, hq, hoddq, dvd_mul_right q p⟩
    have hoddp : Odd p.natDegree := by
      rw [natDegree_mul hq.ne_zero hp, Nat.odd_iff] at hodd
      rw [Nat.odd_iff] at hoddq ⊢
      omega
    obtain ⟨r, hr, hrodd, hrp⟩ := ih hoddp
    exact ⟨r, hr, hrodd, hrp.trans (dvd_mul_left p q)⟩

end Polynomial
