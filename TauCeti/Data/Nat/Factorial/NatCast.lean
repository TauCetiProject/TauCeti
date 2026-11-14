/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Nat.Factorial.NatCast

import Mathlib.Data.ZMod.Basic

/-!
# Factorials cast into a semiring of given characteristic

In a semiring `R`, if a positive natural number `m` vanishes in `R` then so does `k !` for every
`k ≥ m`. Conversely, in exponential characteristic `p`, `n !` is a unit of `R` for every `n < p`.

## Main results

* `Nat.cast_factorial_eq_zero_of_le`: `(m : R) = 0` with `0 < m ≤ k` gives `(k ! : R) = 0`.
* `IsUnit.natCast_factorial_of_expChar`: in exponential characteristic `p`, `(n ! : A)` is a unit
  of any semiring `A` whenever `n < p`.
-/

public section

namespace Nat

variable {R : Type*} [Semiring R]

/-- If `m` is positive and vanishes in `R`, so does the factorial of every `k ≥ m`. -/
theorem cast_factorial_eq_zero_of_le {m k : ℕ} (hm : 0 < m) (hmR : (m : R) = 0) (hk : m ≤ k) :
    (k.factorial : R) = 0 := by
  simpa only [hmR, zero_dvd_iff] using
    (Nat.cast_dvd_cast (Nat.dvd_factorial hm hk) : (m : R) ∣ (k.factorial : R))

end Nat

open scoped Nat in
/-- In exponential characteristic `p`, every factorial `n !` with `n < p` is a unit in any
semiring `A`. At `p = 1` (characteristic zero) this covers `0 ! = 1`; for prime `p` it holds
without assuming additive inverses. -/
theorem IsUnit.natCast_factorial_of_expChar {A : Type*} [Semiring A] (p : ℕ) [ExpChar A p]
    {n : ℕ} (h : n < p) : IsUnit (n ! : A) := by
  rcases ‹ExpChar A p› with _ | hp
  · obtain rfl : n = 0 := Nat.lt_one_iff.1 h
    simp
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := (IsUnit.natCast_factorial_iff_of_charP (A := ZMod p) p).2 h
    set k : ℕ := (↑u⁻¹ : ZMod p).val
    have hk : ((n ! * k : ℕ) : ZMod p) = 1 := by
      rw [Nat.cast_mul, ← hu, ZMod.natCast_zmod_val, Units.mul_inv]
    have hmod : n ! * k % p = 1 := by
      rw [← ZMod.val_natCast, hk, ZMod.val_one p]
    have hdiv : p * (n ! * k / p) + 1 = n ! * k := by
      rw [← hmod, Nat.div_add_mod]
    have hA : (n ! : A) * (k : A) = 1 := by
      have := congrArg (Nat.cast (R := A)) hdiv
      simpa [CharP.cast_eq_zero A p] using this.symm
    exact ⟨⟨n !, k, hA, (Nat.cast_commute _ _).eq.symm.trans hA⟩, rfl⟩

/-- `2 !` is a unit in `ZMod 3`, whereas `3 ! = 0` is not. -/
example : IsUnit ((Nat.factorial 2 : ℕ) : ZMod 3) ∧ ¬ IsUnit ((Nat.factorial 3 : ℕ) : ZMod 3) :=
  ⟨IsUnit.natCast_factorial_of_expChar 3 (by decide), by decide⟩

