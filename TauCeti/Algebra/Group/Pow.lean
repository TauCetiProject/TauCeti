/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Iterated powers in a monoid

## Main results

* `TauCeti.pow_eq_pow_of_pow_succ_eq_pow`: if `a ^ (n + 1) = a ^ n` then `a ^ k = a ^ n` for all
  `k ≥ n`.
* `TauCeti.pow_pow_eq_self_of_pow_sq_eq_self`: if `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`.
* `TauCeti.mul_zpow_mul_mul_zpow`: in a commutative group, integer powers of monomials
  `a ^ i * b ^ j` multiply by adding their exponent vectors.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M] {a : M} {q : ℕ}

/-- Once the powers of `a` repeat once, they are constant from that point on. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {n : ℕ} (h : a ^ (n + 1) = a ^ n) {k : ℕ} (hk : n ≤ k) :
    a ^ k = a ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih => rw [← add_assoc, pow_succ, ih (n.le_add_right d), ← pow_succ, h]

/-- If `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`. For example, an element of a field with `q ^ 2`
elements is fixed by applying the `q`-power map twice. -/
theorem pow_pow_eq_self_of_pow_sq_eq_self (ha : a ^ q ^ 2 = a) : (a ^ q) ^ q = a := by
  rw [← pow_mul, ← sq q, ha]

/-- In a commutative group, `(a ^ i * b ^ j) ^ k * (a ^ i' * b ^ j') ^ k'` is the monomial with
exponents `(i * k + i' * k', j * k + j' * k')`: the integer matrix with columns `(i, j)` and
`(i', j')` acts on the exponent vector `(k, k')`. -/
theorem mul_zpow_mul_mul_zpow {G : Type*} [CommGroup G] (a b : G) (i j k i' j' k' : ℤ) :
    (a ^ i * b ^ j) ^ k * (a ^ i' * b ^ j') ^ k' =
      a ^ (i * k + i' * k') * b ^ (j * k + j' * k') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

end TauCeti
