/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# Iterated powers in a monoid

## Main results

* `TauCeti.pow_eq_pow_of_pow_succ_eq_pow`: if `a ^ (n + 1) = a ^ n` then `a ^ k = a ^ n` for all
  `k ≥ n`.
* `TauCeti.pow_pow_eq_self_of_pow_sq_eq_self`: if `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`.
* `TauCeti.mul_zpow_mul_mul_zpow`: in a commutative group, integer powers of monomials
  `a ^ i * b ^ j` multiply by adding their exponent vectors.
* `TauCeti.eq_mul_zpow_sub_of_mul_zpow_eq`: an equation `a * h ^ D = b * h ^ e` can be solved for
  `a`, as `a = b * h ^ (e - D)`.
* `TauCeti.add_eq_mod_add_carry`: for `n = m d`, the carry of `m p + m q` modulo `n` is the carry of
  `p + q` modulo `d`.
* `TauCeti.pow_mul_mul_pow_mul_eq`: the same carry read in the powers of an `n`-th root of `a`.
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

/-- Moving a power of `h` across an equation: if `a * h ^ D = b * h ^ e` then
`a = b * h ^ (e - D)`. -/
theorem eq_mul_zpow_sub_of_mul_zpow_eq {G : Type*} [Group G] {a b h : G} {D e : ℤ}
    (H : a * h ^ D = b * h ^ e) : a = b * h ^ (e - D) := by
  rw [zpow_sub, ← mul_assoc, ← H, mul_inv_cancel_right]

/-- **Carries under scaling.** For `n = m d` with `m > 0` and `p, q < d`, the carry of
`m p + m q` modulo `n` is the carry of `p + q` modulo `d`. -/
theorem add_eq_mod_add_carry {m d n p q : ℕ} (hmd : m * d = n) (hm : 0 < m)
    (hp : p < d) (hq : q < d) :
    m * p + m * q = (m * p + m * q) % n + n * if d ≤ p + q then 1 else 0 := by
  have hlt : m * p + m * q < 2 * n := calc
    m * p + m * q = m * (p + q) := (mul_add _ _ _).symm
    _ < m * (2 * d) := Nat.mul_lt_mul_of_pos_left (by omega) hm
    _ = 2 * n := by rw [← hmd]; ring
  have hle (h : d ≤ p + q) : n ≤ m * p + m * q := calc
    n = m * d := hmd.symm
    _ ≤ m * (p + q) := Nat.mul_le_mul_left m h
    _ = m * p + m * q := mul_add _ _ _
  have hlt' (h : p + q < d) : m * p + m * q < n := calc
    m * p + m * q = m * (p + q) := (mul_add _ _ _).symm
    _ < m * d := Nat.mul_lt_mul_of_pos_left h hm
    _ = n := hmd
  generalize m * p + m * q = X at *
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod (hle h), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (hlt' (not_le.1 h))]
    omega

/-- **Carries under scaling, in a monoid.** If `α ^ n = a` and `n = m d`, then for `p, q < d` the
product `α ^ (m p) * α ^ (m q)` is `α ^ ((m p + m q) % n)` times `a` when `p + q` carries
modulo `d`. -/
theorem pow_mul_mul_pow_mul_eq {α a : M} {n : ℕ} (hα : α ^ n = a) {m d p q : ℕ}
    (hmd : m * d = n) (hm0 : 0 < m) (hp : p < d) (hq : q < d) :
    α ^ (m * p) * α ^ (m * q) = α ^ ((m * p + m * q) % n) * if d ≤ p + q then a else 1 := by
  rw [← pow_add, add_eq_mod_add_carry hmd hm0 hp hq, pow_add, pow_mul, hα]
  split_ifs <;> simp

end TauCeti
