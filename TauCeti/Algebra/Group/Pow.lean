/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Nat
import TauCeti.Data.Nat.Carry

/-!
# Powers in monoids and groups

## Main results

* `TauCeti.pow_eq_pow_of_pow_succ_eq_pow`: if `a ^ (n + 1) = a ^ n` then `a ^ k = a ^ n` for all
  `k ≥ n`.
* `TauCeti.pow_pow_eq_self_of_pow_sq_eq_self`: if `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`.
* `TauCeti.mul_zpow_mul_mul_zpow`: in a commutative group, integer powers of monomials
  `a ^ i * b ^ j` multiply by adding their exponent vectors.
* `TauCeti.eq_mul_zpow_sub_iff_mul_zpow_eq`: in a group, `a = b * h ^ (n - m)` if and only if
  `a * h ^ m = b * h ^ n`.
* `TauCeti.pow_mul_mul_pow_mul_eq`: the carry of `Nat.add_eq_mod_add_carry`, read in the powers of
  an `n`-th root of `a`.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M] {a : M} {q : ℕ}

/-- Once the powers of `a` repeat once, they are constant from that point on. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {n : ℕ} (h : a ^ (n + 1) = a ^ n) {k : ℕ} (hk : n ≤ k) :
    a ^ k = a ^ n := by
  induction hk with
  | refl => rfl
  | step _ ih => rw [pow_succ, ih, ← pow_succ, h]

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

/-- Moving a power of `h` across an equation: `a = b * h ^ (n - m)` if and only if
`a * h ^ m = b * h ^ n`. -/
theorem eq_mul_zpow_sub_iff_mul_zpow_eq {G : Type*} [Group G] {a b h : G} {m n : ℤ} :
    a = b * h ^ (n - m) ↔ a * h ^ m = b * h ^ n := by
  rw [zpow_sub, ← mul_assoc, eq_mul_inv_iff_mul_eq]

/-- **Carries under scaling, in a monoid.** If `α ^ n = a` and `n = m d`, then for `p, q < d` the
product `α ^ (m p) * α ^ (m q)` is `α ^ ((m p + m q) % n)` times `a` when `p + q` carries
modulo `d`. -/
theorem pow_mul_mul_pow_mul_eq {α a : M} {n : ℕ} (hα : α ^ n = a) {m d p q : ℕ}
    (hmd : m * d = n) (hm0 : 0 < m) (hp : p < d) (hq : q < d) :
    α ^ (m * p) * α ^ (m * q) = α ^ ((m * p + m * q) % n) * if d ≤ p + q then a else 1 := by
  rw [← pow_add, Nat.add_eq_mod_add_carry hmd hm0 hp hq, pow_add, pow_mul, hα]
  split_ifs <;> simp

end TauCeti
