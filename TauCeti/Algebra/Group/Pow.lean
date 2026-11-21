/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Nat
import TauCeti.Data.Nat.Carry
import TauCeti.Data.Nat.Periodic.Basic

/-!
# Powers in monoids and groups

## Main results

* `TauCeti.pow_eq_pow_of_modEq_of_pow_add_eq`: if `a ^ (i + q) = a ^ i`, then `a ^ m = a ^ n`
  whenever `m, n ≥ i` and `m ≡ n [MOD q]`.
* `TauCeti.pow_eq_pow_of_pow_succ_eq_pow`: if `a ^ (n + 1) = a ^ n` then `a ^ k = a ^ n` for all
  `k ≥ n`.
* `TauCeti.pow_pow_eq_self_of_pow_sq_eq_self`: if `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`.
* `TauCeti.mul_zpow_mul_mul_zpow`: in a commutative group, integer powers of monomials
  `a ^ i * b ^ j` multiply by adding their exponent vectors.
* `TauCeti.mul_pow_mul_eq_pow_succ_mul_pow`: in a commutative monoid, a natural power of a product
  times the first factor gives consecutive monomial exponents.
* `TauCeti.eq_mul_zpow_sub_iff_mul_zpow_eq`: in a group, `a = b * h ^ (n - m)` if and only if
  `a * h ^ m = b * h ^ n`.
* `TauCeti.pow_mul_mul_pow_mul_eq`: the carry of `Nat.add_eq_mod_add_carry`, read in the
  powers of an `n`-th root of `a`.
* `TauCeti.pow_two_pow_of_odd` and `TauCeti.nsmul_two_nsmul_of_odd`: for odd `n`, raising to the
  power `(n + 1) / 2` inverts squaring on elements killed by `n`.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M] {a : M} {q : ℕ}

/-- If `a ^ (i + q) = a ^ i`, then the powers of `a` with exponent at least `i` repeat with
period `q`: two of them with exponents congruent modulo `q` are equal. The case `i = 0` is
Mathlib's `pow_eq_pow_of_modEq`, the case `q = 1` is `pow_eq_pow_of_pow_succ_eq_pow`. -/
theorem pow_eq_pow_of_modEq_of_pow_add_eq {i m n : ℕ} (h : a ^ (i + q) = a ^ i) (hm : i ≤ m)
    (hn : i ≤ n) (hmn : m ≡ n [MOD q]) : a ^ m = a ^ n := by
  have hper (k : ℕ) (hk : i ≤ k) : a ^ (k + q) = a ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [add_assoc, pow_add, h, ← pow_add]
  have hmod : (m - i) % q = (n - i) % q :=
    Nat.ModEq.add_right_cancel' i (by rwa [Nat.sub_add_cancel hm, Nat.sub_add_cancel hn])
  calc a ^ m = a ^ (i + (m - i) % q) := Nat.apply_eq_apply_add_sub_mod (a := (a ^ ·)) hper hm
    _ = a ^ (i + (n - i) % q) := by rw [hmod]
    _ = a ^ n := (Nat.apply_eq_apply_add_sub_mod (a := (a ^ ·)) hper hn).symm

/-- Once the powers of `a` repeat once, they are constant from that point on. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {n : ℕ} (h : a ^ (n + 1) = a ^ n) {k : ℕ} (hk : n ≤ k) :
    a ^ k = a ^ n :=
  pow_eq_pow_of_modEq_of_pow_add_eq h hk le_rfl Nat.modEq_one

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

/-- A natural power of a product gives consecutive monomial exponents after multiplication by
the first factor. -/
theorem mul_pow_mul_eq_pow_succ_mul_pow {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n * a = a ^ (n + 1) * b ^ n := by
  simp only [mul_pow, pow_succ]
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
    (hmd : m * d = n) (hp : p < d) (hq : q < d) :
    α ^ (m * p) * α ^ (m * q) = α ^ ((m * p + m * q) % n) * if d ≤ p + q then a else 1 := by
  rw [← pow_add, Nat.add_eq_mod_add_carry hmd hp hq, pow_add, pow_mul, hα]
  split_ifs <;> simp

/-- Two involutions satisfying the length-three braid relation have product of cube one. -/
theorem mul_pow_three_eq_one_of_braid {G : Type*} [Monoid G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * a = b * a * b) :
    (a * b) ^ 3 = 1 := by
  calc
    _ = (a * b * a) * (b * a * b) := by simp [pow_succ, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hab]
    _ = 1 := by simp only [mul_assoc, ← mul_assoc b b, hb, one_mul,
      ← mul_assoc a a, ha]

/-- Two involutions satisfying the length-four braid relation have product of fourth power one. -/
theorem mul_pow_four_eq_one_of_sq_eq_sq {G : Type*} [Monoid G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 2 = (b * a) ^ 2) :
    (a * b) ^ 4 = 1 := by
  calc
    _ = (a * b) ^ 2 * (a * b) ^ 2 := by rw [← pow_add]
    _ = (b * a) ^ 2 * (a * b) ^ 2 := by rw [hab]
    _ = 1 := pow_mul_pow_eq_one 2 (by
      simp only [mul_assoc, ← mul_assoc a a, ha, one_mul, hb])

/-- For odd `n`, raising to the power `(n + 1) / 2` inverts squaring on elements `a` with
`a ^ n = 1`. -/
@[to_additive /-- For odd `n`, multiplying by `(n + 1) / 2` inverts doubling on elements `a` with
`n • a = 0`. -/]
theorem pow_two_pow_of_odd {n : ℕ} (hn : Odd n) {a : M} (ha : a ^ n = 1) :
    (a ^ 2) ^ ((n + 1) / 2) = a := by
  obtain ⟨t, rfl⟩ := hn
  rw [← pow_mul, show 2 * ((2 * t + 1 + 1) / 2) = 2 * t + 1 + 1 by omega, pow_succ, ha, one_mul]

end TauCeti
