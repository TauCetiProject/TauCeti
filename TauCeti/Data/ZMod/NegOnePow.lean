/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.ZMod.Basic

/-!
# The sign `(-1)^p` on `ZMod n` for even `n`

Mathlib's `Int.negOnePow k` is the sign `(-1)^k` of an integer `k`. It depends only on the class
of `k` modulo any even `n`, so for `2 ∣ n` it descends to `ZMod n`. This file defines that sign,
`ZMod.negOnePow`, and records how it computes. It also shows that the sign is forced: a function
`ZMod n → ℤˣ` which is `1` at `0` and changes sign at each step `p ↦ p + 1` takes the value
`Int.negOnePow k` at the class of every integer `k`.

The evenness hypothesis is a `Fact (2 ∣ n)` instance, supplied here for `n = 2 * m` and for the
moduli `2`, `4` and `8`.

## Main definitions and results

* `ZMod.negOnePow`: the sign `(-1)^p` of `p : ZMod n` for even `n`.
* `ZMod.negOnePow_add`, `ZMod.negOnePow_intCast`: it is multiplicative, and it is
  `Int.negOnePow k` at the class of `k : ℤ`.
* `ZMod.negOnePow_eq_one_iff`, `ZMod.negOnePow_eq_neg_one_iff`: it is `1` or `-1` according to
  the reduction of `p` modulo `2`.
* `ZMod.apply_intCast_eq_negOnePow`: a sign function which is `1` at `0` and alternates along
  `p ↦ p + 1` is `Int.negOnePow k` at the class of `k`, for every `n`.
-/

public section

/-- `2 * m` is even. -/
instance Nat.fact_two_dvd_two_mul (m : ℕ) : Fact (2 ∣ 2 * m) :=
  ⟨Nat.dvd_mul_right 2 m⟩

/-- `2` is even. -/
instance Nat.fact_two_dvd_two : Fact (2 ∣ 2) :=
  ⟨dvd_rfl⟩

/-- `4` is even. -/
instance Nat.fact_two_dvd_four : Fact (2 ∣ 4) :=
  ⟨by decide⟩

/-- `8` is even. -/
instance Nat.fact_two_dvd_eight : Fact (2 ∣ 8) :=
  ⟨by decide⟩

namespace ZMod

variable {n : ℕ}

/-- **Alternating signs on `ZMod n` are forced.** A sign function on `ZMod n` which is `1` at `0`
and changes sign at each step `p ↦ p + 1` is `Int.negOnePow k` at the class of `k`. -/
theorem apply_intCast_eq_negOnePow (e : ZMod n → ℤˣ) (h₀ : e 0 = 1)
    (h : ∀ p, e (p + 1) = -e p) (k : ℤ) : e k = k.negOnePow := by
  induction k using Int.induction_on with
  | zero => simpa using h₀
  | succ k ih => rw [Int.cast_add, Int.cast_one, h, ih, Int.negOnePow_succ]
  | pred k ih =>
    have hk := h ((-k - 1 : ℤ) : ZMod n)
    push_cast at hk ih ⊢
    rw [sub_add_cancel, ih] at hk
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, hk, neg_neg]

variable [Fact (2 ∣ n)]

/-- The sign `(-1)^p` of `p : ZMod n` for even `n`, read through the reduction
`ZMod n → ZMod 2`. It is `Int.negOnePow k` at the class of `k : ℤ`
(`ZMod.negOnePow_intCast`). -/
def negOnePow (p : ZMod n) : ℤˣ :=
  (-1 : ℤˣ) ^ castHom (Fact.out : 2 ∣ n) (ZMod 2) p

/-- The sign of a sum is the product of the signs. -/
theorem negOnePow_add (p q : ZMod n) : (p + q).negOnePow = p.negOnePow * q.negOnePow := by
  rw [negOnePow, map_add, uzpow_add, negOnePow, negOnePow]

/-- The sign of `0` is `1`. -/
@[simp]
theorem negOnePow_zero : (0 : ZMod n).negOnePow = 1 := by
  rw [negOnePow, map_zero, uzpow_zero]

/-- The sign of `1` is `-1`. -/
@[simp]
theorem negOnePow_one : (1 : ZMod n).negOnePow = -1 := by
  rw [negOnePow, map_one, uzpow_one]

/-- The sign changes at each step `p ↦ p + 1`. -/
theorem negOnePow_add_one (p : ZMod n) : (p + 1).negOnePow = -p.negOnePow := by
  rw [negOnePow_add, negOnePow_one, mul_neg_one]

/-- The sign of the class of an integer `k` is `(-1)^k`. -/
@[simp]
theorem negOnePow_intCast (k : ℤ) : (k : ZMod n).negOnePow = k.negOnePow := by
  rw [negOnePow, map_intCast, uzpow_intCast, Int.negOnePow_def]

/-- The sign of the class of a natural number `k` is `(-1)^k`. -/
@[simp]
theorem negOnePow_natCast (k : ℕ) : (k : ZMod n).negOnePow = (-1) ^ k := by
  rw [← Int.cast_natCast, negOnePow_intCast, Int.negOnePow_def, zpow_natCast]

/-- The sign of a numeral `k` is `(-1)^k`. -/
@[simp]
theorem negOnePow_ofNat (k : ℕ) [k.AtLeastTwo] :
    (no_index (OfNat.ofNat k) : ZMod n).negOnePow = (-1) ^ (OfNat.ofNat k : ℕ) := by
  have h := negOnePow_natCast (n := n) (OfNat.ofNat k)
  rwa [Nat.cast_ofNat] at h

/-- The sign of `-p` is the sign of `p`. -/
@[simp]
theorem negOnePow_neg (p : ZMod n) : (-p).negOnePow = p.negOnePow := by
  rw [negOnePow, map_neg, uzpow_neg, Int.units_inv_eq_self, negOnePow]

/-- The sign of a difference is the product of the signs. -/
theorem negOnePow_sub (p q : ZMod n) : (p - q).negOnePow = p.negOnePow * q.negOnePow := by
  rw [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

/-- The sign of `p` is `1` exactly when `p` is even, that is, when its reduction modulo `2`
vanishes. -/
theorem negOnePow_eq_one_iff (p : ZMod n) :
    p.negOnePow = 1 ↔ castHom (Fact.out : 2 ∣ n) (ZMod 2) p = 0 := by
  rw [negOnePow, ← natCast_zmod_val (castHom _ (ZMod 2) p), uzpow_natCast,
    natCast_eq_zero_iff_even, neg_one_pow_eq_one_iff_even (by decide)]

/-- The sign of `p` is `-1` exactly when `p` is odd, that is, when its reduction modulo `2`
is `1`. -/
theorem negOnePow_eq_neg_one_iff (p : ZMod n) :
    p.negOnePow = -1 ↔ castHom (Fact.out : 2 ∣ n) (ZMod 2) p = 1 := by
  rw [negOnePow, ← natCast_zmod_val (castHom _ (ZMod 2) p), uzpow_natCast,
    natCast_eq_one_iff_odd, neg_one_pow_eq_neg_one_iff_odd (by decide)]

/-- The sign of `p` is `(-1)^k` for the integer representative `k` of `p`. -/
theorem negOnePow_eq (p : ZMod n) : p.negOnePow = (p.cast : ℤ).negOnePow := by
  rw [← negOnePow_intCast (n := n), intCast_zmod_cast]

end ZMod
