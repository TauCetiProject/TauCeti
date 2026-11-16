/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import TauCeti.Data.ZMod.Nilpotent

/-!
# Residues modulo two and modulo powers of two

A residue modulo two is `0` or `1`, so its canonical representative `ZMod.val` is the indicator
of being nonzero. This is the identity behind the counting arguments that read a `ℕ`-valued
weight off a `ZMod 2`-valued vector: summing the representatives of the coordinates counts the
nonzero ones.

Since `2` is nilpotent in `ℤ/2^n` (`ZMod.isNilpotent_natCast_self_pow`), the units of
`ℤ/2^{k+1}` are exactly the odd elements: an even element plus a unit is a unit, and an even
element is never a unit. These are the cases `p = 2` of `ZMod.isUnit_natCast_mul_add` and
`ZMod.not_isUnit_natCast_mul`, stated with the numeral `2`.

The cyclic group of order two, written multiplicatively as `C₂ = Multiplicative (ZMod 2)`, has
exactly the two elements `1` and `σ = Multiplicative.ofAdd 1`, so a sum over `C₂` has two terms.

## Main results

* `ZMod.natCast_gcd_two`: `gcd(2, n)` and `n` agree modulo two.
* `ZMod.val_eq_ite_mod_two` and `ZMod.eq_one_of_ne_zero`: for `a : ZMod 2`,
  `a.val = if a ≠ 0 then 1 else 0` and `a ≠ 0 → a = 1`.
* `ZMod.neg_one_pow_val`, `ZMod.one_add_neg_one_pow_val`, and `ZMod.neg_one_pow_val_inj`:
  evaluation, indicator identity `1 + (-1) ^ a.val = if a = 0 then 2 else 0`, and injectivity of
  `a ↦ (-1 : R) ^ a.val` for `a : ZMod 2`.
* `ZMod.isUnit_two_mul_add`: `2c + u` is a unit in `ℤ/2^n` when `u` is.
* `ZMod.not_isUnit_two_mul`: `2c` is not a unit in `ℤ/2^{k+1}`.
* `ZMod.eq_two_mul_or_eq_two_mul_add_one`: every element of `ℤ/n` is even or odd.
* `Multiplicative.eq_one_or_eq_ofAdd_one`: every element of `C₂` is `1` or `σ`.
* `TauCeti.sum_cyclicTwo`: a sum over `C₂` is the sum of the values at `1` and at `σ`.
-/

public section

namespace ZMod

/-- `gcd(2, n)` and `n` have the same parity. -/
theorem natCast_gcd_two (n : ℕ) : ((Nat.gcd 2 n : ℕ) : ZMod 2) = n := by
  rw [Nat.gcd_rec, ← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

/-- **The representative of a residue modulo two is the indicator of being nonzero.** -/
theorem val_eq_ite_mod_two (a : ZMod 2) : a.val = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

/-- A nonzero residue modulo two is `1`. -/
theorem eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  Fin.eq_one_of_ne_zero a ha

/-- For `a : ZMod 2`, the sign `(-1) ^ a.val` in a ring is `1` at `0` and `-1` at `1`. -/
theorem neg_one_pow_val {R : Type*} [Ring R] (a : ZMod 2) :
    (-1 : R) ^ a.val = if a = 0 then 1 else -1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [val_eq_ite_mod_two]
  · simp [val_eq_ite_mod_two, ha]

/-- For `a : ZMod 2`, `1 + (-1) ^ a.val` is `2` at `0` and `0` at `1`. -/
theorem one_add_neg_one_pow_val {R : Type*} [Ring R] (a : ZMod 2) :
    (1 : R) + (-1 : R) ^ a.val = if a = 0 then 2 else 0 := by
  rw [neg_one_pow_val]
  split_ifs
  · exact one_add_one_eq_two
  · exact add_neg_cancel 1

/-- Over a ring in which `2 ≠ 0`, the sign `(-1) ^ a.val` determines `a : ZMod 2`. -/
@[simp]
theorem neg_one_pow_val_inj {R : Type*} [Ring R] [NeZero (2 : R)] {a b : ZMod 2} :
    (-1 : R) ^ a.val = (-1 : R) ^ b.val ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have h1 : (1 : R) ≠ -1 := fun h1 ↦ NeZero.ne (2 : R) <| by
    rw [← one_add_one_eq_two]
    nth_rw 2 [h1]
    exact add_neg_cancel 1
  rw [neg_one_pow_val, neg_one_pow_val] at h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact ha.trans hb.symm
  · simp [ha, hb, h1] at h
  · simp [ha, hb, h1.symm] at h
  · exact (eq_one_of_ne_zero ha).trans (eq_one_of_ne_zero hb).symm

variable {n : ℕ}

/-- An even element plus a unit is a unit in `ℤ/2^n`. -/
theorem isUnit_two_mul_add {c u : ZMod (2 ^ n)} (hu : IsUnit u) : IsUnit (2 * c + u) :=
  mod_cast isUnit_natCast_mul_add (p := 2) hu

/-- An even element of `ℤ/2^{k+1}` is not a unit. -/
theorem not_isUnit_two_mul {k : ℕ} (c : ZMod (2 ^ (k + 1))) : ¬ IsUnit (2 * c) :=
  have : Nontrivial (ZMod (2 ^ (k + 1))) :=
    ZMod.nontrivial_iff.2 (Nat.one_lt_two_pow k.succ_ne_zero).ne'
  mod_cast not_isUnit_natCast_mul (p := 2) c

/-- Every element of `ℤ/n` is even or odd, according to the parity of an integer lift. -/
theorem eq_two_mul_or_eq_two_mul_add_one (x : ZMod n) :
    (∃ c, x = 2 * c) ∨ ∃ c, x = 2 * c + 1 := by
  obtain ⟨X, rfl⟩ := ZMod.intCast_surjective x
  rcases Int.even_or_odd' X with ⟨c, rfl | rfl⟩
  · exact Or.inl ⟨c, by push_cast; ring⟩
  · exact Or.inr ⟨c, by push_cast; ring⟩

end ZMod

namespace Multiplicative

/-- Every element of `C₂` is `1` or the generator `σ = Multiplicative.ofAdd 1`. -/
theorem eq_one_or_eq_ofAdd_one (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  revert g
  decide

end Multiplicative

namespace TauCeti

/-- A sum over `C₂` is the sum of the values at `1` and at the generator. -/
theorem sum_cyclicTwo {M : Type*} [AddCommMonoid M] (f : Multiplicative (ZMod 2) → M) :
    ∑ g, f g = f 1 + f (Multiplicative.ofAdd 1) :=
  Fintype.sum_eq_add _ _ (by decide) fun g hg ↦ by
    rcases g.eq_one_or_eq_ofAdd_one with rfl | rfl <;> simp at hg

end TauCeti
