/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Algebra.Group.AddChar

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. This file records its value at
the half-way point of an even level: at level `2n` it sends `n` to `exp (πi) = -1`, together with
conversions between products of `{±1}`-signs and `ZMod (2 * n)` half-level shifts under
`ZMod.stdAddChar`.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
* `ZMod.stdAddChar_natCast_self`: `ZMod.stdAddChar (n : ZMod (2n)) = -1`.
* `ZMod.prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite`: absorbing a product of `{±1}` powers into
  a `ZMod (2n)` shift inside `stdAddChar`.
* `ZMod.stdAddChar_sum_add_ite_eq_prod_pow_mul_stdAddChar`: expanding a sum of conditional `n`
  shifts inside `stdAddChar` into a product of `{±1}` powers.
-/

public section

namespace ZMod

open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- The standard additive character of `ZMod (2 * n)` sends `n` to `-1`. -/
theorem stdAddChar_natCast_self (n : ℕ) [NeZero n] :
    stdAddChar ((n : ℕ) : ZMod (2 * n)) = -1 := by
  rw [stdAddChar_apply, coe_toCircle_natCast_self]

/-- Multiplying `stdAddChar x` on `ZMod (2 * n)` by a product of `{±1}` powers shifts `x` by `n`
whenever the product is `-1`. -/
theorem prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite {ι : Type*} {n : ℕ} [NeZero n]
    {u : Finset ι} {s : ι → ℤ} (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1)
    (x : ZMod (2 * n)) (e : ι → ℕ) :
    (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar x =
      stdAddChar (x + if ∏ i ∈ u, s i ^ e i = -1 then (n : ZMod (2 * n)) else 0) := by
  have hprod : (∏ i ∈ u, s i ^ e i) = 1 ∨ (∏ i ∈ u, s i ^ e i) = -1 := by
    refine Finset.prod_induction _ (fun y ↦ y = 1 ∨ y = -1)
      (fun _ _ ha hb ↦ by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num)
      (Or.inl rfl) fun i hi ↦ ?_
    rcases hs i hi with h | h
    · exact Or.inl (by rw [h, one_pow])
    · rw [h]
      rcases Nat.even_or_odd (e i) with he | he <;> simp [he.neg_one_pow]
  have hcast : (∏ i ∈ u, (s i : ℂ) ^ e i) = ((∏ i ∈ u, s i ^ e i : ℤ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rcases hprod with h | h <;> simp [h, AddChar.map_add_eq_mul, stdAddChar_natCast_self]

/-- Evaluating `stdAddChar` on a sum of `ZMod (2 * n)` terms shifted by `n` when `Odd (e i)` and
`s i = -1` factors out the product of `(s i : ℂ) ^ e i`. -/
theorem stdAddChar_sum_add_ite_eq_prod_pow_mul_stdAddChar {ι : Type*} {n : ℕ} [NeZero n]
    {u : Finset ι} {s : ι → ℤ} (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1)
    (t : ι → ZMod (2 * n)) (e : ι → ℕ) :
    stdAddChar (∑ i ∈ u, (t i + if Odd (e i) ∧ s i = -1 then (n : ZMod (2 * n)) else 0)) =
      (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar (∑ i ∈ u, t i) := by
  rw [Finset.sum_add_distrib, AddChar.map_add_eq_mul, mul_comm, AddChar.map_sum_eq_prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases hs i hi with hsi | hsi
  · simp [hsi]
  · rcases Nat.even_or_odd (e i) with hm | hm
    · simp [hsi, hm.neg_one_pow, Nat.not_odd_iff_even.mpr hm]
    · simp only [hsi, hm, hm.neg_one_pow, and_self, ↓reduceIte, Int.cast_neg, Int.cast_one]
      exact stdAddChar_natCast_self n

end ZMod
