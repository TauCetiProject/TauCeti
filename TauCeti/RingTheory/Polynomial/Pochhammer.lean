/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Descending Pochhammer polynomials

This module provides basic lemmas for descending Pochhammer polynomials `descPochhammer R n`
over general rings.

Unlike Mathlib's `monic_descPochhammer` and `descPochhammer_natDegree`, which require
`[NoZeroDivisors R]` or `[Nontrivial R]`, the results here hold under minimal hypotheses by
transporting from the integer case `descPochhammer ℤ n`.

## Main declarations

* `TauCeti.monic_descPochhammer`: `descPochhammer R n` is monic over any ring `R`.
* `TauCeti.descPochhammer_natDegree`: `(descPochhammer R n).natDegree = n` for nontrivial `R`.
* `TauCeti.descPochhammer_degree`: `(descPochhammer R n).degree = n` for nontrivial `R`.
* `TauCeti.mul_prod_sq_sub_sq_eq_descPochhammer_eval`: the odd polynomial
  `x (x² - 1²) ⋯ (x² - k²)` is the falling factorial of degree `2k + 1` at `x + k`.
* `TauCeti.factorial_dvd_mul_prod_sq_sub_sq`: its values at the integers are divisible by
  `(2k + 1)!`.
-/

public section

namespace TauCeti

open Polynomial

/-- Unlike `monic_descPochhammer`, this drops `[Nontrivial R]` and `[NoZeroDivisors R]`
and holds over any ring. -/
theorem monic_descPochhammer {R : Type*} [Ring R] (n : ℕ) :
    Monic (descPochhammer R n) := by
  rw [← descPochhammer_map (Int.castRingHom R)]
  exact (_root_.monic_descPochhammer ℤ n).map (Int.castRingHom R)

/-- Unlike `descPochhammer_natDegree`, this drops `[NoZeroDivisors R]` and holds over any
nontrivial ring. -/
@[simp]
theorem descPochhammer_natDegree {R : Type*} [Ring R] [Nontrivial R] (n : ℕ) :
    (descPochhammer R n).natDegree = n := by
  rw [← descPochhammer_map (Int.castRingHom R),
    (_root_.monic_descPochhammer ℤ n).natDegree_map (Int.castRingHom R),
    _root_.descPochhammer_natDegree (R := ℤ)]

/-- The degree of the descending Pochhammer polynomial over any nontrivial ring is `n`. -/
@[simp]
theorem descPochhammer_degree {R : Type*} [Ring R] [Nontrivial R] (n : ℕ) :
    (descPochhammer R n).degree = n := by
  rw [Polynomial.degree_eq_natDegree (monic_descPochhammer n).ne_zero,
    descPochhammer_natDegree n]

/-! ### An odd polynomial as a falling factorial -/

/-- **An odd polynomial as a falling factorial.**  The product
`x · (x² - 1²) (x² - 2²) ⋯ (x² - k²)` is the product `(x + k) (x + k - 1) ⋯ (x - k)` of the
`2k + 1` consecutive values centred at `x`, that is, the falling factorial of degree `2k + 1`
evaluated at `x + k`. -/
theorem mul_prod_sq_sub_sq_eq_descPochhammer_eval {R : Type*} [CommRing R] (k : ℕ) (x : R) :
    x * ∏ m ∈ Finset.range k, (x ^ 2 - ((m : R) + 1) ^ 2)
      = (descPochhammer R (2 * k + 1)).eval (x + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (descPochhammer R (2 * k + 1 + 1 + 1)).eval (x + k + 1)
        = (x + k + 1) * (descPochhammer R (2 * k + 1 + 1)).eval (x + k) := by
      rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one,
        add_sub_cancel_right]
    have h2 : (descPochhammer R (2 * k + 1 + 1)).eval (x + k)
        = (descPochhammer R (2 * k + 1)).eval (x + k) * (x + k - ((2 * k + 1 : ℕ) : R)) :=
      descPochhammer_succ_eval _ _
    have hdeg : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [Finset.prod_range_succ, ← mul_assoc, ih, hdeg, Nat.cast_succ, ← add_assoc, h1, h2]
    push_cast
    ring

/-- The product `x · (x² - 1²) ⋯ (x² - k²)` is divisible by `(2k + 1)!` at every integer `x`,
being the product `(x - k) (x - k + 1) ⋯ (x + k)` of `2k + 1` consecutive integers
(`Nat.factorial_coe_dvd_prod`). -/
theorem factorial_dvd_mul_prod_sq_sub_sq (k : ℕ) (x : ℤ) :
    ((2 * k + 1).factorial : ℤ) ∣ x * ∏ m ∈ Finset.range k, (x ^ 2 - ((m : ℤ) + 1) ^ 2) := by
  have hprod : (descPochhammer ℤ (2 * k + 1)).eval (x + k)
      = ∏ i ∈ Finset.range (2 * k + 1), (x - k + i) := by
    rw [descPochhammer_eval_eq_prod_range, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (by have := Finset.mem_range.1 hi; omega)]
    push_cast
    ring
  rw [mul_prod_sq_sub_sq_eq_descPochhammer_eval, hprod]
  exact Nat.factorial_coe_dvd_prod _ _

end TauCeti
