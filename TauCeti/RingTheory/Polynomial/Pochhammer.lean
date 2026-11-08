/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Binomial

/-!
# Descending Pochhammer polynomials

This module provides basic lemmas for descending Pochhammer polynomials `descPochhammer R n`
over general rings, together with their sums over integer intervals and their forward
differences.

The monicity result holds over any ring, and the degree results require only a nontrivial ring.
The summation identity also holds over arbitrary rings; no division by `m + 1` is needed.

## Main declarations

* `TauCeti.monic_descPochhammer`: `descPochhammer R n` is monic over any ring `R`.
* `TauCeti.descPochhammer_natDegree`: `(descPochhammer R n).natDegree = n` for nontrivial `R`.
* `TauCeti.descPochhammer_degree`: `(descPochhammer R n).degree = n` for nontrivial `R`.
* `TauCeti.descPochhammer_succ_eval_add_one`: the falling factorial of degree `m + 1` at `x + 1` is
  `x + 1` times the one of degree `m` at `x`.
* `TauCeti.descPochhammer_succ_smeval_of_sq_eq_zero`: at a square-zero element `ε`, the falling
  factorial of degree `n + 1` is `(-1) ^ n n! ε`.
* `TauCeti.sum_Ico_descPochhammer_eval`: its sum over a half-open integer interval is the endpoint
  difference of the next falling factorial, after clearing the denominator.
* `TauCeti.mul_prod_sq_sub_sq_eq_descPochhammer_eval`: the odd polynomial
  `x (x² - 1²) ⋯ (x² - k²)` is the falling factorial of degree `2k + 1` at `x + k`.
* `TauCeti.factorial_dvd_mul_prod_sq_sub_sq`: its values at the integers are divisible by
  `(2k + 1)!`.
* `TauCeti.two_mul_prod_sq_sub_sq_eq`: twice the even polynomial `(x² - 0²) ⋯ (x² - k²)` is the
  sum of the falling factorials of degree `2k + 2` at `x + k + 1` and at `x + k`.
* `TauCeti.mul_factorial_dvd_prod_sq_sub_sq`: its values at the integers are divisible by
  `(k + 1) (2k + 1)! = (2k + 2)! / 2`, which is its value at `k + 1`
  (`TauCeti.prod_sq_sub_sq_eq_mul_factorial`).
* `TauCeti.prod_sub_mul_add_add_one_eq_descPochhammer_eval`: the polynomial
  `∏_{m < k} (x - m) (x + m + 1)` in `x (x + 1)` is the falling factorial of degree `2k` at `x + k`.
* `TauCeti.two_mul_add_one_mul_prod_sub_mul_add_add_one_eq`: weighted by `2x + 1`, it is the sum
  of the falling factorials of degree `2k + 1` at `x + k + 1` and at `x + k`.
* `TauCeti.factorial_dvd_two_mul_add_one_mul_prod_sub_mul_add_add_one`: the values of the weighted
  polynomial at the integers are divisible by `(2k + 1)!`.
* `TauCeti.fwdDiff_descPochhammer_succ_eval`: the forward difference of the falling factorial of
  degree `n + 1` is `n + 1` times the one of degree `n`.
* `TauCeti.fwdDiff_iter_descPochhammer_eval`: the `k`-th forward difference of the falling
  factorial of degree `j` is `j (j - 1) ⋯ (j - k + 1)` times the falling factorial of degree
  `j - k`.
* `TauCeti.pow_eq_sum_stirlingSecond_mul_descPochhammer_eval`: in any ring, `x ^ m` is
  the sum of the falling factorials of degree `j` at `x` weighted by the Stirling numbers of the
  second kind `S(m, j)`.
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

/-- Shifting the argument of a falling factorial by one strips off its leading linear factor:
the degree `m + 1` falling factorial at `x + 1` is `(x + 1)` times the degree `m` one at `x`. -/
theorem descPochhammer_succ_eval_add_one {R : Type*} [Ring R] (m : ℕ) (x : R) :
    (descPochhammer R (m + 1)).eval (x + 1) = (x + 1) * (descPochhammer R m).eval x := by
  rw [← descPochhammer_map (Int.castRingHom R), ← descPochhammer_map (Int.castRingHom R) m,
    eval_map, eval_map, ← algebraMap_int_eq, ← aeval_def, ← aeval_def, descPochhammer_succ_left,
    map_mul, aeval_X, aeval_comp, map_sub, aeval_X, map_one, add_sub_cancel_right]

/-- The descending Pochhammer polynomial at a square-zero element keeps only its linear term:
`ε (ε - 1) ⋯ (ε - n) = (-1) ^ n n! ε`. -/
theorem descPochhammer_succ_smeval_of_sq_eq_zero {R : Type*} [Ring R] {ε : R} (hε : ε ^ 2 = 0)
    (n : ℕ) : (descPochhammer ℤ (n + 1)).smeval ε = ((-1) ^ n * n.factorial : ℤ) • ε := by
  induction n with
  | zero => simp [Polynomial.smeval_X]
  | succ n ih =>
    -- Multiplying by `ε - n` kills the square term and scales by `-n`.
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih]
    simp [Polynomial.smeval_X, Polynomial.smeval_natCast, -zsmul_eq_mul, mul_sub, ← sq, hε,
      Nat.factorial_succ, mul_add_one, -nsmul_eq_mul, ← nsmul_eq_mul' ε n]
    module

/-! ### Sums over integer intervals -/

/-- **The discrete antiderivative of a falling factorial.** Summing the degree `m` falling
factorial over the integer range `p ≤ t < q` gives the difference of the degree `m + 1` falling
factorial at the endpoints, after multiplying the sum by `m + 1`. The identity holds in any
coefficient ring; it does not require `m + 1` to be invertible.

For `q < p` the interval is empty while the endpoint difference need not vanish. -/
theorem sum_Ico_descPochhammer_eval {R : Type*} [Ring R] (m : ℕ) {p q : ℤ} (h : p ≤ q) :
    ((m : R) + 1) * ∑ t ∈ Finset.Ico p q, (descPochhammer R m).eval (t : R)
      = (descPochhammer R (m + 1)).eval (q : R)
        - (descPochhammer R (m + 1)).eval (p : R) := by
  -- Translate the integer interval to a range so that the range telescoping identity applies.
  rw [Int.Ico_eq_finset_map, Finset.sum_map, Finset.mul_sum]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have hq : (((q - p).toNat : ℕ) : ℤ) = q - p := by omega
  have key := Finset.sum_range_sub
    (fun k : ℕ => (descPochhammer R (m + 1)).eval ((p + k : ℤ) : R))
    (q - p).toNat
  simp only [hq, Nat.cast_zero, add_zero] at key
  simp only [Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_one] at key
  rw [Finset.sum_congr rfl (fun k _ => by
    have hdiff := Ring.descPochhammer_succ_succ_smeval ((p : R) + k) m
    simp only [← aeval_eq_smeval, aeval_def, algebraMap_int_eq, ← eval_map,
      descPochhammer_map, nsmul_eq_mul, Nat.cast_add_one] at hdiff
    simpa only [add_assoc, Int.cast_one] using sub_eq_iff_eq_add.mpr hdiff)] at key
  simpa using key

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
        = (x + k + 1) * (descPochhammer R (2 * k + 1 + 1)).eval (x + k) :=
      descPochhammer_succ_eval_add_one _ _
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

/-! ### An even polynomial as two falling factorials -/

/-- **An even polynomial as two falling factorials.**  The product
`(x² - 0²) (x² - 1²) ⋯ (x² - k²)` is `x` times the falling factorial of degree `2k + 1` at
`x + k`, so doubling it, as `2x = (x + k + 1) + (x - k - 1)`, splits it into the falling factorials
of degree `2k + 2` at `x + k + 1` and at `x + k`. -/
theorem two_mul_prod_sq_sub_sq_eq {R : Type*} [CommRing R] (k : ℕ) (x : R) :
    2 * ∏ m ∈ Finset.range (k + 1), (x ^ 2 - (m : R) ^ 2)
      = (descPochhammer R (2 * k + 2)).eval (x + k + 1)
        + (descPochhammer R (2 * k + 2)).eval (x + k) := by
  have h0 : ∏ m ∈ Finset.range (k + 1), (x ^ 2 - (m : R) ^ 2)
      = x * (x * ∏ m ∈ Finset.range k, (x ^ 2 - ((m : R) + 1) ^ 2)) := by
    rw [Finset.prod_range_succ']
    push_cast
    ring
  have h1 : (descPochhammer R (2 * k + 1 + 1)).eval (x + k + 1)
      = (x + k + 1) * (descPochhammer R (2 * k + 1)).eval (x + k) :=
    descPochhammer_succ_eval_add_one _ _
  have h2 : (descPochhammer R (2 * k + 1 + 1)).eval (x + k)
      = (descPochhammer R (2 * k + 1)).eval (x + k) * (x + k - ((2 * k + 1 : ℕ) : R)) :=
    descPochhammer_succ_eval _ _
  rw [h0, mul_prod_sq_sub_sq_eq_descPochhammer_eval, h1, h2]
  push_cast
  ring

/-- The product `(x² - 0²) (x² - 1²) ⋯ (x² - k²)` is divisible by
`(k + 1) (2k + 1)! = (2k + 2)! / 2` at every integer `x`: twice it is a sum of two falling
factorials of degree `2k + 2` (`TauCeti.two_mul_prod_sq_sub_sq_eq`), each a multiple of
`(2k + 2)!` (`Ring.descPochhammer_eq_factorial_smul_choose`). -/
theorem mul_factorial_dvd_prod_sq_sub_sq (k : ℕ) (x : ℤ) :
    ((k + 1) * (2 * k + 1).factorial : ℤ) ∣ ∏ m ∈ Finset.range (k + 1), (x ^ 2 - (m : ℤ) ^ 2) := by
  have hdvd : ∀ y : ℤ, ((2 * k + 2).factorial : ℤ) ∣ (descPochhammer ℤ (2 * k + 2)).eval y :=
    fun y => ⟨Ring.choose y (2 * k + 2), by
      rw [eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]⟩
  have hfac : ((2 * k + 2).factorial : ℤ) = 2 * ((k + 1) * (2 * k + 1).factorial) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h := dvd_add (hdvd (x + k + 1)) (hdvd (x + k))
  rw [← two_mul_prod_sq_sub_sq_eq, hfac] at h
  exact (mul_dvd_mul_iff_left two_ne_zero).1 h

/-- The value of `(x² - 0²) (x² - 1²) ⋯ (x² - k²)` at `x = k + 1` is `(k + 1) (2k + 1)!`, which is
`(2k + 2)! / 2`. -/
theorem prod_sq_sub_sq_eq_mul_factorial {R : Type*} [CommRing R] (k : ℕ) :
    ∏ m ∈ Finset.range (k + 1), (((k + 1 : ℕ) : R) ^ 2 - (m : R) ^ 2)
      = (((k + 1) * (2 * k + 1).factorial : ℕ) : R) := by
  have hZ : ∏ m ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℤ) ^ 2 - (m : ℤ) ^ 2)
      = (((k + 1) * (2 * k + 1).factorial : ℕ) : ℤ) := by
    have h := two_mul_prod_sq_sub_sq_eq k ((k + 1 : ℕ) : ℤ)
    have e1 : ((k + 1 : ℕ) : ℤ) + k + 1 = ((2 * k + 2 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((k + 1 : ℕ) : ℤ) + k = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_self, Nat.descFactorial_of_lt (by omega), Nat.cast_zero, add_zero,
      Nat.factorial_succ] at h
    push_cast at h ⊢
    linarith
  have := congrArg (Int.cast : ℤ → R) hZ
  push_cast at this ⊢
  exact this

/-! ### A polynomial in `x (x + 1)` as a falling factorial -/

/-- **A polynomial in `x (x + 1)` as a falling factorial.**  The product
`∏_{m < k} (x - m) (x + m + 1)`, whose factors are `x (x + 1) - m (m + 1)`, is the product
`(x + k) (x + k - 1) ⋯ (x - k + 1)` of the `2k` consecutive values centred at `x + 1/2`, that is,
the falling factorial of degree `2k` evaluated at `x + k`. -/
theorem prod_sub_mul_add_add_one_eq_descPochhammer_eval {R : Type*} [CommRing R] (k : ℕ)
    (x : R) :
    ∏ m ∈ Finset.range k, (x - m) * (x + m + 1) = (descPochhammer R (2 * k)).eval (x + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (descPochhammer R (2 * k + 1 + 1)).eval (x + k + 1)
        = (x + k + 1) * (descPochhammer R (2 * k + 1)).eval (x + k) :=
      descPochhammer_succ_eval_add_one _ _
    have h2 : (descPochhammer R (2 * k + 1)).eval (x + k)
        = (descPochhammer R (2 * k)).eval (x + k) * (x + k - ((2 * k : ℕ) : R)) :=
      descPochhammer_succ_eval _ _
    have hdeg : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [Finset.prod_range_succ, ih, hdeg, Nat.cast_succ, ← add_assoc, h1, h2]
    push_cast
    ring

/-- **The weighted polynomial in `x (x + 1)` as two falling factorials.**  Weighting
`∏_{m < k} (x - m) (x + m + 1)` by `2x + 1 = (x + k + 1) + (x - k)` splits it into the falling
factorials of degree `2k + 1` at `x + k + 1` and at `x + k`. -/
theorem two_mul_add_one_mul_prod_sub_mul_add_add_one_eq {R : Type*} [CommRing R] (k : ℕ)
    (x : R) :
    (2 * x + 1) * ∏ m ∈ Finset.range k, (x - m) * (x + m + 1)
      = (descPochhammer R (2 * k + 1)).eval (x + k + 1)
        + (descPochhammer R (2 * k + 1)).eval (x + k) := by
  have h1 : (descPochhammer R (2 * k + 1)).eval (x + k + 1)
      = (x + k + 1) * (descPochhammer R (2 * k)).eval (x + k) :=
    descPochhammer_succ_eval_add_one _ _
  have h2 : (descPochhammer R (2 * k + 1)).eval (x + k)
      = (descPochhammer R (2 * k)).eval (x + k) * (x + k - ((2 * k : ℕ) : R)) :=
    descPochhammer_succ_eval _ _
  rw [prod_sub_mul_add_add_one_eq_descPochhammer_eval, h1, h2]
  push_cast
  ring

/-- The weighted product `(2x + 1) ∏_{m < k} (x - m) (x + m + 1)` is divisible by `(2k + 1)!` at
every integer `x`, being a sum of two falling factorials of degree `2k + 1`
(`Ring.descPochhammer_eq_factorial_smul_choose`). -/
theorem factorial_dvd_two_mul_add_one_mul_prod_sub_mul_add_add_one (k : ℕ) (x : ℤ) :
    ((2 * k + 1).factorial : ℤ)
      ∣ (2 * x + 1) * ∏ m ∈ Finset.range k, (x - m) * (x + m + 1) := by
  have hdvd : ∀ y : ℤ, ((2 * k + 1).factorial : ℤ) ∣ (descPochhammer ℤ (2 * k + 1)).eval y :=
    fun y => ⟨Ring.choose y (2 * k + 1), by
      rw [eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]⟩
  rw [two_mul_add_one_mul_prod_sub_mul_add_add_one_eq]
  exact dvd_add (hdvd _) (hdvd _)

/-! ### Forward differences -/

open scoped fwdDiff

/-- **One forward difference of a falling factorial.** The forward difference of the falling
factorial of degree `n + 1` is `n + 1` times the falling factorial of degree `n`. -/
theorem fwdDiff_descPochhammer_succ_eval {R : Type*} [Ring R] (n : ℕ) :
    Δ_[1] (fun x : R ↦ (descPochhammer R (n + 1)).eval x) =
      fun x ↦ ((n + 1 : ℕ) : R) * (descPochhammer R n).eval x := by
  funext x
  -- the falling factorial at `x` commutes with `x`, as it is an integral polynomial in `x`
  have hx : Commute ((descPochhammer R n).eval x) x := by
    rw [← descPochhammer_map (Int.castRingHom R), eval_map, ← algebraMap_int_eq, ← aeval_def]
    simpa using (commute_X (descPochhammer ℤ n)).symm.map (aeval x)
  rw [fwdDiff, descPochhammer_succ_eval_add_one, descPochhammer_succ_eval,
    (hx.sub_right (Nat.cast_commute n _).symm).eq, ← sub_mul, add_sub_sub_cancel,
    Nat.cast_add_one, add_comm (1 : R)]

/-- **Forward differences of falling factorials.** The `k`-th forward difference of the falling
factorial `x (x - 1) ⋯ (x - j + 1)` of degree `j` is `j (j - 1) ⋯ (j - k + 1)` times the falling
factorial of degree `j - k`. In particular it vanishes for `k > j`. -/
theorem fwdDiff_iter_descPochhammer_eval {R : Type*} [Ring R] (j k : ℕ) :
    Δ_[1]^[k] (fun x : R ↦ (descPochhammer R j).eval x) =
      fun x ↦ (j.descFactorial k : R) * (descPochhammer R (j - k)).eval x := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases j with
    | zero => simp [Function.iterate_fixed]
    | succ i =>
      simp_rw [fwdDiff_descPochhammer_succ_eval, ← smul_eq_mul, ← Pi.smul_def]
      rw [fwdDiff_iter_const_smul, ih, Nat.succ_descFactorial_succ, Nat.add_sub_add_right]
      funext x
      simp [mul_assoc]

/-- **Powers in the falling-factorial basis.** In any ring, `x ^ m` is the sum of the
falling factorials of degree `j ≤ m` at `x`, weighted by the Stirling numbers of the second kind
`S(m, j)`. This is the ring version of `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`. -/
theorem pow_eq_sum_stirlingSecond_mul_descPochhammer_eval {R : Type*} [Ring R] (m : ℕ)
    (x : R) :
    x ^ m = ∑ j ∈ Finset.range (m + 1),
      (m.stirlingSecond j : R) * (descPochhammer R j).eval x := by
  -- the identity holds in `ℤ[X]`, since both sides agree at every natural number
  have hP : (X ^ m : ℤ[X]) =
      ∑ j ∈ Finset.range (m + 1), (m.stirlingSecond j : ℤ[X]) * descPochhammer ℤ j := by
    refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := (Nat.cast : ℕ → ℤ)) Nat.cast_injective fun n ↦ ?_)
    simp only [Set.mem_ofPred_eq, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast,
      descPochhammer_eval_eq_descFactorial]
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n m
  have hD (j : ℕ) : aeval x (descPochhammer ℤ j) = (descPochhammer R j).eval x := by
    rw [aeval_def, algebraMap_int_eq, eval₂_eq_eval_map, descPochhammer_map]
  simpa [hD] using congrArg (aeval x) hP

end TauCeti
