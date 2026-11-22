/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# q-factorials and finite q-Pochhammer products

For a parameter `q` in a commutative semiring, the q-integer `[n]_q = ∑_{i < n} q ^ i` is
Mathlib's finite geometric sum; `mul_neg_geom_sum` gives `(1 - q) [n]_q = 1 - q ^ n` and
`one_geom_sum` gives `[n]_1 = n`. This file defines the two products built from it,

* the q-factorial `[n]_q! = ∏_{i = 1}^{n} [i]_q`, and
* the finite q-Pochhammer product `(x; q)_n = ∏_{i < n} (1 - x q ^ i)`,

and proves the elementary identities relating them. Everything is an identity of ring
elements, with no division, so it holds in positive characteristic and at roots of unity, and
with coefficient ring `R[q]` and `q = X` it gives polynomial identities. In particular
`(q; q)_N = ∏_{i = 1}^{N} (1 - q ^ i)` is the factorial polynomial whose multiples define the
cyclotomic (Habiro) completion of `R[q]`.

These are the asymmetric (Gaussian) conventions of basic hypergeometric series. The q-integers
here are not the symmetric quantum integers `TauCeti.qInt` (at a loop parameter) or
`TauCeti.quantumInteger`, and `TauCeti.qFactorial` is not built from them; see
`TauCeti.quantumFactorial` and `TauCeti.laurentQuantumFactorial` for the symmetric quantum
factorial.

## Main definitions

* `TauCeti.qFactorial q n`: the q-factorial `[n]_q! = ∏_{i < n} ∑_{j ≤ i} q ^ j`.
* `TauCeti.qPochhammer x q n`: the finite q-Pochhammer product `(x; q)_n`.

## Main results

* `TauCeti.qFactorial_base_one`: `[n]_1! = n!`.
* `TauCeti.map_qFactorial`, `TauCeti.map_qPochhammer`: both products commute with ring
  homomorphisms; `Polynomial.map_qFactorial`, `Polynomial.map_qPochhammer` and the `eval`
  versions are the coefficient-change and evaluation forms on `R[X]`.
* `TauCeti.qPochhammer_add`: concatenation, `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n`, with
  the shift law `TauCeti.qPochhammer_succ'`: `(x; q)_{n + 1} = (1 - x) (x q; q)_n`.
* `TauCeti.one_sub_pow_mul_qFactorial`: `(1 - q) ^ n [n]_q! = (q; q)_n`.
* `TauCeti.qPochhammer_base_one`: at base `q = 1`, `(x; 1)_n = (1 - x) ^ n`.
* `TauCeti.qPochhammer_eq_zero_iff`: without zero divisors, `(x; q)_n = 0` exactly when
  `x q ^ i = 1` for some `i < n`.
* `TauCeti.qPochhammer_inv`, `TauCeti.qPochhammer_inv_self`: for units `x` and `q`,
  `(x⁻¹; q⁻¹)_n = (-1) ^ n x⁻ⁿ q^{-n(n-1)/2} (x; q)_n`, and in particular
  `(q⁻¹; q⁻¹)_n = (-1) ^ n q^{-n(n+1)/2} (q; q)_n`.

## References

* G. Gasper, M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Encyclopedia of Mathematics and
  its Applications 96, Cambridge University Press, 2004, §1.2 and Appendix I.
* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25, Definition 1.1, Table 1 and Proposition 2.1.
-/

public section

open Finset

open scoped Nat

namespace TauCeti

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The q-factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q`, where `[i]_q = ∑_{j < i} q ^ j` is the
q-integer. This is the asymmetric (Gaussian) q-factorial; it is not built from the symmetric
quantum integer `TauCeti.qInt`, and `TauCeti.quantumFactorial` is the symmetric convention. -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j

/-- The defining product formula for the q-factorial. -/
theorem qFactorial_def (q : R) (n : ℕ) :
    qFactorial q n = ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j :=
  (rfl)

/-- `[0]_q! = 1`. -/
@[simp]
theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by
  simp [qFactorial_def]

/-- `[n + 1]_q! = [n]_q! [n + 1]_q`. -/
theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * ∑ j ∈ range (n + 1), q ^ j := by
  simp [qFactorial_def, prod_range_succ]

/-- `[1]_q! = 1`. -/
@[simp]
theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial_def]

/-- At `q = 1` the q-factorial is the ordinary factorial: `[n]_1! = n!`. -/
@[simp]
theorem qFactorial_base_one (n : ℕ) : qFactorial (1 : R) n = n ! := by
  simp [qFactorial_def, ← prod_range_add_one_eq_factorial]

/-- The q-factorial commutes with ring homomorphisms. -/
@[simp]
theorem map_qFactorial {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (q : R)
    (n : ℕ) : f (qFactorial q n) = qFactorial (f q) n := by
  simp [qFactorial_def, map_prod, map_sum]

end CommSemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The finite q-Pochhammer product `(x; q)_n = (1 - x) (1 - x q) ⋯ (1 - x q ^ (n - 1))` with
base `q`. -/
def qPochhammer (x q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - x * q ^ i)

/-- The defining product formula for the finite q-Pochhammer product. -/
theorem qPochhammer_def (x q : R) (n : ℕ) :
    qPochhammer x q n = ∏ i ∈ range n, (1 - x * q ^ i) :=
  (rfl)

/-- The empty q-Pochhammer product is one: `(x; q)_0 = 1`. -/
@[simp]
theorem qPochhammer_zero (x q : R) : qPochhammer x q 0 = 1 := by
  simp [qPochhammer_def]

/-- `(x; q)_1 = 1 - x`. -/
@[simp]
theorem qPochhammer_one (x q : R) : qPochhammer x q 1 = 1 - x := by
  simp [qPochhammer_def]

/-- Splitting off the last factor: `(x; q)_{n + 1} = (x; q)_n (1 - x q ^ n)`. -/
theorem qPochhammer_succ (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = qPochhammer x q n * (1 - x * q ^ n) := by
  simp [qPochhammer_def, prod_range_succ]

/-- Concatenation of q-Pochhammer products: `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n`. -/
theorem qPochhammer_add (x q : R) (m n : ℕ) :
    qPochhammer x q (m + n) = qPochhammer x q m * qPochhammer (x * q ^ m) q n := by
  simp [qPochhammer_def, prod_range_add, pow_add, mul_assoc]

/-- The shift law, splitting off the first factor: `(x; q)_{n + 1} = (1 - x) (x q; q)_n`. -/
theorem qPochhammer_succ' (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  rw [add_comm, qPochhammer_add, qPochhammer_one, pow_one]

/-- With `x = 0` every factor is one: `(0; q)_n = 1`. -/
@[simp]
theorem qPochhammer_zero_left (q : R) (n : ℕ) : qPochhammer 0 q n = 1 := by
  simp [qPochhammer_def]

/-- At `q = 1` the q-Pochhammer product is a power: `(x; 1)_n = (1 - x) ^ n`. -/
@[simp]
theorem qPochhammer_base_one (x : R) (n : ℕ) : qPochhammer x 1 n = (1 - x) ^ n := by
  simp [qPochhammer_def]

/-- `(q; q)_n = ∏_{i = 1}^{n} (1 - q ^ i)`, the form in which `(q; q)_n` is the factorial
polynomial. -/
theorem qPochhammer_self (q : R) (n : ℕ) :
    qPochhammer q q n = ∏ i ∈ range n, (1 - q ^ (i + 1)) := by
  simp [qPochhammer_def, pow_succ']

/-- The finite q-Pochhammer product commutes with ring homomorphisms. -/
@[simp]
theorem map_qPochhammer {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (x q : R)
    (n : ℕ) : f (qPochhammer x q n) = qPochhammer (f x) (f q) n := by
  simp [qPochhammer_def, map_prod]

/-- The q-factorial and the q-Pochhammer product are related by
`(1 - q) ^ n [n]_q! = (q; q)_n`. -/
theorem one_sub_pow_mul_qFactorial (q : R) (n : ℕ) :
    (1 - q) ^ n * qFactorial q n = qPochhammer q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, qPochhammer_succ, ← ih, ← pow_succ', ← mul_neg_geom_sum]
    ring

/-- A q-Pochhammer product vanishes as soon as one of its factors does: if `x q ^ i = 1` for
some `i < n`, then `(x; q)_n = 0`. -/
theorem qPochhammer_eq_zero_of_mul_pow_eq_one {x q : R} {n i : ℕ} (hi : i < n)
    (h : x * q ^ i = 1) : qPochhammer x q n = 0 :=
  prod_eq_zero (mem_range.mpr hi) (by rw [h, sub_self])

/-- Without zero divisors, `(x; q)_n = 0` exactly when `x q ^ i = 1` for some `i < n`. -/
theorem qPochhammer_eq_zero_iff [NoZeroDivisors R] [Nontrivial R] {x q : R} {n : ℕ} :
    qPochhammer x q n = 0 ↔ ∃ i < n, x * q ^ i = 1 := by
  simp [qPochhammer_def, prod_eq_zero_iff, sub_eq_zero, eq_comm (a := (1 : R))]

/-- The inverse-parameter formula: for units `x` and `q`,
`(x⁻¹; q⁻¹)_n = (-1) ^ n x⁻ⁿ q^{-n(n-1)/2} (x; q)_n`. -/
theorem qPochhammer_inv (x q : Rˣ) (n : ℕ) :
    qPochhammer (↑x⁻¹ : R) ↑q⁻¹ n =
      (-1) ^ n * (↑x⁻¹ : R) ^ n * (↑q⁻¹ : R) ^ (n * (n - 1) / 2) * qPochhammer (x : R) q n := by
  -- Each factor is `1 - x⁻¹ q⁻ⁱ = (-1) x⁻¹ q⁻ⁱ (1 - x qⁱ)`.
  have hfactor (i : ℕ) :
      1 - (↑x⁻¹ : R) * ↑q⁻¹ ^ i = -1 * ↑x⁻¹ * ↑q⁻¹ ^ i * (1 - x * q ^ i) := by
    have hx : (↑x⁻¹ : R) * x = 1 := x.inv_mul
    have hq : (↑q⁻¹ : R) ^ i * q ^ i = 1 := by rw [← mul_pow, q.inv_mul, one_pow]
    linear_combination -((↑q⁻¹ : R) ^ i * q ^ i) * hx - hq
  simp only [qPochhammer_def, hfactor, prod_mul_distrib, prod_const, card_range]
  rw [prod_pow_eq_pow_sum (range n) (fun i ↦ i), sum_range_id]

/-- The inverse-parameter formula for `(q; q)_n`: for a unit `q`,
`(q⁻¹; q⁻¹)_n = (-1) ^ n q^{-n(n+1)/2} (q; q)_n`. -/
theorem qPochhammer_inv_self (q : Rˣ) (n : ℕ) :
    qPochhammer (↑q⁻¹ : R) ↑q⁻¹ n =
      (-1) ^ n * (↑q⁻¹ : R) ^ (n * (n + 1) / 2) * qPochhammer (q : R) q n := by
  have hexp : n * (n + 1) / 2 = n + n * (n - 1) / 2 := by
    simpa [mul_comm, add_comm] using Nat.triangle_succ n
  rw [qPochhammer_inv, hexp, pow_add, mul_assoc ((-1 : R) ^ n)]

end CommRing

/-! ### Polynomial coefficients

With coefficient ring `R[X]` these give the coefficient-change and evaluation behaviour of the
polynomial products such as `(X; X)_n`. -/

section Polynomial

open Polynomial

/-- Coefficient change commutes with the q-factorial. -/
@[simp]
theorem _root_.Polynomial.map_qFactorial {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : R[X]) (n : ℕ) : (qFactorial q n).map f = qFactorial (q.map f) n :=
  TauCeti.map_qFactorial (mapRingHom f) q n

/-- Evaluation commutes with the q-factorial. -/
@[simp]
theorem _root_.Polynomial.eval_qFactorial {R : Type*} [CommSemiring R] (a : R) (q : R[X])
    (n : ℕ) : (qFactorial q n).eval a = qFactorial (q.eval a) n :=
  TauCeti.map_qFactorial (evalRingHom a) q n

/-- Coefficient change commutes with the finite q-Pochhammer product. -/
@[simp]
theorem _root_.Polynomial.map_qPochhammer {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x q : R[X]) (n : ℕ) : (qPochhammer x q n).map f = qPochhammer (x.map f) (q.map f) n :=
  TauCeti.map_qPochhammer (mapRingHom f) x q n

/-- Evaluation commutes with the finite q-Pochhammer product. -/
@[simp]
theorem _root_.Polynomial.eval_qPochhammer {R : Type*} [CommRing R] (a : R) (x q : R[X])
    (n : ℕ) : (qPochhammer x q n).eval a = qPochhammer (x.eval a) (q.eval a) n :=
  TauCeti.map_qPochhammer (evalRingHom a) x q n

end Polynomial

/-! ### Reference values -/

/-- `[3]_q! = (1 + q) (1 + q + q²)`. -/
example {R : Type*} [CommSemiring R] (q : R) : qFactorial q 3 = (1 + q) * (1 + q + q ^ 2) := by
  simp only [qFactorial_def, prod_range_succ, sum_range_succ, prod_range_zero, sum_range_zero]
  ring

/-- `[3]_1! = 6`. -/
example : qFactorial (1 : ℤ) 3 = 6 := by
  simp [Nat.factorial]

/-- `(q; q)_2 = (1 - q) (1 - q²)`. -/
example {R : Type*} [CommRing R] (q : R) : qPochhammer q q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [qPochhammer_self, prod_range_succ]

/-- `(x; 1)_3 = (1 - x) ^ 3`, with no division at `q = 1`. -/
example {R : Type*} [CommRing R] (x : R) : qPochhammer x 1 3 = (1 - x) ^ 3 :=
  qPochhammer_base_one x 3

/-- `(2; 3)_3 = (1 - 2) (1 - 6) (1 - 18) = -85`. -/
example : qPochhammer (2 : ℤ) 3 3 = -85 := by
  simp [qPochhammer_def, prod_range_succ]

/-- `x = 1` makes every positive product vanish: `(1; q)_n = 0` for `n > 0`. -/
example {R : Type*} [CommRing R] (q : R) {n : ℕ} (hn : 0 < n) : qPochhammer 1 q n = 0 :=
  qPochhammer_eq_zero_of_mul_pow_eq_one hn (by simp)

end TauCeti
