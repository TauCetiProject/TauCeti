/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.LucasLehmer
public import TauCeti.NumberTheory.LucasSequence.Basic
public import TauCeti.RingTheory.Polynomial.Dickson

/-!
# Polynomial evaluations, generating functions, and specializations of Lucas sequences

Evaluating Mathlib's Dickson polynomials of the second and first kinds at `P` with parameter `Q`
recovers `lucasU P Q (n + 1)` and `lucasV P Q n`. Combining those identifications with the
Dickson evaluation and power-series identities in `TauCeti.RingTheory.Polynomial.Dickson` yields
the symmetric root-power (Binet) formulas, repeated-root values, weighted homogeneity, parity,
Chebyshev specializations, period-`6` periodicity at `(1, 1)`, and rational generating functions of
`lucasU` and `lucasV`, together with their `LinearRecurrence` solutions and classical
specializations (`Nat.fib`, `mersenne`, and `LucasLehmer.s`).

## Main results

* `TauCeti.lucasU_succ_eq_dickson_eval`, `TauCeti.lucasV_eq_dickson_eval`:
  `lucasU P Q (n + 1) = (Polynomial.dickson 2 Q n).eval P` and
  `lucasV P Q n = (Polynomial.dickson 1 Q n).eval P`.
* `TauCeti.lucasU_add_mul_mul_sub`, `TauCeti.lucasU_add_mul_eq_div`, `TauCeti.lucasV_add_mul`:
  the cleared-denominator and field Binet identities for `lucasU (x + y) (x * y)` and the power-sum
  identity `lucasV (x + y) (x * y) n = x ^ n + y ^ n`.
* `TauCeti.lucasU_two_mul_sq_succ`, `TauCeti.lucasV_two_mul_sq`: repeated-root evaluations at
  `P = 2 * x`, `Q = x ^ 2`.
* `TauCeti.mk_lucasU_mul_one_sub_add_eq_X`, `TauCeti.mk_lucasV_mul_one_sub_add_eq`: rational
  generating functions of `lucasU` and `lucasV` in `R⟦X⟧`.
* `TauCeti.isSolution_lucasU`, `TauCeti.isSolution_lucasV`: `lucasU P Q` and `lucasV P Q` solve
  the order-two linear recurrence `⟨2, ![-Q, P]⟩`.
* `TauCeti.lucasU_one_neg_one`, `TauCeti.lucasU_three_two_eq_mersenne`,
  `TauCeti.lucasV_four_one_two_pow`: specializations to `Nat.fib`, `mersenne`, and `LucasLehmer.s`.

## References

* R. D. Carmichael, *On the numerical factors of the arithmetic forms αⁿ ± βⁿ*, Annals of
  Mathematics (2) **15** (1913), 30–48.
* R. Lidl, G. L. Mullen, and G. Turnwald, *Dickson Polynomials*, Longman, 1993.
-/

public section

open Finset Polynomial

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Dickson and Chebyshev polynomial evaluations -/

/-- `lucasU P Q (n + 1)` is the Dickson polynomial of the second kind `dickson 2 Q n` evaluated at
`P`. -/
theorem lucasU_succ_eq_dickson_eval (P Q : R) (n : ℕ) :
    lucasU P Q (n + 1) = (dickson 2 Q n).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more n ih₀ ih₁ =>
    rw [lucasU_add_two P Q (n + 1), dickson_add_two, eval_sub, eval_mul, eval_X, eval_mul, eval_C,
      ih₁, ih₀]

/-- `lucasV P Q n` is the Dickson polynomial of the first kind `dickson 1 Q n` evaluated at `P`. -/
theorem lucasV_eq_dickson_eval (P Q : R) (n : ℕ) :
    lucasV P Q n = (dickson 1 Q n).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more n ih₀ ih₁ =>
    simp [lucasV_add_two, dickson_add_two, ih₀, ih₁]

/-- For `Q = 1`, `lucasU P 1 (n + 1)` evaluates the rescaled Chebyshev polynomial `Chebyshev.S`. -/
theorem lucasU_one_right_succ_eq_chebyshev_S_eval (P : R) (n : ℕ) :
    lucasU P 1 (n + 1) = (Chebyshev.S R n).eval P := by
  rw [lucasU_succ_eq_dickson_eval, dickson_two_one_eq_chebyshev_S]

/-- For `Q = 1`, `lucasV P 1 n` evaluates the rescaled Chebyshev polynomial `Chebyshev.C`. -/
theorem lucasV_one_right_eq_chebyshev_C_eval (P : R) (n : ℕ) :
    lucasV P 1 n = (Chebyshev.C R n).eval P := by
  rw [lucasV_eq_dickson_eval, dickson_one_one_eq_chebyshev_C]

/-! ### Binet root-power identities, repeated roots, homogeneity, and parity -/

/-- Complete homogeneous symmetric expansion of `lucasU (x + y) (x * y) (n + 1)`. -/
theorem lucasU_add_mul_succ (x y : R) (n : ℕ) :
    lucasU (x + y) (x * y) (n + 1) = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) := by
  rw [lucasU_succ_eq_dickson_eval, dickson_two_eval_add rfl]

/-- **Cleared-denominator Binet formula for `lucasU`**:
`lucasU (x + y) (x * y) n * (x - y) = x ^ n - y ^ n` in every commutative ring, including at
`n = 0` and at repeated roots `x = y`. -/
theorem lucasU_add_mul_mul_sub (x y : R) (n : ℕ) :
    lucasU (x + y) (x * y) n * (x - y) = x ^ n - y ^ n := by
  cases n with
  | zero => simp
  | succ n => rw [lucasU_succ_eq_dickson_eval, dickson_two_eval_add_mul_sub rfl]

/-- **Root-power formula for `lucasV`**: `lucasV (x + y) (x * y) n = x ^ n + y ^ n`. -/
theorem lucasV_add_mul (x y : R) (n : ℕ) :
    lucasV (x + y) (x * y) n = x ^ n + y ^ n := by
  rw [lucasV_eq_dickson_eval, dickson_one_eval_add rfl]

/-- At the repeated-root parameters `P = 2 * x`, `Q = x ^ 2`,
`lucasU (2 * x) (x ^ 2) (n + 1) = (n + 1) * x ^ n`. -/
@[simp]
theorem lucasU_two_mul_sq_succ (x : R) (n : ℕ) :
    lucasU (2 * x) (x ^ 2) (n + 1) = (n + 1) * x ^ n := by
  rw [lucasU_succ_eq_dickson_eval, dickson_two_sq_eval_two_mul]

/-- At the repeated-root parameters `P = 2 * x`, `Q = x ^ 2`,
`lucasV (2 * x) (x ^ 2) n = 2 * x ^ n`. -/
@[simp]
theorem lucasV_two_mul_sq (x : R) (n : ℕ) :
    lucasV (2 * x) (x ^ 2) n = 2 * x ^ n := by
  rw [two_mul x, sq x, lucasV_add_mul, two_mul]

/-- Weighted homogeneity of `lucasU`: scaling `P` by `s` and `Q` by `s ^ 2` scales `U_{n + 1}` by
`s ^ n`. -/
@[simp]
theorem lucasU_mul_sq_mul_succ (s P Q : R) (n : ℕ) :
    lucasU (s * P) (s ^ 2 * Q) (n + 1) = s ^ n * lucasU P Q (n + 1) := by
  rw [lucasU_succ_eq_dickson_eval, lucasU_succ_eq_dickson_eval, dickson_sq_mul_eval_mul]

/-- Weighted homogeneity of `lucasV`: scaling `P` by `s` and `Q` by `s ^ 2` scales `V_n` by
`s ^ n`. -/
@[simp]
theorem lucasV_mul_sq_mul (s P Q : R) (n : ℕ) :
    lucasV (s * P) (s ^ 2 * Q) n = s ^ n * lucasV P Q n := by
  rw [lucasV_eq_dickson_eval, lucasV_eq_dickson_eval, dickson_sq_mul_eval_mul]

/-- Parity of `lucasU` in the first parameter: `U_{n + 1}(-P, Q) = (-1) ^ n * U_{n + 1}(P, Q)`. -/
theorem lucasU_neg_left_succ (P Q : R) (n : ℕ) :
    lucasU (-P) Q (n + 1) = (-1) ^ n * lucasU P Q (n + 1) := by
  rw [lucasU_succ_eq_dickson_eval, lucasU_succ_eq_dickson_eval, dickson_eval_neg]

/-- Parity of `lucasV` in the first parameter: `V_n(-P, Q) = (-1) ^ n * V_n(P, Q)`. -/
theorem lucasV_neg_left (P Q : R) (n : ℕ) :
    lucasV (-P) Q n = (-1) ^ n * lucasV P Q n := by
  rw [lucasV_eq_dickson_eval, lucasV_eq_dickson_eval, dickson_eval_neg]

/-! ### Rational generating functions -/

/-- **Generating function of `lucasU`**:
`(∑ₙ Uₙ(P, Q) Xⁿ) * (1 - P X + Q X²) = X` in `R⟦X⟧`. -/
theorem mk_lucasU_mul_one_sub_add_eq_X (P Q : R) :
    PowerSeries.mk (lucasU P Q) *
        (1 - PowerSeries.C P * PowerSeries.X + PowerSeries.C Q * PowerSeries.X ^ 2) =
      PowerSeries.X := by
  have hmk : PowerSeries.mk (lucasU P Q) =
      PowerSeries.X * PowerSeries.mk fun n ↦ (dickson 2 Q n).eval P := by
    ext (_ | n) <;> simp [lucasU_succ_eq_dickson_eval]
  rw [hmk, mul_assoc, mk_dickson_two_eval_mul_one_sub_add_eq_one, mul_one]

/-- **Generating function of `lucasV`**:
`(∑ₙ Vₙ(P, Q) Xⁿ) * (1 - P X + Q X²) = 2 - P X` in `R⟦X⟧`. -/
theorem mk_lucasV_mul_one_sub_add_eq (P Q : R) :
    PowerSeries.mk (lucasV P Q) *
        (1 - PowerSeries.C P * PowerSeries.X + PowerSeries.C Q * PowerSeries.X ^ 2) =
      2 - PowerSeries.C P * PowerSeries.X := by
  have hmk : PowerSeries.mk (lucasV P Q) =
      2 * (PowerSeries.mk fun n ↦ (dickson 2 Q n).eval P) -
        PowerSeries.C P * PowerSeries.mk (lucasU P Q) := by
    ext n
    simp [lucasV_eq_two_mul_lucasU_succ_sub, lucasU_succ_eq_dickson_eval]
  rw [hmk, sub_mul, mul_assoc, mk_dickson_two_eval_mul_one_sub_add_eq_one, mul_one, mul_assoc,
    mk_lucasU_mul_one_sub_add_eq_X]

/-! ### Order-two `LinearRecurrence` interface -/

/-- `lucasU P Q` solves the order-two linear recurrence `⟨2, ![-Q, P]⟩`. -/
theorem isSolution_lucasU (P Q : R) :
    (⟨2, ![-Q, P]⟩ : LinearRecurrence R).IsSolution (lucasU P Q) := by
  intro n
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.val_zero, Fin.val_one, add_zero, lucasU_add_two]
  ring

/-- `lucasV P Q` solves the order-two linear recurrence `⟨2, ![-Q, P]⟩`. -/
theorem isSolution_lucasV (P Q : R) :
    (⟨2, ![-Q, P]⟩ : LinearRecurrence R).IsSolution (lucasV P Q) := by
  intro n
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.val_zero, Fin.val_one, add_zero, lucasV_add_two]
  ring

/-! ### Classical parameter specializations -/

/-- At `(2, 1)` (repeated root `1`), `lucasU 2 1 n = n`. -/
@[simp]
theorem lucasU_two_one (n : ℕ) : lucasU (2 : R) 1 n = n := by
  cases n with
  | zero => simp
  | succ n =>
    simpa using lucasU_two_mul_sq_succ (1 : R) n

/-- At `(2, 1)` (repeated root `1`), `lucasV 2 1 n = 2`. -/
@[simp]
theorem lucasV_two_one (n : ℕ) : lucasV (2 : R) 1 n = 2 := by
  simpa using lucasV_two_mul_sq (1 : R) n

/-- At `(3, 2)` (roots `2` and `1`), `lucasU 3 2 n = 2 ^ n - 1`. -/
@[simp]
theorem lucasU_three_two (n : ℕ) : lucasU (3 : R) 2 n = 2 ^ n - 1 := by
  have h := lucasU_add_mul_mul_sub (2 : R) 1 n
  norm_num at h
  exact h

/-- At `(3, 2)` (roots `2` and `1`), `lucasU 3 2 n` equals the Mersenne number `mersenne n` cast
into `R`. -/
theorem lucasU_three_two_eq_mersenne (n : ℕ) : lucasU (3 : R) 2 n = mersenne n := by
  rw [lucasU_three_two, mersenne, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one]

/-- At `(3, 2)` (roots `2` and `1`), `lucasV 3 2 n = 2 ^ n + 1`. -/
@[simp]
theorem lucasV_three_two (n : ℕ) : lucasV (3 : R) 2 n = 2 ^ n + 1 := by
  have h := lucasV_add_mul (2 : R) 1 n
  norm_num at h
  exact h

/-- **Fibonacci specialization**: `lucasU 1 (-1) n = Nat.fib n` in every commutative ring. -/
@[simp]
theorem lucasU_one_neg_one (n : ℕ) : lucasU (1 : R) (-1) n = Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero | one => simp
  | more n ih₀ ih₁ =>
    rw [lucasU_add_two, ih₁, ih₀, Nat.fib_add_two, Nat.cast_add]
    ring

/-- At `(1, 1)` (primitive sixth roots of unity), `lucasU 1 1` changes sign under `n ↦ n + 3`. -/
theorem lucasU_one_one_add_three (n : ℕ) : lucasU (1 : R) 1 (n + 3) = -lucasU (1 : R) 1 n := by
  cases n with
  | zero =>
    rw [zero_add, lucasU_three, lucasU_zero]
    ring
  | succ n =>
    rw [Nat.succ_add, lucasU_succ_eq_dickson_eval, lucasU_succ_eq_dickson_eval,
      dickson_eval_one_add_three]

/-- At `(1, 1)` (primitive sixth roots of unity), `lucasV 1 1` changes sign under `n ↦ n + 3`. -/
theorem lucasV_one_one_add_three (n : ℕ) : lucasV (1 : R) 1 (n + 3) = -lucasV (1 : R) 1 n := by
  rw [lucasV_eq_dickson_eval, lucasV_eq_dickson_eval, dickson_eval_one_add_three]

/-- At `(1, 1)`, `lucasU 1 1` has period `6`. -/
@[simp]
theorem lucasU_one_one_six_mul_add (j r : ℕ) :
    lucasU (1 : R) 1 (6 * j + r) = lucasU (1 : R) 1 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h6 : 6 * (j + 1) + r = 6 * j + r + 3 + 3 := by omega
    rw [h6, lucasU_one_one_add_three, lucasU_one_one_add_three, neg_neg, ih]

/-- At `(1, 1)`, `lucasU 1 1` vanishes at multiples of `6`. -/
@[simp]
theorem lucasU_one_one_six_mul (j : ℕ) : lucasU (1 : R) 1 (6 * j) = 0 := by
  simpa using lucasU_one_one_six_mul_add (R := R) j 0

/-- At `(1, 1)`, `lucasV 1 1` has period `6`. -/
@[simp]
theorem lucasV_one_one_six_mul_add (j r : ℕ) :
    lucasV (1 : R) 1 (6 * j + r) = lucasV (1 : R) 1 r := by
  rw [lucasV_eq_dickson_eval, lucasV_eq_dickson_eval, dickson_eval_one_six_mul_add]

/-- At `(1, 1)`, `lucasV 1 1` equals `2` at multiples of `6`. -/
@[simp]
theorem lucasV_one_one_six_mul (j : ℕ) : lucasV (1 : R) 1 (6 * j) = 2 := by
  simpa using lucasV_one_one_six_mul_add (R := R) j 0

end CommRing

section Field

/-- **Quotient Binet formula for `lucasU` over a field**: when `x ≠ y`,
`lucasU (x + y) (x * y) n = (x ^ n - y ^ n) / (x - y)`. -/
theorem lucasU_add_mul_eq_div {K : Type*} [Field K] {x y : K} (hxy : x ≠ y) (n : ℕ) :
    lucasU (x + y) (x * y) n = (x ^ n - y ^ n) / (x - y) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr hxy) (lucasU_add_mul_mul_sub x y n)

end Field

section IntSpecializations

/-- Over `ℤ`, `lucasV 4 1 (2 ^ i)` is Mathlib's Lucas–Lehmer sequence `LucasLehmer.s i`. -/
theorem lucasV_four_one_two_pow (i : ℕ) : lucasV (4 : ℤ) 1 (2 ^ i) = LucasLehmer.s i := by
  induction i with
  | zero => simp [LucasLehmer.s]
  | succ i ih =>
    rw [pow_succ', lucasV_two_mul, ih, one_pow, mul_one, LucasLehmer.s]

end IntSpecializations

end TauCeti
