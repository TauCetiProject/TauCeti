/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Parity and lower bounds for rescaled Chebyshev polynomials of the second kind

Mathlib's rescaled Chebyshev polynomial of the second kind `Polynomial.Chebyshev.S R n` satisfies
`Sₙ(2) = n + 1` and `Sₙ(-2) = (-1)ⁿ (n + 1)`. Beyond the oscillatory interval `(-2, 2)`, its
values grow at least linearly: for `2 ≤ x` and `n : ℕ`, successive differences satisfy
`1 ≤ Sₙ(x) - Sₙ₋₁(x)`, whence `n + 1 ≤ Sₙ(x)`. Combined with the parity relation
`Sₙ(-x) = (-1)ⁿ Sₙ(x)`, this gives `n + 1 ≤ |Sₙ(x)|` whenever `2 ≤ |x|`.

These lower bounds rule out torsion in products of reflections whose Cartan product is at least `4`
(such as affine `A₁⁽¹⁾` and indefinite rank-two generalized Cartan matrices) and ensure positivity
of rank-two alternating words in the root lattice.

## Main results

* `Polynomial.Chebyshev.S_eval_neg`: `Sₙ(-x) = n.negOnePow * Sₙ(x)`.
* `Polynomial.Chebyshev.one_le_S_eval_sub_S_eval`: `1 ≤ Sₙ(x) - Sₙ₋₁(x)` for `2 ≤ x` and `n : ℕ`.
* `Polynomial.Chebyshev.natCast_add_one_le_S_eval`: `n + 1 ≤ Sₙ(x)` for `2 ≤ x` and `n : ℕ`.
* `Polynomial.Chebyshev.natCast_add_one_le_abs_S_eval`: `n + 1 ≤ |Sₙ(x)|` for `2 ≤ |x|` and
  `n : ℕ`.
-/

public section

namespace Polynomial.Chebyshev

section CommRing

variable {R : Type*} [CommRing R]

/-- **Parity of `Sₙ`.** Evaluating `Sₙ` at `-x` multiplies its value at `x` by `(-1)ⁿ`. -/
theorem S_eval_neg (n : ℤ) (x : R) :
    (S R n).eval (-x) = (n.negOnePow : R) * (S R n).eval x := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h2 : (Int.negOnePow 2 : ℤ) = 1 := by decide
    simp only [S_add_two, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, ih1, ih2,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_mul, Units.val_neg, Units.val_one, h2,
      Int.cast_mul, Int.cast_neg, Int.cast_one]
    ring
  | neg_add_one n ih1 ih2 =>
    have hsub : (-↑n - 1 : ℤ) = -↑n + 1 - 2 := by omega
    have hsub1 : (-↑n + 1 - 1 : ℤ) = -↑n := by omega
    have hpow : (-(n : ℤ) - 1).negOnePow = -(n : ℤ).negOnePow := by
      rw [← Int.negOnePow_neg, neg_sub, sub_neg_eq_add, add_comm, Int.negOnePow_succ]
    rw [hpow, hsub, S_sub_two]
    simp only [hsub1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, ih1, ih2,
      Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one, Units.val_mul, Units.val_neg,
      Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one]
    ring

end CommRing

section Ordered

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

private theorem natCast_le_and_one_le_S_eval_sub {x : R} (hx : 2 ≤ x) (n : ℕ) :
    (n : R) ≤ (S R ((n : ℤ) - 1)).eval x ∧
      1 ≤ (S R n).eval x - (S R ((n : ℤ) - 1)).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : ((n + 1 : ℕ) : R) ≤ (S R n).eval x := by
      push_cast
      have hsum := add_le_add ih.1 ih.2
      rwa [add_sub_cancel] at hsum
    refine ⟨?_, ?_⟩
    · simpa using hn1
    · have hrec : (S R ((n + 1 : ℕ) : ℤ)).eval x - (S R n).eval x =
          (x - 2) * (S R n).eval x + ((S R n).eval x - (S R ((n : ℤ) - 1)).eval x) := by
        push_cast
        rw [S_add_one]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
        ring
      have h0 : (0 : R) ≤ x - 2 := sub_nonneg.mpr hx
      have hS0 : (0 : R) ≤ (S R n).eval x := (Nat.cast_nonneg (n + 1)).trans hn1
      have hidx : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
      rw [hidx, hrec]
      exact le_add_of_nonneg_of_le (mul_nonneg h0 hS0) ih.2

/-- For `2 ≤ x`, successive natural-indexed Chebyshev `S`-values grow by at least `1`. -/
theorem one_le_S_eval_sub_S_eval {x : R} (hx : 2 ≤ x) (n : ℕ) :
    1 ≤ (S R n).eval x - (S R ((n : ℤ) - 1)).eval x :=
  (natCast_le_and_one_le_S_eval_sub hx n).2

/-- **Linear lower bound on `[2, ∞)`.** For `2 ≤ x` and `n : ℕ`, `n + 1 ≤ Sₙ(x)`. -/
theorem natCast_add_one_le_S_eval {x : R} (hx : 2 ≤ x) (n : ℕ) :
    (n : R) + 1 ≤ (S R n).eval x := by
  simpa using (natCast_le_and_one_le_S_eval_sub hx (n + 1)).1

/-- For `2 ≤ x` and `n : ℕ`, `Sₙ(x)` is nonnegative. -/
theorem S_eval_nonneg {x : R} (hx : 2 ≤ x) (n : ℕ) :
    0 ≤ (S R n).eval x :=
  (add_nonneg (Nat.cast_nonneg n) zero_le_one).trans (natCast_add_one_le_S_eval hx n)

end Ordered

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **Linear lower bound outside `(-2, 2)`.** For `2 ≤ |x|` and `n : ℕ`, `n + 1 ≤ |Sₙ(x)|`. -/
theorem natCast_add_one_le_abs_S_eval {x : R} (hx : 2 ≤ |x|) (n : ℕ) :
    (n : R) + 1 ≤ |(S R n).eval x| := by
  rcases le_abs.mp hx with hx' | hx'
  · exact (natCast_add_one_le_S_eval hx' n).trans (le_abs_self _)
  · have hneg := natCast_add_one_le_S_eval hx' n
    rw [S_eval_neg] at hneg
    rcases Int.units_eq_one_or (n : ℤ).negOnePow with hp | hp
    · rw [hp, Units.val_one, Int.cast_one, one_mul] at hneg
      exact hneg.trans (le_abs_self _)
    · rw [hp, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hneg
      exact hneg.trans (neg_le_abs _)

end LinearOrder

end Polynomial.Chebyshev
