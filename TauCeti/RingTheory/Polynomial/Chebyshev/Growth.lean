/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Growth of the rescaled Chebyshev polynomials of the second kind from `2` on

Mathlib's rescaled Chebyshev polynomials of the second kind `Polynomial.Chebyshev.S R n` take the
value `n + 1` at `2` (`Polynomial.Chebyshev.S_eval_two`). This file shows that at every point
`t ≥ 2` of an ordered commutative ring they grow at least as fast: the values `Sₙ(t)`, `n ≥ 0`,
increase by at least `1` at each step, so `n + 1 ≤ Sₙ(t)`.

The values `Sₙ(t)` are the coefficients of the powers of a product of two reflections whose
Cartan product is `t + 2`. For `t ≥ 2` the product is a shear or a hyperbolic transformation,
and the growth proved here shows that it has infinite order. The file also records the value
`S₃(1) = -1`, which rules out the order `3` for Cartan product `3`, and the value of `Sₙ` at the
image of an integer, which transports the growth bound from `ℤ` to any ring.

## Main results

* `Polynomial.Chebyshev.S_eval_add_one_le`: `Sₙ(t) + 1 ≤ Sₙ₊₁(t)` for `t ≥ 2` and `n ≥ 0`.
* `Polynomial.Chebyshev.natCast_add_one_le_S_eval`: `n + 1 ≤ Sₙ(t)` for `t ≥ 2` and `n ≥ 0`.
* `Polynomial.Chebyshev.S_three_eval_one`: `S₃(1) = -1`.
* `Polynomial.Chebyshev.S_eval_intCast`: `Sₙ` over `R` at the image of an integer `c` is the image
  of `Sₙ` over `ℤ` at `c`.
-/

public section

namespace Polynomial.Chebyshev

/-- `S₃(1) = -1`: at `t = 1` the values `Sₙ(t)` run through `1, 1, 0, -1`. -/
theorem S_three_eval_one (R : Type*) [CommRing R] : (S R 3).eval (1 : R) = -1 := by
  have h : S R (3 : ℤ) = X * S R 2 - S R 1 := by simpa using S_add_two R (1 : ℤ)
  simp [h, S_one, S_two]

/-- The value of `Sₙ` over `R` at the image of an integer `c` is the image of its value over `ℤ`
at `c`. -/
theorem S_eval_intCast (R : Type*) [CommRing R] (n c : ℤ) :
    (S R n).eval (c : R) = (((S ℤ n).eval c : ℤ) : R) := by
  rw [← map_S (Int.castRingHom R), eval_intCast_map, eq_intCast, Int.cast_id]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {t : R}

/-- Both growth statements at once, so that the induction can use the positivity of `Sₙ(t)`. -/
private theorem S_eval_add_one_le_and (ht : 2 ≤ t) (n : ℕ) :
    (S R n).eval t + 1 ≤ (S R (n + 1)).eval t ∧ (n + 1 : R) ≤ (S R n).eval t := by
  induction n with
  | zero => simp [S_zero, S_one]; linarith
  | succ n ih =>
    obtain ⟨h₁, h₂⟩ := ih
    have hrec : (S R ((n + 1 : ℕ) + 1)).eval t =
        t * (S R ((n + 1 : ℕ) : ℤ)).eval t - (S R n).eval t := by
      have := S_add_two R (n : ℤ)
      push_cast at this ⊢
      rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, this]
      simp
    push_cast at hrec ⊢
    -- `Sₙ₊₂(t) = t Sₙ₊₁(t) - Sₙ(t) ≥ 2 Sₙ₊₁(t) - Sₙ(t)`, since `Sₙ₊₁(t) ≥ 0`.
    have hpos : 0 ≤ (S R ((n : ℤ) + 1)).eval t := by
      have : (0 : R) ≤ n := Nat.cast_nonneg n
      linarith
    have hmul : 2 * (S R ((n : ℤ) + 1)).eval t ≤ t * (S R ((n : ℤ) + 1)).eval t :=
      mul_le_mul_of_nonneg_right ht hpos
    constructor <;> linarith

/-- At a point `t ≥ 2` the values `Sₙ(t)` increase by at least `1` at each step. -/
theorem S_eval_add_one_le (ht : 2 ≤ t) (n : ℕ) :
    (S R n).eval t + 1 ≤ (S R (n + 1)).eval t :=
  (S_eval_add_one_le_and ht n).1

/-- At a point `t ≥ 2` the value `Sₙ(t)` is at least its value `n + 1` at `2`. -/
theorem natCast_add_one_le_S_eval (ht : 2 ≤ t) (n : ℕ) :
    (n + 1 : R) ≤ (S R n).eval t :=
  (S_eval_add_one_le_and ht n).2

end Polynomial.Chebyshev
