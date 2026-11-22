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
increase by at least `1` at each step, so `n + 1 ≤ Sₙ(t)`. In particular `1 ≤ Sₙ(t)`, the map
`n ↦ Sₙ(t)` is monotone (strictly so in a nontrivial ring), and `0 ≤ Sₙ₋₁(t)` for all `n ≥ 0`.

The values `Sₙ(t)` are the coefficients of the powers of a product of two reflections whose
Cartan product is `t + 2`. For `t ≥ 2` the product is a shear or a hyperbolic transformation,
and the growth proved here shows that it has infinite order. The file also records the value
`S₃(1) = -1`, which rules out the order `3` for Cartan product `3`, and the value of `Sₙ` at the
image of an integer, which transports the growth bound from `ℤ` to any ring.

## Main results

* `Polynomial.Chebyshev.S_eval_add_one_le`: `Sₙ(t) + 1 ≤ Sₙ₊₁(t)` for `t ≥ 2` and `n ≥ 0`.
* `Polynomial.Chebyshev.natCast_add_one_le_S_eval`: `n + 1 ≤ Sₙ(t)` for `t ≥ 2` and `n ≥ 0`.
* `Polynomial.Chebyshev.one_le_S_eval`, `Polynomial.Chebyshev.nonneg_S_eval_sub_one`: `1 ≤ Sₙ(t)`
  and `0 ≤ Sₙ₋₁(t)` for `t ≥ 2` and `n ≥ 0`.
* `Polynomial.Chebyshev.monotone_S_eval`, `Polynomial.Chebyshev.strictMono_S_eval`: `n ↦ Sₙ(t)` is
  monotone, and strictly monotone in a nontrivial ring, for `t ≥ 2`.
* `Polynomial.Chebyshev.S_eval_add_S_sub_one_eval_strictMono`: the sum of adjacent values
  `Sₙ(t) + Sₙ₋₁(t)` grows strictly for `t ≥ 2` in a nontrivial ordered commutative ring.
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

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] {t : R}

/-- Positivity and the unit step at once, so that the induction can use the positivity of
`Sₙ(t)`. -/
private theorem one_le_S_eval_and_step (ht : 2 ≤ t) :
    ∀ n : ℕ, 1 ≤ (S R n).eval t ∧ (S R n).eval t + 1 ≤ (S R (n + 1 : ℕ)).eval t
  | 0 => by
    refine ⟨by simp, ?_⟩
    simpa [one_add_one_eq_two] using ht
  | n + 1 => by
    obtain ⟨h1, hstep⟩ := one_le_S_eval_and_step ht n
    have h1' : 1 ≤ (S R (n + 1 : ℕ)).eval t :=
      le_trans h1 (le_trans (le_add_of_nonneg_right zero_le_one) hstep)
    have hnonneg : 0 ≤ (S R (n + 1 : ℕ)).eval t := le_trans zero_le_one h1'
    have hrec : (S R (n + 2 : ℕ)).eval t =
        t * (S R (n + 1 : ℕ)).eval t - (S R n).eval t := by
      have hcast : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast, S_add_two, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, hcast1]
    -- `Sₙ₊₂(t) = t Sₙ₊₁(t) - Sₙ(t) ≥ 2 Sₙ₊₁(t) - Sₙ(t)`, since `Sₙ₊₁(t) ≥ 0`.
    have hmul : 2 * (S R (n + 1 : ℕ)).eval t ≤ t * (S R (n + 1 : ℕ)).eval t :=
      mul_le_mul_of_nonneg_right ht hnonneg
    have hstep' : (S R (n + 1 : ℕ)).eval t + 1 ≤ (S R (n + 2 : ℕ)).eval t := by
      rw [hrec]
      have hsub : (S R (n + 1 : ℕ)).eval t + 1 ≤
          2 * (S R (n + 1 : ℕ)).eval t - (S R n).eval t := by
        rw [two_mul, add_sub_assoc]
        exact add_le_add_right (le_sub_iff_add_le'.mpr hstep) _
      exact le_trans hsub (sub_le_sub_right hmul _)
    exact ⟨h1', hstep'⟩

/-- At a point `t ≥ 2` the values `Sₙ(t)` increase by at least `1` at each step. -/
theorem S_eval_add_one_le (ht : 2 ≤ t) (n : ℕ) :
    (S R n).eval t + 1 ≤ (S R (n + 1)).eval t := by
  simpa using (one_le_S_eval_and_step ht n).2

/-- At a point `t ≥ 2` the value `Sₙ(t)` is at least its value `n + 1` at `2`. -/
theorem natCast_add_one_le_S_eval (ht : 2 ≤ t) : ∀ n : ℕ, (n + 1 : R) ≤ (S R n).eval t
  | 0 => by simp
  | n + 1 => by
    have ih := natCast_add_one_le_S_eval ht n
    push_cast
    exact le_trans (add_le_add_left ih 1) (S_eval_add_one_le ht n)

/-- At a point `t ≥ 2` every value `Sₙ(t)`, `n ≥ 0`, is at least `1`. -/
theorem one_le_S_eval (ht : 2 ≤ t) (n : ℕ) : 1 ≤ (S R n).eval t :=
  (one_le_S_eval_and_step ht n).1

/-- At a point `t ≥ 2`, `n ↦ Sₙ(t)` is monotone on `ℕ`. -/
theorem monotone_S_eval (ht : 2 ≤ t) : Monotone fun n : ℕ ↦ (S R n).eval t :=
  monotone_nat_of_le_succ fun n ↦
    le_trans (le_add_of_nonneg_right zero_le_one) (one_le_S_eval_and_step ht n).2

/-- At a point `t ≥ 2` of a nontrivial ordered commutative ring, `n ↦ Sₙ(t)` is strictly monotone
on `ℕ`. -/
theorem strictMono_S_eval [Nontrivial R] (ht : 2 ≤ t) : StrictMono fun n : ℕ ↦ (S R n).eval t :=
  strictMono_nat_of_lt_succ fun n ↦
    lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) (one_le_S_eval_and_step ht n).2

/-- At a point `t ≥ 2` every value `Sₙ₋₁(t)`, `n ≥ 0`, is nonnegative: it vanishes at `n = 0` and
is at least `1` for `n ≥ 1`. -/
theorem nonneg_S_eval_sub_one (ht : 2 ≤ t) : ∀ n : ℕ, 0 ≤ (S R ((n : ℤ) - 1)).eval t
  | 0 => by simp
  | n + 1 => by
    simpa [Nat.cast_add, add_sub_cancel_right] using le_trans zero_le_one (one_le_S_eval ht n)

/-- At `t ≥ 2` in a nontrivial ordered commutative ring, the sum of the rescaled Chebyshev
values at indices `n` and `(n : ℤ) - 1` is strictly increasing in the natural index `n`. -/
theorem S_eval_add_S_sub_one_eval_strictMono [Nontrivial R] (ht : 2 ≤ t) :
    StrictMono fun n : ℕ ↦ (S R (n : ℤ)).eval t + (S R ((n : ℤ) - 1)).eval t := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hlt := strictMono_S_eval ht (Nat.lt_succ_self n)
  have hprev : (S R ((n : ℤ) - 1)).eval t ≤ (S R (((n + 1 : ℕ) : ℤ) - 1)).eval t := by
    cases n with
    | zero => simp [S_neg_one, S_zero]
    | succ n =>
      simpa only [Nat.cast_succ, add_sub_cancel_right] using
        monotone_S_eval ht (Nat.le_succ n)
  exact add_lt_add_of_lt_of_le hlt hprev

end Polynomial.Chebyshev
