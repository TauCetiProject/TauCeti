/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Positivity and monotonicity of rescaled Chebyshev polynomials for `t ≥ 2`

Mathlib's rescaled Chebyshev polynomials of the second kind `Polynomial.Chebyshev.S R n` satisfy
the recurrence `S_{n+2}(t) = t · S_{n+1}(t) - S_n(t)` with `S_{-1}(t) = 0`, `S_0(t) = 1`, and
`S_1(t) = t`. At `t = 2`, `(S R n).eval 2 = n + 1` (`Polynomial.Chebyshev.S_eval_two`).

Over any ordered commutative ring `R`, for every `t ≥ 2`, the increments `S_{n+1}(t) - S_n(t)` are
at least `1` for all `n : ℕ`. Consequently:

* `(S R n).eval t + 1 ≤ (S R (n + 1 : ℕ)).eval t`;
* `(n : R) + 1 ≤ (S R n).eval t` (sharp at `t = 2`), and in particular `1 ≤ (S R n).eval t`;
* `n ↦ (S R n).eval t` is monotone on `ℕ` (and strictly monotone whenever `R` is nontrivial);
* `0 ≤ (S R ((n : ℤ) - 1)).eval t` for all `n : ℕ`.

## Main results

* `Polynomial.Chebyshev.S_eval_add_one_le_S_eval_succ`: step lower bound
  `(S R n).eval t + 1 ≤ (S R (n + 1 : ℕ)).eval t` for `2 ≤ t`.
* `Polynomial.Chebyshev.natCast_add_one_le_S_eval`: sharp linear lower bound
  `(n : R) + 1 ≤ (S R n).eval t` for `2 ≤ t`.
* `Polynomial.Chebyshev.one_le_S_eval`: positivity `1 ≤ (S R n).eval t` for `2 ≤ t`.
* `Polynomial.Chebyshev.monotone_S_eval`, `Polynomial.Chebyshev.strictMono_S_eval`: monotonicity
  and strict monotonicity of `n ↦ (S R n).eval t` on `ℕ` for `2 ≤ t`.
* `Polynomial.Chebyshev.nonneg_S_eval_sub_one`: nonnegativity `0 ≤ (S R ((n : ℤ) - 1)).eval t` for
  all `n : ℕ` and `2 ≤ t`.
-/

public section

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

private theorem one_le_S_eval_and_step {t : R} (ht : 2 ≤ t) :
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

/-- For `t ≥ 2`, consecutive evaluations of `S R n` at `t` increase by at least `1`. -/
theorem S_eval_add_one_le_S_eval_succ {t : R} (ht : 2 ≤ t) (n : ℕ) :
    (S R n).eval t + 1 ≤ (S R (n + 1 : ℕ)).eval t :=
  (one_le_S_eval_and_step ht n).2

/-- For `t ≥ 2`, `(S R n).eval t` is at least `n + 1` (attained with equality at `t = 2`). -/
theorem natCast_add_one_le_S_eval {t : R} (ht : 2 ≤ t) :
    ∀ n : ℕ, (n : R) + 1 ≤ (S R n).eval t
  | 0 => by simp
  | n + 1 => by
    have ih := natCast_add_one_le_S_eval ht n
    push_cast
    exact le_trans (add_le_add_left ih 1) (S_eval_add_one_le_S_eval_succ ht n)

/-- For `t ≥ 2` and `n : ℕ`, `(S R n).eval t ≥ 1`. -/
theorem one_le_S_eval {t : R} (ht : 2 ≤ t) (n : ℕ) : 1 ≤ (S R n).eval t :=
  (one_le_S_eval_and_step ht n).1

/-- For `t ≥ 2`, `n ↦ (S R n).eval t` is monotone on `ℕ`. -/
theorem monotone_S_eval {t : R} (ht : 2 ≤ t) : Monotone fun n : ℕ ↦ (S R n).eval t :=
  monotone_nat_of_le_succ fun n ↦
    le_trans (le_add_of_nonneg_right zero_le_one) (S_eval_add_one_le_S_eval_succ ht n)

/-- For `t ≥ 2` in a nontrivial ordered commutative ring, `n ↦ (S R n).eval t` is strictly
monotone on `ℕ`. -/
theorem strictMono_S_eval [Nontrivial R] {t : R} (ht : 2 ≤ t) :
    StrictMono fun n : ℕ ↦ (S R n).eval t :=
  strictMono_nat_of_lt_succ fun n ↦
    lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) (S_eval_add_one_le_S_eval_succ ht n)

/-- For `t ≥ 2` and every `n : ℕ`, `(S R (n - 1)).eval t` is nonnegative (vanishing at `n = 0`
and at least `1` for `n ≥ 1`). -/
theorem nonneg_S_eval_sub_one {t : R} (ht : 2 ≤ t) :
    ∀ n : ℕ, 0 ≤ (S R ((n : ℤ) - 1)).eval t
  | 0 => by simp
  | n + 1 => by
    have h := one_le_S_eval ht n
    simpa [Nat.cast_add, add_sub_cancel_right] using le_trans zero_le_one h

end Polynomial.Chebyshev
