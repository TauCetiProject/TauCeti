/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.NumberTheory.Padics.Basic

/-!
# `p`-adic estimates for binomial coefficients

In a normed `ℚ_p`-algebra `K` the binomial coefficient `C(N - 1, j) = ∏_{1 ≤ i ≤ j} (N - i) / i` is
close to `(-1)ʲ` when `N` is `p`-adically small:

`‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖`

(`TauCeti.norm_natCast_choose_pred_sub_neg_one_pow_le`). Dividing by `j + 1`, the coefficient
`C(N, j + 1) / N` of `t ^ (j + 1)` in `((1 + t) ^ N - 1) / N` is within `(j + 1)² ‖N‖` of the
coefficient `(-1)ʲ / (j + 1)` of `log (1 + t)` (`TauCeti.norm_natCast_choose_succ_div_sub_le`).
This is the coefficient estimate behind `log (1 + t) = lim ((1 + t) ^ (p ^ m) - 1) / p ^ m`.

The induction uses the recursion `C(n, k) (n - k) = (k + 1) C(n, k + 1)`, cast to an arbitrary ring
(`Nat.cast_choose_mul_sub`).

## Main results

* `TauCeti.norm_natCast_choose_pred_sub_neg_one_pow_le`: `‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖`.
* `TauCeti.norm_natCast_choose_succ_div_sub_le`:
  `‖C(N, j + 1) / N - (-1)ʲ / (j + 1)‖ ≤ (j + 1)² ‖N‖`.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- **`C(N - 1, j)` is `p`-adically close to `(-1)ʲ`.** In a normed `ℚ_p`-algebra the binomial
coefficient `C(N - 1, j) = ∏_{1 ≤ i ≤ j} (N - i) / i` satisfies the norm bound
`‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖`, where the factor `j + 1` is a real number, not a norm. -/
theorem norm_natCast_choose_pred_sub_neg_one_pow_le (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] {N : ℕ} (hN : N ≠ 0) (j : ℕ) :
    ‖((N - 1).choose j : K) - (-1) ^ j‖ ≤ (j + 1) * ‖(N : K)‖ := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : ((j + 1 : ℕ) : K) ≠ 0 := (isUnit_natCast_of_ne_zero ℚ_[p] j.succ_ne_zero).ne_zero
    set x : K := N / (j + 1 : ℕ) with hx_def
    -- The recursion `C(N - 1, j + 1) = -C(N - 1, j) (1 - N / (j + 1))`.
    have hrec : ((N - 1).choose (j + 1) : K) = -((N - 1).choose j : K) * (1 - x) := by
      have h' := Nat.cast_choose_mul_sub (R := K) (N - 1) j
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hN), Nat.cast_one] at h'
      rw [hx_def]
      push_cast at hj ⊢
      field_simp
      linear_combination -h'
    by_cases hbig : 1 ≤ (j + 1 + 1) * ‖(N : K)‖
    · -- Both terms are integers, so the difference has norm at most `1`.
      have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) + 1) * ‖(N : K)‖ := by push_cast; linarith
      refine (IsUltrametricDist.norm_sub_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_natCast_le_one K _).trans h1) ?_)
      simpa using h1
    · push Not at hbig
      have hx : ‖x‖ ≤ (j + 1) * ‖(N : K)‖ := by
        rw [hx_def, div_eq_mul_inv, norm_mul, mul_comm]
        gcongr
        exact_mod_cast norm_inv_natCast_le p (j + 1)
      have hx1 : ‖1 - x‖ ≤ 1 :=
        (IsUltrametricDist.norm_sub_le_max _ _).trans
          (max_le norm_one.le (hx.trans (by nlinarith [norm_nonneg (N : K)])))
      have hsplit : ((N - 1).choose (j + 1) : K) - (-1) ^ (j + 1) =
          -((((N - 1).choose j : K) - (-1) ^ j) * (1 - x) - (-1) ^ j * x) := by
        rw [hrec]
        ring
      rw [hsplit, norm_neg]
      refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc _ ≤ ((j + 1) * ‖(N : K)‖) * 1 :=
              mul_le_mul ih hx1 (norm_nonneg _) (by positivity)
          _ ≤ _ := by push_cast; nlinarith [norm_nonneg (N : K)]
      · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        refine hx.trans ?_
        push_cast
        nlinarith [norm_nonneg (N : K)]

/-- **The coefficients of `((1 + t) ^ N - 1) / N` approximate those of `log (1 + t)`.** In a normed
`ℚ_p`-algebra, `‖C(N, j + 1) / N - (-1)ʲ / (j + 1)‖ ≤ (j + 1)² ‖N‖`. -/
theorem norm_natCast_choose_succ_div_sub_le (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K] {N : ℕ}
    (hN : N ≠ 0) (j : ℕ) :
    ‖(N.choose (j + 1) : K) / N - (-1) ^ j / (j + 1)‖ ≤ (j + 1) ^ 2 * ‖(N : K)‖ := by
  have hN' : (N : K) ≠ 0 := (isUnit_natCast_of_ne_zero ℚ_[p] hN).ne_zero
  have hj : ((j + 1 : ℕ) : K) ≠ 0 := (isUnit_natCast_of_ne_zero ℚ_[p] j.succ_ne_zero).ne_zero
  -- `C(N, j + 1) / N = C(N - 1, j) / (j + 1)`.
  have hsucc := congrArg (Nat.cast : ℕ → K) (Nat.add_one_mul_choose_eq (N - 1) j)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN)] at hsucc
  push_cast at hsucc hj
  have heq : (N.choose (j + 1) : K) / N - (-1) ^ j / (j + 1) =
      (((N - 1).choose j : K) - (-1) ^ j) * ((j + 1 : ℕ) : K)⁻¹ := by
    push_cast
    field_simp
    linear_combination -hsucc
  rw [heq, norm_mul]
  calc _ ≤ ((j + 1) * ‖(N : K)‖) * (j + 1 : ℕ) :=
        mul_le_mul (norm_natCast_choose_pred_sub_neg_one_pow_le p hN j)
          (norm_inv_natCast_le p _) (norm_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

end TauCeti
