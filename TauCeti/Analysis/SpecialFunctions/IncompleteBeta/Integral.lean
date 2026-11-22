/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The quadratic transformation and the negative binomial series of the incomplete Beta function

The incomplete Beta function `B_x(a, b)` of `TauCeti.incompleteBeta` is the unnormalized integral
`∫ t in 0..x, t ^ (a - 1) * (1 - t) ^ (b - 1)` ([DLMF 8.17.1](https://dlmf.nist.gov/8.17.E1)),
and the regularized incomplete Beta function `I_x(a, b)` of `TauCeti.regularizedIncompleteBeta`
is `B_x(a, b) / Β(a, b)` for `a, b > 0` and `0 ≤ x ≤ 1`. This file proves two closed forms.

The substitution `u = 4 t (1 - t)` is increasing on `t ≤ 1/2`, maps `[0, 1/2]` onto `[0, 1]`, and
turns the symmetric integrand `t ^ (a - 1) * (1 - t) ^ (a - 1)` into a multiple of the integrand
with parameters `a` and `1/2`. This gives the quadratic transformation
`I_x(a, a) = I_{4x(1-x)}(a, 1/2) / 2` for `a > 0` and `x ≤ 1/2`; for `a < 0` both sides are `0`.

At natural parameters the unit-step recurrence in the first parameter peels one negative binomial
weight off `I_x(m, n)` at a time, and the negative binomial series of `(1 - x) ^ (-n)` sums all of
them to `1`. Together they give `I_x(m, n) = (1 - x) ^ n * ∑_{j ≥ m} (n + j - 1).choose j * x ^ j`
for `n > 0` and `0 ≤ x < 1`.

## Main results

* `TauCeti.incompleteBeta_one_half_four_mul_mul_one_sub`: the substitution
  `B_{4x(1-x)}(a, 1/2) = 4 ^ a * B_x(a, a)` for `x ≤ 1/2`, for every `a`;
* `TauCeti.regularizedIncompleteBeta_self_eq_regularizedIncompleteBeta_one_half_div_two`: the
  quadratic transformation, [DLMF 8.17.6](https://dlmf.nist.gov/8.17.E6), for `a ≠ 0` and
  `x ≤ 1/2`;
* `TauCeti.regularizedIncompleteBeta_natCast_eq_one_sub_sum_range`: the finite form
  `I_x(m, n) = 1 - (1 - x) ^ n * ∑_{j < m} (n + j - 1).choose j * x ^ j` for natural `m` and `n`,
  not both `0`, and `0 ≤ x ≤ 1`;
* `TauCeti.hasSum_choose_mul_pow_regularizedIncompleteBeta`: the negative binomial series,
  [DLMF 8.17.24](https://dlmf.nist.gov/8.17.E24), for natural `m` and `n`, not both `0`, and
  `0 ≤ x < 1`.

The quadratic substitution is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/IncompleteGamma/Beta.lean`.

## References

* [NIST Digital Library of Mathematical Functions, §8.17](https://dlmf.nist.gov/8.17).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Nat

namespace TauCeti

variable {a b x : ℝ}

/-! ## The quadratic transformation -/

/-- The pointwise form of the substitution `u = 4 t (1 - t)`: for `t < 1/2` the integrand with
parameters `a` and `1/2` at `u`, times `du/dt = 4 (1 - 2 t)`, is `4 ^ a` times the symmetric
integrand at `t`. -/
private lemma rpow_mul_one_sub_rpow_four_mul_mul_one_sub {t : ℝ} (ht1 : t < 1 / 2) :
    (4 * t * (1 - t)) ^ (a - 1) * (1 - 4 * t * (1 - t)) ^ ((1 / 2 : ℝ) - 1) * (4 * (1 - 2 * t)) =
      4 ^ a * (t ^ (a - 1) * (1 - t) ^ (a - 1)) := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - 2 * t := by linarith
  have h2' : 1 - t * 2 ≠ 0 := by linarith
  have hprod : (4 * t * (1 - t)) ^ (a - 1) = 4 ^ (a - 1) * (t ^ (a - 1) * (1 - t) ^ (a - 1)) := by
    rw [mul_comm _ (1 - t), Real.mul_rpow_of_nonneg_left h1.le,
      Real.mul_rpow_of_nonneg_left (by norm_num)]
    ring
  have hsq : 1 - 4 * t * (1 - t) = (1 - 2 * t) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    ring
  rw [hprod, hsq, ← Real.rpow_mul h2.le, Real.rpow_sub_one four_ne_zero]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- The substitution `u = 4 t (1 - t)` on `[0, x]`, for `x ≤ 1/2`:
`B_{4x(1-x)}(a, 1/2) = 4 ^ a * B_x(a, a)`. It holds for every `a`; where the integrals diverge
both sides are `0`. -/
theorem incompleteBeta_one_half_four_mul_mul_one_sub (hx : x ≤ 1 / 2) :
    incompleteBeta a (1 / 2) (4 * x * (1 - x)) = 4 ^ a * incompleteBeta a a x := by
  have hmax : max 0 x ≤ 1 / 2 := max_le (by norm_num) hx
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := x)
    (f := fun t => 4 * t * (1 - t)) (f' := fun t => 4 * (1 - 2 * t))
    (g := fun u => u ^ (a - 1) * (1 - u) ^ ((1 / 2 : ℝ) - 1)) (by fun_prop)
    (fun t _ => (((hasDerivAt_id' t).const_mul 4).mul
      ((hasDerivAt_id' t).const_sub 1)).congr_deriv (by ring))
    (fun t ht => by linarith [ht.2])
  simp only [mul_zero, zero_mul] at hsub
  rw [incompleteBeta_def, incompleteBeta_def, ← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  exact rpow_mul_one_sub_rpow_four_mul_mul_one_sub
    (lt_of_lt_of_le (by simpa [uIoo] using ht.2) hmax)

/-- The quadratic transformation of the symmetric regularized incomplete Beta function,
`I_x(a, a) = I_{4x(1-x)}(a, 1/2) / 2` for `a ≠ 0` and `x ≤ 1/2`
([DLMF 8.17.6](https://dlmf.nist.gov/8.17.E6)). DLMF states it for `a > 0` and `0 ≤ x ≤ 1/2`;
for `a < 0` both sides are `0` by the default value, and for `x < 0` both sides are `0` because
`4x(1-x) < 0` too. -/
theorem regularizedIncompleteBeta_self_eq_regularizedIncompleteBeta_one_half_div_two
    (ha : a ≠ 0) (hx1 : x ≤ 1 / 2) :
    regularizedIncompleteBeta a a x =
      regularizedIncompleteBeta a (1 / 2) (4 * x * (1 - x)) / 2 := by
  rcases ha.lt_or_gt with ha | ha
  · rw [regularizedIncompleteBeta_eq_zero_of_neg_left ha,
      regularizedIncompleteBeta_eq_zero_of_neg_left ha, zero_div]
  rcases lt_or_ge x 0 with hx | hx0
  · have hy : 4 * x * (1 - x) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx,
      regularizedIncompleteBeta_eq_zero_of_neg _ _ hy, zero_div]
  have hy : 4 * x * (1 - x) ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  rw [regularizedIncompleteBeta_def_of_mem_Icc ha ha ⟨hx0, by linarith⟩,
    regularizedIncompleteBeta_def_of_mem_Icc ha hh hy, ← incompleteBeta_def,
    ← incompleteBeta_def, incompleteBeta_one_half_four_mul_mul_one_sub hx1,
    beta_comm a (1 / 2), beta_one_half_left_eq_two_rpow_mul_beta_self]
  have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a - 1) * 2 := by
    rw [← Real.rpow_add_one two_ne_zero, sub_add_cancel, Real.rpow_mul zero_le_two]
    norm_num
  have hB := (beta_pos ha ha).ne'
  have h2 : (2 : ℝ) ^ (2 * a - 1) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  rw [h4]
  field_simp

/-! ## The negative binomial series -/

/-- At natural parameters `m` and `n`, not both `0`, the regularized incomplete Beta function is
one minus the first `m` negative binomial weights:
`I_x(m, n) = 1 - (1 - x) ^ n * ∑_{j < m} (n + j - 1).choose j * x ^ j` for `0 ≤ x ≤ 1`. At
`m = 0` this is the boundary value `I_x(0, n) = 1`, and at `n = 0` both sides are `0`. -/
theorem regularizedIncompleteBeta_natCast_eq_one_sub_sum_range {m n : ℕ} (h : 0 < m ∨ 0 < n)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta m n x =
      1 - ∑ j ∈ Finset.range m, (1 - x) ^ n * ((n + j - 1).choose j : ℝ) * x ^ j := by
  rcases n.eq_zero_or_pos with rfl | hn
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.cast_zero, regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl,
      Finset.sum_range_succ']
    simp
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    rw [Nat.cast_zero, regularizedIncompleteBeta_zero_left (by positivity) hx0]
    simp
  | succ m ih =>
    rcases m.eq_zero_or_pos with rfl | hm
    · rw [Nat.cast_one, regularizedIncompleteBeta_one_left (by positivity) hx0 hx1,
        Real.rpow_natCast]
      simp
    have hstep := regularizedIncompleteBeta_add_one_left (a := m) (b := (k + 1 : ℕ)) (x := x)
      (by positivity) (by positivity) hx0 hx1
    rw [Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv,
      natCast_mul_beta_natCast_inv_eq_choose hm] at hstep
    rw [Nat.cast_succ, hstep, ih (Or.inl hm), Finset.sum_range_succ]
    ring

/-- The negative binomial series for the regularized incomplete Beta function at natural
parameters, `I_x(m, n) = (1 - x) ^ n * ∑_{j ≥ m} (n + j - 1).choose j * x ^ j` for `m` and `n`
not both `0` and `0 ≤ x < 1` ([DLMF 8.17.24](https://dlmf.nist.gov/8.17.E24)), with the
summation index shifted to start at `0`. DLMF states it for `m, n > 0`; at `m = 0` it is the
negative binomial series of `(1 - x) ^ (-n)` together with the boundary value `I_x(0, n) = 1`,
and at `n = 0` every term and the sum are `0`. -/
theorem hasSum_choose_mul_pow_regularizedIncompleteBeta {m n : ℕ} (h : 0 < m ∨ 0 < n)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j => (1 - x) ^ n * ((n + (j + m) - 1).choose (j + m) : ℝ) * x ^ (j + m))
      (regularizedIncompleteBeta m n x) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have hm := h.resolve_right (lt_irrefl 0)
    rw [Nat.cast_zero, regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl]
    convert hasSum_zero with j
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
  -- Remove the finite prefix of `regularizedIncompleteBeta_natCast_eq_one_sub_sum_range` from
  -- Mathlib's full negative binomial series `hasSum_choose_mul_geometric_of_norm_lt_one`.
  rw [regularizedIncompleteBeta_natCast_eq_one_sub_sum_range h hx0 hx1.le,
    hasSum_nat_add_iff' (f := fun j => (1 - x) ^ n * ((n + j - 1).choose j : ℝ) * x ^ j) m]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k
    (by rwa [Real.norm_of_nonneg hx0] : ‖x‖ < 1)).mul_left ((1 - x) ^ (k + 1))
  have hx : (1 - x) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [mul_one_div_cancel hx] at h
  convert h using 2 with j
  have hidx : k + 1 + j - 1 = j + k := by omega
  rw [hidx, Nat.choose_symm_add]
  ring

end TauCeti
