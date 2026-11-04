/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The Lie–Trotter product formula in a Banach algebra

In a complete normed algebra `A` over `ℝ`, the exponential of a sum is the limit of iterated
products of rescaled exponentials:

`((exp (n⁻¹ • x) * exp (n⁻¹ • y)) ^ n) → exp (x + y)` as `n → ∞`.

No unit-norm hypothesis (`‖(1 : A)‖ ≤ 1`) is needed, so the formula applies uniformly to matrix
algebras with empty index types as well as general operator algebras. Writing each factor in the
form `1 + a` avoids `‖(1 : A)‖`: every positive power in `exp z - 1` has norm at most `‖z‖ ^ m`,
giving `‖exp z - 1‖ ≤ Real.exp ‖z‖ - 1`, and inductively `‖(1 + a) ^ n - (1 + b) ^ n‖` is at most
`n * M ^ (n - 1) * ‖a - b‖` whenever `1 + ‖a‖ ≤ M` and `1 + ‖b‖ ≤ M`. For
`1 + a = exp (n⁻¹ • x) * exp (n⁻¹ • y)` and `1 + b = exp (n⁻¹ • (x + y))`, one may take
`M = Real.exp ((‖x‖ + ‖y‖) / n)`, whose `(n - 1)`st power is bounded by `Real.exp (‖x‖ + ‖y‖)`,
while differentiability of `t ↦ exp (t • x) * exp (t • y) - exp (t • (x + y))` at `0` with
vanishing derivative sends `n * ‖a - b‖` to `0`.

## Main results

* `NormedSpace.norm_exp_sub_one_le`: `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1` in any real Banach algebra,
  without any bound on `‖(1 : A)‖`.
* `NormedSpace.tendsto_exp_inv_smul_mul_exp_inv_smul_pow`: **the Lie–Trotter product formula**
  `(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n → exp (x + y)` as `n → ∞`.

## References

* H. F. Trotter, *On the product of semi-groups of operators*, Proc. Amer. Math. Soc. 10 (1959),
  545–551.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Graduate Texts in
  Mathematics 222, Springer (2015), Theorem 2.11.
-/

public section

open Filter Topology
open scoped Nat

noncomputable section

namespace NormedSpace

section Ring

variable {A : Type*} [NormedRing A]

/-- Right-multiplying a power of `1 + b` scales norms by at most `(1 + ‖b‖) ^ n`, without
invoking `‖(1 : A)‖`. -/
private theorem norm_mul_one_add_pow_le (z b : A) :
    ∀ n : ℕ, ‖z * (1 + b) ^ n‖ ≤ ‖z‖ * (1 + ‖b‖) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', ← mul_assoc, mul_add, mul_one]
    have hstep : ‖z + z * b‖ ≤ ‖z‖ * (1 + ‖b‖) := by
      calc ‖z + z * b‖ ≤ ‖z‖ + ‖z * b‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ‖z‖ * ‖b‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖z‖ * (1 + ‖b‖) := by ring
    exact (norm_mul_one_add_pow_le (z + z * b) b n).trans <| by
      rw [pow_succ']
      nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + ‖b‖) n]

/-- Noncommutative telescoping bound for powers of perturbations of `1`, avoiding `‖(1 : A)‖`. -/
private theorem norm_one_add_pow_sub_one_add_pow_le {a b : A} {M : ℝ}
    (ha : 1 + ‖a‖ ≤ M) (hb : 1 + ‖b‖ ≤ M) :
    ∀ n : ℕ, ‖(1 + a) ^ n - (1 + b) ^ n‖ ≤ n * M ^ (n - 1) * ‖a - b‖
  | 0 => by simp
  | 1 => by
    have hsub : (1 + a) ^ 1 - (1 + b) ^ 1 = a - b := by
      rw [pow_one, pow_one]
      abel
    rw [hsub]
    simp
  | n + 2 => by
    have hM : 0 ≤ M := (by positivity : 0 ≤ 1 + ‖a‖).trans ha
    have hdecomp :
        (1 + a) ^ (n + 2) - (1 + b) ^ (n + 2) =
          ((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)) +
            a * ((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)) +
            (a - b) * (1 + b) ^ (n + 1) := by
      simp only [pow_succ', add_mul, one_mul, sub_mul, mul_sub]
      abel
    have hleft :
        ‖((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)) +
            a * ((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1))‖ ≤
          ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * ‖a - b‖ := by
      calc ‖((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)) +
              a * ((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1))‖
          ≤ ‖(1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)‖ +
              ‖a‖ * ‖(1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_mul_le _ _
        _ = (1 + ‖a‖) * ‖(1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)‖ := by ring
        _ ≤ M * (((n + 1 : ℕ) : ℝ) * M ^ n * ‖a - b‖) := by
            gcongr
            exact norm_one_add_pow_sub_one_add_pow_le ha hb (n + 1)
        _ = ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * ‖a - b‖ := by
            rw [pow_succ']
            ring
    have hright : ‖(a - b) * (1 + b) ^ (n + 1)‖ ≤ M ^ (n + 1) * ‖a - b‖ := by
      calc ‖(a - b) * (1 + b) ^ (n + 1)‖
          ≤ ‖a - b‖ * (1 + ‖b‖) ^ (n + 1) := norm_mul_one_add_pow_le (a - b) b (n + 1)
        _ ≤ ‖a - b‖ * M ^ (n + 1) := by gcongr
        _ = M ^ (n + 1) * ‖a - b‖ := mul_comm _ _
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    calc ‖((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1)) +
            a * ((1 + a) ^ (n + 1) - (1 + b) ^ (n + 1))‖ +
          ‖(a - b) * (1 + b) ^ (n + 1)‖
        ≤ ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * ‖a - b‖ + M ^ (n + 1) * ‖a - b‖ :=
          add_le_add hleft hright
      _ = ((n + 2 : ℕ) : ℝ) * M ^ (n + 1) * ‖a - b‖ := by
          push_cast
          ring

end Ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- In any real Banach algebra, `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1`. Unlike `‖exp x‖ ≤ Real.exp ‖x‖`,
this requires no bound on `‖(1 : A)‖` because the constant term cancels. -/
theorem norm_exp_sub_one_le (x : A) : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx : HasSum (fun n : ℕ ↦ ((n + 1)!⁻¹ : ℝ) • x ^ (n + 1)) (exp x - 1) := by
    simpa [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr : HasSum (fun n : ℕ ↦ ((n + 1)!⁻¹ : ℝ) * ‖x‖ ^ (n + 1)) (Real.exp ‖x‖ - 1) := by
    have h0 : HasSum (fun n : ℕ ↦ (n !⁻¹ : ℝ) * ‖x‖ ^ n) (Real.exp ‖x‖) := by
      rw [Real.exp_eq_exp_ℝ]
      simpa [smul_eq_mul] using exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) ‖x‖
    simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).2 h0
  rw [← hx.tsum_eq]
  refine tsum_of_norm_bounded hr fun n ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le' x n.succ_pos

/-- **Lie–Trotter product formula** in a real Banach algebra: for all `x, y : A`,
`(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n` converges to `exp (x + y)` as `n → ∞`. -/
theorem tendsto_exp_inv_smul_mul_exp_inv_smul_pow (x y : A) :
    Tendsto (fun n : ℕ ↦ (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n)
      atTop (𝓝 (exp (x + y))) := by
  let g : ℝ → A := fun t ↦ exp (t • x) * exp (t • y) - exp (t • (x + y))
  have hg0 : g 0 = 0 := by simp [g]
  have hderiv : HasDerivAt g 0 0 := by
    have hx : HasDerivAt (fun t : ℝ ↦ exp (t • x)) x 0 := by
      simpa using hasDerivAt_exp_smul_const x (0 : ℝ)
    have hy : HasDerivAt (fun t : ℝ ↦ exp (t • y)) y 0 := by
      simpa using hasDerivAt_exp_smul_const y (0 : ℝ)
    have hxy : HasDerivAt (fun t : ℝ ↦ exp (t • (x + y))) (x + y) 0 := by
      simpa using hasDerivAt_exp_smul_const (x + y) (0 : ℝ)
    have hmul : HasDerivAt (fun t : ℝ ↦ exp (t • x) * exp (t • y)) (x + y) 0 := by
      simpa using hx.fun_mul hy
    simpa only [g, Pi.sub_def, sub_self] using HasDerivAt.sub hmul hxy
  have hslope : Tendsto (fun t : ℝ ↦ ‖t‖⁻¹ * ‖g t‖) (𝓝 0) (𝓝 0) := by
    simpa [hg0] using hasDerivAt_iff_tendsto.1 hderiv
  have hlim_seq : Tendsto (fun n : ℕ ↦ (n : ℝ) * ‖g (n : ℝ)⁻¹‖) atTop (𝓝 0) := by
    have hcomp := hslope.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n _hn
    simp [Function.comp_def]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_
    (by simpa using hlim_seq.const_mul (Real.exp (‖x‖ + ‖y‖)))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set t : ℝ := (n : ℝ)⁻¹
  have ht0 : 0 ≤ t := inv_nonneg.2 hnR.le
  set a : A := exp (t • x) * exp (t • y) - 1
  set b : A := exp (t • (x + y)) - 1
  set M : ℝ := Real.exp (t * (‖x‖ + ‖y‖))
  have ha1 : 1 + a = exp (t • x) * exp (t • y) := add_sub_cancel 1 _
  have hb1 : 1 + b = exp (t • (x + y)) := add_sub_cancel 1 _
  have hab : a - b = g t := by simp [a, b, g]
  have hb_pow : (1 + b) ^ n = exp (x + y) := by
    rw [hb1, ← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hnR.ne', one_smul]
  have haM : 1 + ‖a‖ ≤ M := by
    have hdecomp : a = (exp (t • x) - 1) * (exp (t • y) - 1) +
        (exp (t • x) - 1) + (exp (t • y) - 1) := by
      simp only [a, sub_mul, mul_sub, one_mul, mul_one]
      abel
    have hex : ‖exp (t • x) - 1‖ ≤ Real.exp (t * ‖x‖) - 1 := by
      simpa [norm_smul, Real.norm_of_nonneg ht0] using norm_exp_sub_one_le (t • x)
    have hey : ‖exp (t • y) - 1‖ ≤ Real.exp (t * ‖y‖) - 1 := by
      simpa [norm_smul, Real.norm_of_nonneg ht0] using norm_exp_sub_one_le (t • y)
    have hprod : ‖(exp (t • x) - 1) * (exp (t • y) - 1)‖ ≤
        (Real.exp (t * ‖x‖) - 1) * (Real.exp (t * ‖y‖) - 1) :=
      (norm_mul_le _ _).trans <| mul_le_mul hex hey (norm_nonneg _)
        (sub_nonneg.2 (Real.one_le_exp (by positivity)))
    have ha_norm : ‖a‖ ≤ (Real.exp (t * ‖x‖) - 1) * (Real.exp (t * ‖y‖) - 1) +
        (Real.exp (t * ‖x‖) - 1) + (Real.exp (t * ‖y‖) - 1) := by
      rw [hdecomp]
      calc ‖(exp (t • x) - 1) * (exp (t • y) - 1) + (exp (t • x) - 1) + (exp (t • y) - 1)‖
          ≤ ‖(exp (t • x) - 1) * (exp (t • y) - 1) + (exp (t • x) - 1)‖ +
              ‖exp (t • y) - 1‖ := norm_add_le _ _
        _ ≤ (‖(exp (t • x) - 1) * (exp (t • y) - 1)‖ + ‖exp (t • x) - 1‖) +
              ‖exp (t • y) - 1‖ := add_le_add_left (norm_add_le _ _) _
        _ ≤ (Real.exp (t * ‖x‖) - 1) * (Real.exp (t * ‖y‖) - 1) +
              (Real.exp (t * ‖x‖) - 1) + (Real.exp (t * ‖y‖) - 1) :=
            add_le_add (add_le_add hprod hex) hey
    calc 1 + ‖a‖
        ≤ 1 + ((Real.exp (t * ‖x‖) - 1) * (Real.exp (t * ‖y‖) - 1) +
            (Real.exp (t * ‖x‖) - 1) + (Real.exp (t * ‖y‖) - 1)) := add_le_add_right ha_norm 1
      _ = Real.exp (t * ‖x‖) * Real.exp (t * ‖y‖) := by ring
      _ = M := by rw [← Real.exp_add, ← mul_add]
  have hbM : 1 + ‖b‖ ≤ M := by
    have heb : ‖b‖ ≤ Real.exp ‖t • (x + y)‖ - 1 := norm_exp_sub_one_le _
    calc 1 + ‖b‖ ≤ 1 + (Real.exp ‖t • (x + y)‖ - 1) := add_le_add_right heb 1
      _ = Real.exp ‖t • (x + y)‖ := by ring
      _ ≤ M := by
          apply Real.exp_le_exp.2
          rw [norm_smul, Real.norm_of_nonneg ht0]
          gcongr
          exact norm_add_le x y
  have hMn : M ^ (n - 1) ≤ Real.exp (‖x‖ + ‖y‖) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hle : ((n - 1 : ℕ) : ℝ) * t ≤ 1 := by
      have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      calc ((n - 1 : ℕ) : ℝ) * t ≤ (n : ℝ) * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hn1 ht0
        _ = 1 := mul_inv_cancel₀ hnR.ne'
    calc ((n - 1 : ℕ) : ℝ) * (t * (‖x‖ + ‖y‖))
        = (((n - 1 : ℕ) : ℝ) * t) * (‖x‖ + ‖y‖) := by ring
      _ ≤ 1 * (‖x‖ + ‖y‖) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = ‖x‖ + ‖y‖ := one_mul _
  rw [Real.norm_of_nonneg (norm_nonneg _), ← ha1, ← hb_pow]
  calc ‖(1 + a) ^ n - (1 + b) ^ n‖
      ≤ (n : ℝ) * M ^ (n - 1) * ‖a - b‖ := norm_one_add_pow_sub_one_add_pow_le haM hbM n
    _ ≤ (n : ℝ) * Real.exp (‖x‖ + ‖y‖) * ‖g t‖ := by
        rw [hab]
        gcongr
    _ = Real.exp (‖x‖ + ‖y‖) * ((n : ℝ) * ‖g t‖) := by ring

end NormedSpace
