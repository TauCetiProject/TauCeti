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

In a complete normed algebra `A` over `ℝ`, `((exp (n⁻¹ • x) * exp (n⁻¹ • y)) ^ n) → exp (x + y)` as
`n → ∞`, without any unit-norm hypothesis (`‖(1 : A)‖ ≤ 1`).

## Main results

* `NormedSpace.norm_exp_sub_one_le`, `NormedSpace.tendsto_exp_inv_smul_mul_exp_inv_smul_pow`.

## References

* H. F. Trotter, Proc. Amer. Math. Soc. 10 (1959); B. C. Hall, *Lie Groups, Lie Algebras, and
  Representations*, 2nd ed., Springer (2015), Theorem 2.11.
-/

public section

open Filter Topology
open scoped Nat

noncomputable section

namespace NormedSpace

private theorem norm_mul_one_add_pow_le {A : Type*} [NormedRing A] (z b : A) :
    ∀ n : ℕ, ‖z * (1 + b) ^ n‖ ≤ ‖z‖ * (1 + ‖b‖) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', ← mul_assoc, mul_add, mul_one, pow_succ', ← mul_assoc]
    exact (norm_mul_one_add_pow_le (z + z * b) b n).trans <| mul_le_mul_of_nonneg_right
      ((norm_add_le z (z * b)).trans <| by
        linarith [norm_mul_le z b, (by ring : ‖z‖ + ‖z‖ * ‖b‖ = ‖z‖ * (1 + ‖b‖))]) (by positivity)

private theorem norm_one_add_pow_sub_one_add_pow_le {A : Type*} [NormedRing A] {a b : A} {M : ℝ}
    (ha : 1 + ‖a‖ ≤ M) (hb : 1 + ‖b‖ ≤ M) :
    ∀ n : ℕ, ‖(1 + a) ^ n - (1 + b) ^ n‖ ≤ n * M ^ (n - 1) * ‖a - b‖
  | 0 => by simp
  | n + 1 => by
    have hM : 0 ≤ M := (by positivity : 0 ≤ 1 + ‖a‖).trans ha
    have hpow : M * ((n : ℝ) * M ^ (n - 1)) = (n : ℝ) * M ^ n := by
      rcases n with _ | n <;> simp [pow_succ']; ring
    set d := (1 + a) ^ n - (1 + b) ^ n
    have hleft : ‖d + a * d‖ ≤ (n : ℝ) * M ^ n * ‖a - b‖ :=
      ((norm_add_le _ _).trans <| by
        linarith [norm_mul_le a d, (by ring : ‖d‖ + ‖a‖ * ‖d‖ = (1 + ‖a‖) * ‖d‖)]).trans <|
        (mul_le_mul ha (norm_one_add_pow_sub_one_add_pow_le ha hb n) (norm_nonneg _) hM).trans_eq
          (by rw [← mul_assoc, hpow])
    have hright : ‖(a - b) * (1 + b) ^ n‖ ≤ M ^ n * ‖a - b‖ :=
      (norm_mul_one_add_pow_le (a - b) b n).trans <|
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb n) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
    rw [show (1 + a) ^ (n + 1) - (1 + b) ^ (n + 1) = (d + a * d) + (a - b) * (1 + b) ^ n by
      simp only [d, pow_succ', add_mul, one_mul, sub_mul, mul_sub]; abel, Nat.add_sub_cancel]
    exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by push_cast; ring))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- In any real Banach algebra, `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1`. Unlike `‖exp x‖ ≤ Real.exp ‖x‖`,
this requires no bound on `‖(1 : A)‖` because the constant term cancels. -/
theorem norm_exp_sub_one_le (x : A) : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx : HasSum (fun n : ℕ ↦ ((n + 1)!⁻¹ : ℝ) • x ^ (n + 1)) (exp x - 1) := by
    simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).2 (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr : HasSum (fun n : ℕ ↦ ((n + 1)!⁻¹ : ℝ) * ‖x‖ ^ (n + 1)) (Real.exp ‖x‖ - 1) := by
    simpa [Finset.sum_range_one, Real.exp_eq_exp_ℝ, smul_eq_mul] using
      (hasSum_nat_add_iff' 1).2 (exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) ‖x‖)
  rw [← hx.tsum_eq]
  refine tsum_of_norm_bounded hr fun n ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x n.succ_pos) (by positivity)

/-- **Lie–Trotter product formula** in a real Banach algebra: for all `x, y : A`,
`(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n` converges to `exp (x + y)` as `n → ∞`. -/
theorem tendsto_exp_inv_smul_mul_exp_inv_smul_pow (x y : A) :
    Tendsto (fun n : ℕ ↦ (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n)
      atTop (𝓝 (exp (x + y))) := by
  let g : ℝ → A := fun t ↦ exp (t • x) * exp (t • y) - exp (t • (x + y))
  have hmul : HasDerivAt (fun t : ℝ ↦ exp (t • x) * exp (t • y)) (x + y) 0 := by
    simpa using (hasDerivAt_exp_smul_const x (0 : ℝ)).fun_mul (hasDerivAt_exp_smul_const y (0 : ℝ))
  have hxy : HasDerivAt (fun t : ℝ ↦ exp (t • (x + y))) (x + y) 0 := by
    simpa using hasDerivAt_exp_smul_const (x + y) (0 : ℝ)
  have hg0 : HasDerivAt g 0 0 := by simpa only [g, Pi.sub_def, sub_self] using hmul.sub hxy
  have hslope : Tendsto (fun t : ℝ ↦ ‖t‖⁻¹ * ‖g t‖) (𝓝 0) (𝓝 0) := by
    simpa [g] using hasDerivAt_iff_tendsto.1 hg0
  have hlim_seq : Tendsto (fun n : ℕ ↦ (n : ℝ) * ‖g (n : ℝ)⁻¹‖) atTop (𝓝 0) :=
    (hslope.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)).congr' <| by
      filter_upwards [eventually_gt_atTop 0] with n _; simp [Function.comp_def]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (by simpa using hlim_seq.const_mul (Real.exp (‖x‖ + ‖y‖)))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set t : ℝ := (n : ℝ)⁻¹
  have ht0 : 0 ≤ t := inv_nonneg.2 hnR.le
  set a : A := exp (t • x) * exp (t • y) - 1
  set b : A := exp (t • (x + y)) - 1
  set M : ℝ := Real.exp (t * (‖x‖ + ‖y‖))
  have hb_pow : (1 + b) ^ n = exp (x + y) := by
    rw [add_sub_cancel, ← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hnR.ne', one_smul]
  have hex : ‖exp (t • x) - 1‖ ≤ Real.exp (t * ‖x‖) - 1 := by
    simpa [norm_smul, Real.norm_of_nonneg ht0] using norm_exp_sub_one_le (t • x)
  have hey : ‖exp (t • y) - 1‖ ≤ Real.exp (t * ‖y‖) - 1 := by
    simpa [norm_smul, Real.norm_of_nonneg ht0] using norm_exp_sub_one_le (t • y)
  have haM : 1 + ‖a‖ ≤ M := by
    have hprod := (norm_mul_le (exp (t • x) - 1) (exp (t • y) - 1)).trans <|
      mul_le_mul hex hey (norm_nonneg _) (sub_nonneg.2 (Real.one_le_exp (by positivity)))
    have htri := (norm_add_le ((exp (t • x) - 1) * (exp (t • y) - 1) + (exp (t • x) - 1))
      (exp (t • y) - 1)).trans (add_le_add_left (norm_add_le _ _) _)
    rw [show (exp (t • x) - 1) * (exp (t • y) - 1) + (exp (t • x) - 1) + (exp (t • y) - 1) = a by
      simp only [a, sub_mul, mul_sub, one_mul, mul_one]; abel] at htri
    exact (by linarith : 1 + ‖a‖ ≤ Real.exp (t * ‖x‖) * Real.exp (t * ‖y‖)).trans_eq
      (by rw [← Real.exp_add, ← mul_add])
  have hbM : 1 + ‖b‖ ≤ M :=
    (by linarith [norm_exp_sub_one_le (t • (x + y))] : 1 + ‖b‖ ≤ Real.exp ‖t • (x + y)‖).trans <|
      Real.exp_le_exp.2 (by rw [norm_smul, Real.norm_of_nonneg ht0]; gcongr; exact norm_add_le x y)
  have hMn : M ^ (n - 1) ≤ Real.exp (‖x‖ + ‖y‖) := by
    rw [← Real.exp_nat_mul]
    have hle : ((n - 1 : ℕ) : ℝ) * t ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) ht0).trans_eq
        (mul_inv_cancel₀ hnR.ne')
    exact Real.exp_le_exp.2 (by nlinarith [norm_nonneg x, norm_nonneg y])
  rw [Real.norm_of_nonneg (norm_nonneg _), ← add_sub_cancel 1 (exp (t • x) * exp (t • y)), ← hb_pow]
  calc ‖(1 + a) ^ n - (1 + b) ^ n‖
      ≤ (n : ℝ) * M ^ (n - 1) * ‖g t‖ := by
          simpa [a, b, g] using norm_one_add_pow_sub_one_add_pow_le haM hbM n
    _ ≤ (n : ℝ) * Real.exp (‖x‖ + ‖y‖) * ‖g t‖ := by gcongr
    _ = Real.exp (‖x‖ + ‖y‖) * ((n : ℝ) * ‖g t‖) := by ring

end NormedSpace
