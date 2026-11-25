/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Fourier coefficients of `1 / (b + c e^{iθ})`

For complex numbers `b`, `c` with `‖b‖ ≠ ‖c‖` and an integer `n`, this file computes

`∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ`,

which is `2π` times the `(-n)`-th Fourier coefficient of `θ ↦ 1 / (b + c e^{iθ})`:

* if `‖c‖ < ‖b‖`, it is `2π (-c)^{-n} b^{n-1}` for `n ≤ 0` and `0` for `n ≥ 1`;
* if `‖b‖ < ‖c‖`, it is `0` for `n ≤ 0` and `2π (-b)^{n-1} c^{-n}` for `n ≥ 1`.

With `b = a` and `c = r > 0` these are the inner integrals of the kernel `G_w` of liquid type
weights in the dimer model: `(2π)⁻¹ ∫₀^{2π} e^{inθ} / (a + r e^{iθ}) dθ` is
`[|a| > r] (-r)^{-n} a^{n-1}` for `n ≤ 0` and `[|a| < r] (-a)^{n-1} r^{-n}` for `n ≥ 1`.

## Proof

The integral `∫₀^{2π} e^{iθ} f(e^{iθ}) dθ` is `-i` times the circle integral of `f` over the unit
circle, so it vanishes when `f` is holomorphic on the closed unit disc
(`TauCeti.integral_exp_mul_I_mul_eq_zero`). For `‖c‖ < ‖b‖` and `n ≥ 1` this applies to
`f(z) = z^{n-1} / (b + c z)`. For `‖c‖ < ‖b‖` and `n = -N ≤ 0` the finite geometric expansion
`1 / (b + c w) = Σ_{k ≤ N} b⁻¹ (-c w / b)^k + (-c w / b)^{N + 1} / (b + c w)` reduces the integral
to the integrals `∫₀^{2π} e^{ikθ} dθ = 2π [k = 0]` (`TauCeti.integral_exp_int_mul_I`) and one
vanishing integral of the first kind. The case `‖b‖ < ‖c‖` follows from these two by the
substitution `θ ↦ -θ`, which exchanges the roles of `b` and `c` and of `n` and `1 - n`.

## Main results

* `TauCeti.integral_exp_int_mul_I`: `∫₀^{2π} e^{ikθ} dθ = 2π [k = 0]`.
* `TauCeti.integral_exp_mul_I_mul_eq_zero`: `∫₀^{2π} e^{iθ} f(e^{iθ}) dθ = 0` for `f`
  holomorphic on the closed unit disc.
* `TauCeti.integral_exp_div_add_of_nonpos_of_norm_lt`,
  `TauCeti.integral_exp_div_add_of_pos_of_norm_lt`,
  `TauCeti.integral_exp_div_add_of_nonpos_of_lt_norm`,
  `TauCeti.integral_exp_div_add_of_pos_of_lt_norm`: the four cases above.
-/

public section

open Complex Metric Set intervalIntegral
open scoped Real

namespace TauCeti

/-- `∫₀^{2π} e^{ikθ} dθ = 2π [k = 0]` for every integer `k`. -/
theorem integral_exp_int_mul_I (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (k * θ * I) = if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · have hc : (k * I : ℂ) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    have h1 : exp (k * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I k]
      push_cast
      ring_nf
    simp only [h1, ofReal_zero, mul_zero, exp_zero, sub_self, zero_div] at h
    calc _ = ∫ θ in (0 : ℝ)..2 * π, exp (k * I * θ) := by congr 1; ext θ; ring_nf
      _ = 0 := h

/-- `∫₀^{2π} e^{iθ} f(e^{iθ}) dθ = 0` when `f` is holomorphic on the open unit disc and continuous
on its closure: this integral is `-i` times the circle integral of `f` over the unit circle. -/
theorem integral_exp_mul_I_mul_eq_zero {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball 0 1)) :
    ∫ θ in (0 : ℝ)..2 * π, exp (θ * I) * f (exp (θ * I)) = 0 := by
  have h := hf.circleIntegral_eq_zero zero_le_one
  rw [circleIntegral] at h
  simp only [deriv_circleMap, ofReal_one, one_mul, smul_eq_mul, circleMap,
    zero_add] at h
  have h' : ∫ θ in (0 : ℝ)..2 * π, exp (θ * I) * f (exp (θ * I)) * I = 0 := by
    rw [← h]
    congr 1
    ext θ
    ring
  rw [intervalIntegral.integral_mul_const] at h'
  exact (mul_eq_zero.1 h').resolve_right I_ne_zero

/-- For `‖c‖ < ‖b‖` the denominator `b + c z` does not vanish on the closed unit disc. -/
private theorem add_mul_ne_zero {b c z : ℂ} (hcb : ‖c‖ < ‖b‖) (hz : ‖z‖ ≤ 1) :
    b + c * z ≠ 0 := by
  intro h
  have hb : b = -(c * z) := eq_neg_of_add_eq_zero_left h
  have : ‖b‖ ≤ ‖c‖ := by
    rw [hb, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg c) hz
  exact this.not_gt hcb

/-- A function of the form `z ↦ z ^ m / (b + c z)` with `‖c‖ < ‖b‖` is holomorphic on the closed
unit disc. -/
private theorem diffContOnCl_pow_div_add_mul {b c : ℂ} (hcb : ‖c‖ < ‖b‖) (m : ℕ) :
    DiffContOnCl ℂ (fun z => z ^ m / (b + c * z)) (ball (0 : ℂ) 1) := by
  refine DifferentiableOn.diffContOnCl fun z hz => ?_
  rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right] at hz
  exact ((differentiableAt_pow m).div ((differentiableAt_const b).add
    ((differentiableAt_const c).mul differentiableAt_id))
    (add_mul_ne_zero hcb hz)).differentiableWithinAt

private theorem norm_exp_mul_I (θ : ℝ) : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ

private theorem continuous_exp_int_mul_I (k : ℤ) : Continuous fun θ : ℝ => exp (k * θ * I) := by
  fun_prop

/-- For `‖c‖ < ‖b‖` and `n ≥ 1`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 0`. -/
theorem integral_exp_div_add_of_pos_of_norm_lt {b c : ℂ} (hcb : ‖c‖ < ‖b‖) {n : ℤ}
    (hn : 0 < n) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨(n - 1).toNat, by omega⟩
  rw [← integral_exp_mul_I_mul_eq_zero (diffContOnCl_pow_div_add_mul hcb m)]
  congr 1
  ext θ
  rw [mul_div_assoc', ← exp_natCast_mul, ← exp_add]
  congr 2
  push_cast
  ring

/-- The finite geometric expansion of `w^{-N} / (b + c w)` on the unit circle. -/
private theorem exp_neg_div_add_eq {b c : ℂ} (hcb : ‖c‖ < ‖b‖) (N : ℕ) (θ : ℝ) :
    exp (((-N : ℤ) : ℂ) * θ * I) / (b + c * exp (θ * I)) =
      (∑ k ∈ Finset.range (N + 1),
        b⁻¹ * (-c / b) ^ k * exp ((k - N : ℤ) * θ * I)) +
      (-c / b) ^ (N + 1) * (exp (θ * I) * (exp (θ * I) ^ 0 / (b + c * exp (θ * I)))) := by
  set w := exp (θ * I) with hw
  have hb : b ≠ 0 := norm_pos_iff.1 ((norm_nonneg c).trans_lt hcb)
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hd : b + c * w ≠ 0 := add_mul_ne_zero hcb (norm_exp_mul_I θ).le
  have hexp : ∀ k : ℤ, exp (k * θ * I) = w ^ k := fun k => by
    rw [hw, ← exp_intCast_mul]
    ring_nf
  have hq : -c * w / b ≠ 1 := by
    intro h
    apply hd
    field_simp at h
    linear_combination -h
  rw [hexp, Finset.sum_congr rfl fun k _ => by rw [hexp, zpow_sub₀ hw0, zpow_natCast,
    zpow_natCast]]
  have hsum : ∑ k ∈ Finset.range (N + 1), b⁻¹ * (-c / b) ^ k * (w ^ k / w ^ N) =
      b⁻¹ / w ^ N * ∑ k ∈ Finset.range (N + 1), (-c * w / b) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_pow, div_pow, mul_pow]
    field_simp
  have hlast : (-c / b) ^ (N + 1) * (w * (w ^ 0 / (b + c * w))) =
      (-c * w / b) ^ (N + 1) / w ^ N / (b * (1 - -c * w / b)) := by
    rw [pow_zero, show b * (1 - -c * w / b) = b + c * w by field_simp; ring]
    field_simp
    ring
  rw [hsum, hlast, geom_sum_eq hq, zpow_neg, zpow_natCast,
    show b + c * w = b * (1 - -c * w / b) by field_simp; ring]
  generalize -c * w / b = q at hq ⊢
  have h1q : 1 - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 hq
  field_simp
  ring

/-- For `‖c‖ < ‖b‖` and `n ≤ 0`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 2π (-c)^{-n} b^{n-1}`. -/
theorem integral_exp_div_add_of_nonpos_of_norm_lt {b c : ℂ} (hcb : ‖c‖ < ‖b‖) {n : ℤ}
    (hn : n ≤ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      2 * π * (-c) ^ (-n) * b ^ (n - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = -N := ⟨(-n).toNat, by omega⟩
  have hb : b ≠ 0 := norm_pos_iff.1 ((norm_nonneg c).trans_lt hcb)
  simp_rw [exp_neg_div_add_eq hcb N]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    integral_exp_mul_I_mul_eq_zero (diffContOnCl_pow_div_add_mul hcb 0), mul_zero, add_zero,
    intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I, sub_eq_zero,
      Nat.cast_inj, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range (N + 1)) N, ite_eq_left (Finset.self_mem_range_succ N),
      neg_neg, zpow_natCast, show (-(N : ℤ) - 1) = -((N + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, div_pow, pow_succ]
    field_simp
  · exact fun k _ => (continuous_const.mul (continuous_exp_int_mul_I _)).intervalIntegrable _ _
  · exact (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (continuous_exp_int_mul_I _)).intervalIntegrable _ _
  · refine (continuous_const.mul ((by fun_prop : Continuous fun θ : ℝ => exp (θ * I)).mul
      ((by fun_prop : Continuous fun θ : ℝ => exp (θ * I) ^ 0).div (by fun_prop)
        fun θ => add_mul_ne_zero hcb (norm_exp_mul_I θ).le))).intervalIntegrable _ _

/-- A `2π`-periodic function has the same integral over `[0, 2π]` as its reflection. -/
private theorem integral_comp_neg_of_periodic {F : ℝ → ℂ} (hF : Function.Periodic F (2 * π)) :
    ∫ θ in (0 : ℝ)..2 * π, F (-θ) = ∫ θ in (0 : ℝ)..2 * π, F θ := by
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  simpa using hF.intervalIntegral_add_eq (-(2 * π)) 0

private theorem periodic_exp_div_add (b c : ℂ) (n : ℤ) :
    Function.Periodic (fun θ : ℝ => exp (n * θ * I) / (b + c * exp (θ * I))) (2 * π) := by
  intro θ
  have h : ∀ k : ℤ, exp (k * ((θ + 2 * π : ℝ) : ℂ) * I) = exp (k * θ * I) := fun k => by
    rw [← mul_one (exp (k * θ * I)), ← exp_int_mul_two_pi_mul_I k, ← exp_add]
    push_cast
    ring_nf
  simp only
  rw [h n, show ((θ + 2 * π : ℝ) : ℂ) * I = ((1 : ℤ) : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I by simp,
    h 1]
  simp

/-- The substitution `θ ↦ -θ` exchanges `b` and `c` and sends `n` to `1 - n`. -/
private theorem integral_exp_div_add_swap (b c : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      ∫ θ in (0 : ℝ)..2 * π, exp ((1 - n : ℤ) * θ * I) / (c + b * exp (θ * I)) := by
  rw [← integral_comp_neg_of_periodic (periodic_exp_div_add b c n)]
  congr 1
  ext θ
  have hw0 : exp (θ * I) ≠ 0 := exp_ne_zero _
  have h1 : exp (((-θ : ℝ) : ℂ) * I) = (exp (θ * I))⁻¹ := by
    rw [← exp_neg]
    push_cast
    ring_nf
  have h2 : exp (n * ((-θ : ℝ) : ℂ) * I) = (exp (θ * I) ^ n)⁻¹ := by
    rw [← exp_intCast_mul, ← exp_neg]
    push_cast
    ring_nf
  have h3 : exp ((1 - n : ℤ) * θ * I) = exp (θ * I) / exp (θ * I) ^ n := by
    rw [← exp_intCast_mul, ← exp_sub]
    push_cast
    ring_nf
  rw [h1, h2, h3]
  rcases eq_or_ne (c + b * exp (θ * I)) 0 with h | h
  · have h' : b + c * (exp (θ * I))⁻¹ = 0 := by
      rw [show b + c * (exp (θ * I))⁻¹ = (c + b * exp (θ * I)) / exp (θ * I) by field_simp; ring,
        h, zero_div]
    rw [h, h', div_zero, div_zero]
  · have hp : exp (θ * I) ^ n ≠ 0 := zpow_ne_zero n hw0
    field_simp
    rw [add_comm (b * _) c, div_self h]

/-- For `‖b‖ < ‖c‖` and `n ≤ 0`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 0`. -/
theorem integral_exp_div_add_of_nonpos_of_lt_norm {b c : ℂ} (hbc : ‖b‖ < ‖c‖) {n : ℤ}
    (hn : n ≤ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) = 0 := by
  rw [integral_exp_div_add_swap]
  exact integral_exp_div_add_of_pos_of_norm_lt hbc (by omega)

/-- For `‖b‖ < ‖c‖` and `n ≥ 1`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 2π (-b)^{n-1} c^{-n}`. -/
theorem integral_exp_div_add_of_pos_of_lt_norm {b c : ℂ} (hbc : ‖b‖ < ‖c‖) {n : ℤ}
    (hn : 0 < n) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      2 * π * (-b) ^ (n - 1) * c ^ (-n) := by
  rw [integral_exp_div_add_swap, integral_exp_div_add_of_nonpos_of_norm_lt hbc (by omega)]
  congr 2 <;> ring_nf

end TauCeti
