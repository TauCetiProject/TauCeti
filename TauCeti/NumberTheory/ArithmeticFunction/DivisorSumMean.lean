/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.NumberTheory.Divisors

/-!
# The mean value of a divisor sum

Let `g` be a function on the natural numbers with values in a real Banach space, and put
`a(t) = ∑_{d ∣ t} g(d)`. If `∑_d ‖g(d)‖ / √d` converges, then `a` has the mean value
`C = ∑_d g(d) / d`, with a square-root error term:

`‖∑_{1 ≤ t ≤ x} a(t) - x C‖ ≤ √x ∑_d ‖g(d)‖ / √d` for every real `x ≥ 0`.

This is the first-order form of Wintner's mean value theorem with an explicit remainder. Regrouping
the sum by divisor gives `∑_{t ≤ x} a(t) = ∑_{d ≤ x} ⌊x / d⌋ g(d)`. A divisor `d ≤ x` contributes
`(⌊x / d⌋ - x / d) g(d)` to the difference, of norm at most `‖g(d)‖ ≤ √(x / d) ‖g(d)‖`, and a
divisor `d > x` contributes `-(x / d) g(d)`, of norm at most `√(x / d) ‖g(d)‖`.

## Main results

* `TauCeti.summable_inv_smul_of_summable_norm_div_sqrt`: the series `∑_d g(d) / d` converges.
* `TauCeti.norm_sum_Ioc_sum_divisors_sub_smul_tsum_le`: the mean value estimate above.
* `TauCeti.isBigO_sum_Ioc_sum_divisors_sub_smul_tsum`: `∑_{t ≤ x} a(t) - x C = O(√x)`.
* `TauCeti.norm_sum_Ioc_mul_zeta_sub_mul_tsum_le`: the estimate for the Dirichlet convolution
  `g * ζ` of an arithmetic function with real or complex values.

## References

* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), proof of Lemma 4.3, pp. 705–706. There Wintner's theorem is quoted
  in a general form, equation (4.2), and applied with
  `g(d) = |μ(d)| ∏_{p ∣ d} ((1 + f(p)) ^ n - 1)`; the estimate of this file is the case of (4.2)
  used there, with the two error terms combined.
-/

public section

open Asymptotics Filter Finset
open scoped ArithmeticFunction.zeta

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coefficient of `g(d)` in `∑_{d ≤ x} ⌊x / d⌋ g(d) - x ∑_d g(d) / d` has absolute value at
most `√x / √d`. -/
private theorem abs_ite_natFloor_div_sub_mul_inv_le {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    |(if d ∈ Ioc 0 ⌊x⌋₊ then ((⌊x⌋₊ / d : ℕ) : ℝ) else 0) - x * (d : ℝ)⁻¹| ≤ √x / √d := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  have hd' : (0 : ℝ) < d := mod_cast hd
  split_ifs with h
  · have hdx : (d : ℝ) ≤ x := (Nat.cast_le.2 (mem_Ioc.1 h).2).trans (Nat.floor_le hx)
    have h1 : (⌊x / d⌋₊ : ℝ) ≤ x / d := Nat.floor_le (div_nonneg hx hd'.le)
    have h2 : x / d < ⌊x / d⌋₊ + 1 := Nat.lt_floor_add_one _
    have h3 : 1 ≤ √x / √d := (one_le_div (Real.sqrt_pos.2 hd')).2 (Real.sqrt_le_sqrt hdx)
    rw [← Nat.floor_div_natCast, ← div_eq_mul_inv, abs_le]
    constructor <;> linarith
  · have hxd : x < d := Nat.lt_of_floor_lt (by simpa [hd] using h)
    have hs : √x ≤ √d := Real.sqrt_le_sqrt hxd.le
    rw [zero_sub, abs_neg, abs_of_nonneg (by positivity), ← div_eq_mul_inv,
      div_le_div_iff₀ hd' (Real.sqrt_pos.2 hd')]
    calc x * √d = √x * √d * √x := by rw [mul_right_comm, Real.mul_self_sqrt hx]
      _ ≤ √x * √d * √d :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = √x * d := by rw [mul_assoc, Real.mul_self_sqrt hd'.le]

/-- If `∑_d ‖g(d)‖ / √d` converges, then so does the series `∑_d g(d) / d` of the mean value. -/
theorem summable_inv_smul_of_summable_norm_div_sqrt [CompleteSpace E] {g : ℕ → E}
    (hg : Summable fun d : ℕ ↦ ‖g d‖ / √d) : Summable fun d : ℕ ↦ (d : ℝ)⁻¹ • g d := by
  refine Summable.of_norm_bounded hg fun d ↦ ?_
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  have hd' : (1 : ℝ) ≤ d := mod_cast hd
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.sqrt_pos.2 (by linarith))
    ((Real.sqrt_le_left (by linarith)).2 (by nlinarith))

/-- **The mean value of a divisor sum.** If `∑_d ‖g(d)‖ / √d` converges, then for every real
`x ≥ 0`,
`‖∑_{1 ≤ t ≤ x} ∑_{d ∣ t} g(d) - x ∑_d g(d) / d‖ ≤ √x ∑_d ‖g(d)‖ / √d`. -/
theorem norm_sum_Ioc_sum_divisors_sub_smul_tsum_le [CompleteSpace E] {g : ℕ → E}
    (hg : Summable fun d : ℕ ↦ ‖g d‖ / √d) {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ t ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ t.divisors, g d - x • ∑' d : ℕ, (d : ℝ)⁻¹ • g d‖ ≤
      √x * ∑' d : ℕ, ‖g d‖ / √d := by
  have hsum : ∑ d ∈ Ioc 0 ⌊x⌋₊, (if d ∈ Ioc 0 ⌊x⌋₊ then (⌊x⌋₊ / d) • g d else 0) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (⌊x⌋₊ / d) • g d :=
    sum_congr rfl fun d hd ↦ ite_eq_left_of_eq_true _ _ (eq_true hd)
  have hfin : HasSum (fun d : ℕ ↦ if d ∈ Ioc 0 ⌊x⌋₊ then (⌊x⌋₊ / d) • g d else 0)
      (∑ d ∈ Ioc 0 ⌊x⌋₊, (⌊x⌋₊ / d) • g d) := by
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun d hd ↦ ite_eq_right_of_eq_false _ _ (eq_false hd)
  have hdiff := HasSum.sub hfin
    (HasSum.const_smul x (summable_inv_smul_of_summable_norm_div_sqrt hg).hasSum)
  rw [Nat.sum_Ioc_sum_divisors]
  refine HasSum.norm_le_of_bounded hdiff (HasSum.mul_left √x hg.hasSum) fun d ↦ ?_
  have hsmul : (if d ∈ Ioc 0 ⌊x⌋₊ then (⌊x⌋₊ / d) • g d else 0) - x • ((d : ℝ)⁻¹ • g d) =
      ((if d ∈ Ioc 0 ⌊x⌋₊ then ((⌊x⌋₊ / d : ℕ) : ℝ) else 0) - x * (d : ℝ)⁻¹) • g d := by
    rw [sub_smul, mul_smul, ite_smul, zero_smul, Nat.cast_smul_eq_nsmul]
  rw [hsmul, norm_smul, Real.norm_eq_abs]
  calc |(if d ∈ Ioc 0 ⌊x⌋₊ then ((⌊x⌋₊ / d : ℕ) : ℝ) else 0) - x * (d : ℝ)⁻¹| * ‖g d‖
      ≤ √x / √d * ‖g d‖ :=
        mul_le_mul_of_nonneg_right (abs_ite_natFloor_div_sub_mul_inv_le hx d) (norm_nonneg _)
    _ = √x * (‖g d‖ / √d) := by ring

/-- If `∑_d ‖g(d)‖ / √d` converges, then
`∑_{1 ≤ t ≤ x} ∑_{d ∣ t} g(d) - x ∑_d g(d) / d = O(√x)` as `x → ∞`. -/
theorem isBigO_sum_Ioc_sum_divisors_sub_smul_tsum [CompleteSpace E] {g : ℕ → E}
    (hg : Summable fun d : ℕ ↦ ‖g d‖ / √d) :
    (fun x : ℝ ↦ ∑ t ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ t.divisors, g d - x • ∑' d : ℕ, (d : ℝ)⁻¹ • g d)
      =O[atTop] fun x : ℝ ↦ √x := by
  refine IsBigO.of_bound (∑' d : ℕ, ‖g d‖ / √d) ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), mul_comm]
  exact norm_sum_Ioc_sum_divisors_sub_smul_tsum_le hg hx

/-- **The mean value of a Dirichlet convolution with `ζ`.** For an arithmetic function `g` with
real or complex values such that `∑_d ‖g(d)‖ / √d` converges, and every real `x ≥ 0`,
`‖∑_{1 ≤ n ≤ x} (g * ζ)(n) - x ∑_d g(d) / d‖ ≤ √x ∑_d ‖g(d)‖ / √d`. -/
theorem norm_sum_Ioc_mul_zeta_sub_mul_tsum_le {𝕜 : Type*} [RCLike 𝕜] {g : ArithmeticFunction 𝕜}
    (hg : Summable fun d : ℕ ↦ ‖g d‖ / √d) {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, (g * ζ) n - x * ∑' d : ℕ, g d / d‖ ≤ √x * ∑' d : ℕ, ‖g d‖ / √d := by
  have h := norm_sum_Ioc_sum_divisors_sub_smul_tsum_le hg hx
  have hterm : ∀ d : ℕ, (d : ℝ)⁻¹ • g d = g d / d := fun d ↦ by
    rw [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast, inv_mul_eq_div]
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, RCLike.real_smul_eq_coe_mul, hterm] using h

/-! ### Examples -/

/-- For `g = 1`, the indicator of `1`, the divisor sum is the constant `1` and the estimate
reads `|⌊x⌋ - x| ≤ √x`. -/
example {x : ℝ} (hx : 0 ≤ x) : |(⌊x⌋₊ : ℝ) - x| ≤ √x := by
  have hsum : HasSum (fun d : ℕ ↦ ‖(1 : ArithmeticFunction ℝ) d‖ / √d) 1 := by
    convert hasSum_ite_eq 1 (1 : ℝ) using 2 with d
    by_cases hd : d = 1 <;> simp [hd]
  have h := norm_sum_Ioc_mul_zeta_sub_mul_tsum_le hsum.summable hx
  have hC : ∑' d : ℕ, (1 : ArithmeticFunction ℝ) d / d = 1 := by
    rw [tsum_eq_single 1 fun d hd ↦ by simp [hd]]
    simp
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, ((1 : ArithmeticFunction ℝ) * ζ) n = ⌊x⌋₊ :=
    calc ∑ n ∈ Ioc 0 ⌊x⌋₊, ((1 : ArithmeticFunction ℝ) * ζ) n
        = ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) :=
          sum_congr rfl fun n hn ↦ by simp [(mem_Ioc.1 hn).1.ne']
      _ = ⌊x⌋₊ := by simp
  rwa [hsum.tsum_eq, hC, hS, mul_one, mul_one, Real.norm_eq_abs] at h

end TauCeti
