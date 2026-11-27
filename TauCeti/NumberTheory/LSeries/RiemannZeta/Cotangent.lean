/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The Taylor expansion of the cotangent in the even zeta values

For complex `z` with `0 < |z| < 1`,

  `π cot (πz) = 1/z - 2 ∑_{n ≥ 1} ζ(2n) z^(2n - 1)`,

the series converging absolutely (a summable family in `ℂ` is absolutely summable,
`summable_norm_iff`). This is Euler's expansion of the cotangent in the values of `ζ` at the even
integers; with `riemannZeta_two_mul_nat` it is the expansion of `πz cot (πz)` in the Bernoulli
numbers. The radius `1` is the distance from `0` to the nearest other poles `±1` of `cot (πz)`.

The proof expands each term of the partial-fraction expansion `cot_series_rep'`,
`1/(z - n) + 1/(z + n) = 2z/(z² - n²) = -2 ∑_{k ≥ 0} z^(2k+1) / n^(2k+2)` for `|z| < 1 ≤ n`,
as a geometric series. The double series converges absolutely, since
`|z|^(2k+1) / n^(2k+2) ≤ |z|^(2k+1) / n²`, so the two summations may be exchanged, and
`∑_{n ≥ 1} 1 / n^(2k+2) = ζ(2k + 2)`.

## Main results

* `TauCeti.hasSum_pi_mul_cot_pi_mul_sub_one_div`: `∑_{k ≥ 0} -2 ζ(2k + 2) z^(2k+1)` has sum
  `π cot (πz) - 1/z` for `‖z‖ < 1`. At `z = 0` both sides are `0`, by the conventions
  `cot 0 = 0` and `1/0 = 0`.
* `TauCeti.pi_mul_cot_pi_mul_eq_one_div_sub_tsum`: the expansion as an identity of sums,
  `π cot (πz) = 1/z - 2 ∑_{k ≥ 0} ζ(2k + 2) z^(2k+1)`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- The geometric expansion `z / ((n + 1)² - z²) = ∑_{k ≥ 0} z^(2k+1) / (n + 1)^(2k+2)` for
`‖z‖ < n + 1`. -/
private theorem hasSum_pow_div_natCast_add_one_pow {z : ℂ} {n : ℕ} (hz : ‖z‖ < n + 1) :
    HasSum (fun k : ℕ ↦ z ^ (2 * k + 1) / (n + 1 : ℂ) ^ (2 * k + 2))
      (z / ((n + 1 : ℂ) ^ 2 - z ^ 2)) := by
  have hm : ‖(n + 1 : ℂ)‖ = n + 1 := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  have hm₀ : (n + 1 : ℂ) ≠ 0 := by
    rw [← norm_ne_zero_iff, hm]
    positivity
  have hq : ‖z ^ 2 / (n + 1 : ℂ) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, norm_pow, hm, div_lt_one (by positivity)]
    exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
  have hne : (n + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, div_self (pow_ne_zero 2 hm₀), norm_one] at hq
    exact lt_irrefl 1 hq
  convert (hasSum_geometric_of_norm_lt_one hq).mul_left (z / (n + 1 : ℂ) ^ 2) using 1
  · funext k
    rw [div_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  · field_simp

/-- `ζ(2k + 2) = ∑_{n ≥ 0} 1 / (n + 1)^(2k+2)`, with the summability of the series. -/
private theorem hasSum_one_div_natCast_add_one_pow (k : ℕ) :
    HasSum (fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ (2 * k + 2)) (riemannZeta (2 * k + 2)) := by
  have hs : Summable fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ (2 * k + 2) := by
    refine Summable.of_norm ?_
    refine ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (show 1 < 2 * k + 2 by omega))).congr fun n ↦ ?_
    rw [norm_div, norm_one, norm_pow, show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
  convert hs.hasSum using 1
  rw [show (2 * (k : ℂ) + 2) = ((2 * k + 2 : ℕ) : ℂ) by push_cast; ring,
    zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [natCast_re]; exact_mod_cast (by omega))]
  simp_rw [cpow_natCast]

/-- The family `(n, k) ↦ z^(2k+1) / (n + 1)^(2k+2)` is absolutely summable for `‖z‖ < 1`. -/
private theorem summable_norm_pow_div_natCast_add_one_pow {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun p : ℕ × ℕ ↦ ‖z ^ (2 * p.2 + 1) / (p.1 + 1 : ℂ) ^ (2 * p.2 + 2)‖ := by
  have h₁ : Summable fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ 2) := by
    simpa using (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  have h₂ : Summable fun k : ℕ ↦ ‖z‖ ^ (2 * k + 1) :=
    ((summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg z] :
      ‖z‖ ^ 2 < 1)).mul_left ‖z‖).congr fun k ↦ by ring
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_)
    (h₁.mul_of_nonneg h₂ (fun _ ↦ by positivity) (fun _ ↦ by positivity))
  have hm : ‖(p.1 + 1 : ℂ)‖ = p.1 + 1 := by
    rw [show (p.1 + 1 : ℂ) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  rw [norm_div, norm_pow, norm_pow, hm, one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1)]) (by omega))

/-- **The Taylor expansion of the cotangent.** For `‖z‖ < 1`,
`∑_{k ≥ 0} -2 ζ(2k + 2) z^(2k+1) = π cot (πz) - 1/z`, that is
`π cot (πz) = 1/z - 2 ∑_{n ≥ 1} ζ(2n) z^(2n - 1)`. At `z = 0` both sides are `0`. -/
theorem hasSum_pi_mul_cot_pi_mul_sub_one_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ -2 * riemannZeta (2 * k + 2) * z ^ (2 * k + 1))
      (π * cot (π * z) - 1 / z) := by
  rcases eq_or_ne z 0 with rfl | hz₀
  · simp [Complex.cot_eq_cos_div_sin]
  have hzZ : z ∈ integerComplement := by
    rintro ⟨m, rfl⟩
    have h : |(m : ℝ)| < 1 := by simpa [Complex.norm_intCast] using hz
    have h₁ : -1 < m := by exact_mod_cast (abs_lt.1 h).1
    have h₂ : m < 1 := by exact_mod_cast (abs_lt.1 h).2
    exact hz₀ (by simp [show m = 0 by omega])
  set f : ℕ × ℕ → ℂ := fun p ↦ z ^ (2 * p.2 + 1) / (p.1 + 1 : ℂ) ^ (2 * p.2 + 2) with hf
  have hS : Summable f := (summable_norm_pow_div_natCast_add_one_pow hz).of_norm
  -- summing over `k` first gives `z / ((n + 1)² - z²)`; summing over `n` first, `ζ(2k + 2)`
  have hn : HasSum (fun n : ℕ ↦ z / ((n + 1 : ℂ) ^ 2 - z ^ 2)) (∑' p, f p) :=
    hS.hasSum.prod_fiberwise fun n ↦ hasSum_pow_div_natCast_add_one_pow
      (hz.trans_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have hk : HasSum (fun k : ℕ ↦ riemannZeta (2 * k + 2) * z ^ (2 * k + 1)) (∑' p, f p) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hS.hasSum).prod_fiberwise fun k ↦ by
      have h := (hasSum_one_div_natCast_add_one_pow k).mul_left (z ^ (2 * k + 1))
      rw [mul_comm (z ^ _)] at h
      convert h using 1
      funext n
      simp [hf, div_eq_mul_inv]
  -- each term of the partial-fraction expansion is `-2 z / ((n + 1)² - z²)`
  have hcot : π * cot (π * z) - 1 / z = -2 * ∑' p, f p := by
    rw [cot_series_rep' hzZ, ← hn.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    have h₁ := integerComplement_add_ne_zero hzZ (n + 1)
    have h₂ := integerComplement_add_ne_zero hzZ (-(n + 1))
    push_cast at h₁ h₂
    rw [← sub_eq_add_neg] at h₂
    have h₃ : (n + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      refine mul_ne_zero (by rwa [add_comm]) fun h ↦ h₂ ?_
      linear_combination -h
    field_simp
    ring
  rw [hcot]
  simpa only [mul_assoc] using hk.mul_left (-2)

/-- **The Taylor expansion of the cotangent**, as an identity of sums: for `‖z‖ < 1`,
`π cot (πz) = 1/z - 2 ∑_{k ≥ 0} ζ(2k + 2) z^(2k+1)`. -/
theorem pi_mul_cot_pi_mul_eq_one_div_sub_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    π * cot (π * z) = 1 / z - 2 * ∑' k : ℕ, riemannZeta (2 * k + 2) * z ^ (2 * k + 1) := by
  have h := (hasSum_pi_mul_cot_pi_mul_sub_one_div hz).tsum_eq
  simp only [mul_assoc, tsum_mul_left] at h
  linear_combination -h

/-- At `z = 1/2`, where `cot (π/2) = 0`, the expansion gives `∑_{n ≥ 1} ζ(2n) / 4ⁿ = 1/2`. -/
example : HasSum (fun k : ℕ ↦ riemannZeta (2 * k + 2) * (1 / 4) ^ (k + 1)) (1 / 2) := by
  have h := (hasSum_pi_mul_cot_pi_mul_sub_one_div (z := 1 / 2) (by norm_num)).mul_left (-1 / 4)
  have hcot : cot (π * (1 / 2 : ℂ)) = 0 := by
    rw [Complex.cot_eq_cos_div_sin, show (π : ℂ) * (1 / 2) = π / 2 by ring, Complex.cos_pi_div_two,
      zero_div]
  rw [hcot] at h
  convert h using 1
  · funext k
    rw [show (1 / 4 : ℂ) = (1 / 2) ^ 2 by norm_num, ← pow_mul,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    ring
  · norm_num

end TauCeti
