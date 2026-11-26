/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Power series of the error function and the half-Gamma series

This file expresses the real error function `TauCeti.Real.erf` on all of `ℝ` through Tricomi's
entire incomplete Gamma function `Complex.tricomiIncompleteGamma`, derives its alternating
Maclaurin series (DLMF 7.6.1) and positive-coefficient `exp(x²) erf(x)` series (DLMF 7.6.2), and
combines the latter with the exponential series to sum the half-Gamma series
`∑_{m ≥ 0} x^m / Γ(m / 2 + 1) = exp(x²) (1 + erf x)` (the real-line slice of DLMF 7.6.3, i.e. the
Mittag-Leffler function `E_{1/2}(x) = exp(x²) erfc(-x)`).

Because `|erf x| < 1` on the whole real line, the closed form immediately yields strict positivity
and the polynomial-free Gaussian majorant `∑_{m ≥ 0} x^m / Γ(m / 2 + 1) < 2 exp(x²)` for every
`x : ℝ`. Having no polynomial prefactor in `x` allows this bound to cancel Gaussian weights inside
Laplace-type integrals without losing integrability near the origin.

## Main results

* `TauCeti.Real.ofReal_erf_eq_mul_tricomiIncompleteGamma`: `(erf x : ℂ) = x γ*(1 / 2, x²)` for all
  `x : ℝ` (DLMF 7.11.3), removing the nonnegativity hypothesis of
  `TauCeti.Real.erf_eq_regularizedGamma_half_sq`.
* `TauCeti.Real.hasSum_erf`, `TauCeti.Real.erf_eq_tsum`: the alternating Maclaurin series
  `erf x = (2 / √π) ∑_{n ≥ 0} (-1)^n x^{2n + 1} / (n! (2n + 1))` (DLMF 7.6.1).
* `TauCeti.Real.mul_sum_range_two_mul_le_erf`, `TauCeti.Real.erf_le_mul_sum_range_two_mul_add_one`:
  for `0 ≤ x` with `x² ≤ 3`, where the terms of the series decrease
  (`TauCeti.Real.antitone_pow_div_factorial_mul_two_mul_add_one`), its partial sums with an even or
  odd number of terms bound `erf x` from below or above.
* `TauCeti.Real.hasSum_pow_two_mul_add_one_div_Gamma_add_three_halves`,
  `TauCeti.Real.hasSum_exp_sq_mul_erf`, `TauCeti.Real.erf_eq_mul_exp_neg_sq_mul_tsum`: the
  positive-term series `exp(x²) erf x = ∑_{n ≥ 0} x^{2n + 1} / Γ(n + 3 / 2)` and its
  double-factorial form `erf x = (2 / √π) exp(-x²) ∑_{n ≥ 0} 2^n x^{2n + 1} / (2n + 1)‼`
  (DLMF 7.6.2).
* `TauCeti.Real.hasSum_pow_div_Gamma_div_two_add_one`,
  `TauCeti.Real.tsum_pow_div_Gamma_div_two_add_one`:
  `∑_{m ≥ 0} x^m / Γ(m / 2 + 1) = exp(x²) (1 + erf x)` for all `x : ℝ` (DLMF 7.6.3).
* `Real.summable_pow_div_Gamma_div_two_add_one`, `Real.tsum_pow_div_Gamma_div_two_add_one_pos`,
  `Real.tsum_pow_div_Gamma_div_two_add_one_lt_two_mul_exp`: summability, strict positivity, and the
  sharp polynomial-free Gaussian upper bound `0 < ∑_{m ≥ 0} x^m / Γ(m / 2 + 1) < 2 exp(x²)` on all
  of `ℝ`.
* `Real.abs_tsum_pow_add_div_Gamma_div_two_add_one_le_tsum_abs`,
  `Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp`,
  `Real.abs_tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp`,
  `Real.abs_tsum_mul_pow_add_div_Gamma_div_two_add_one_le_of_abs_le_one`,
  `Real.abs_tsum_pow_add_div_Gamma_div_two_add_one_le_mul_exp`,
  `Real.tsum_pow_add_two_mul_div_Gamma_div_two_add_one_le`: for all `x : ℝ`, shifted tails of the
  half-Gamma series are bounded in absolute value by the shifted tail at `|x|`, satisfy the
  uniform polynomial-free bound `|·| < 2 exp(x²)`, the scaled small-argument bound
  `|·| ≤ 2 exp(x²) |u|^M` for `|u| ≤ 1`, the global arbitrary-shift bound
  `|·| ≤ 2 e |x|^M exp(x²)`, and the `2L`-shifted factorial bound `≤ 2 x^{2L} / L! * exp(x²)`.
* `Real.continuous_tsum_pow_div_Gamma_div_two_add_one`,
  `Real.continuous_tsum_pow_add_div_Gamma_div_two_add_one`: continuity on `ℝ` of the half-Gamma
  series and its `M`-shifted tails.

## References

* *NIST Digital Library of Mathematical Functions*, [§7.6](https://dlmf.nist.gov/7.6) and
  [§7.11](https://dlmf.nist.gov/7.11).
-/

public section

noncomputable section

open Complex Real
open scoped Nat

namespace TauCeti.Real

/-! ### Representation through Tricomi's entire incomplete Gamma function -/

/-- On the entire real line, `erf x = x γ*(1 / 2, x²)` in `ℂ` (DLMF 7.11.3), where `γ*` is
`Complex.tricomiIncompleteGamma`. Unlike `TauCeti.Real.erf_eq_regularizedGamma_half_sq`, no sign
condition on `x` is required because `x ↦ x γ*(1 / 2, x²)` is odd. -/
theorem ofReal_erf_eq_mul_tricomiIncompleteGamma (x : ℝ) :
    (erf x : ℂ) = x * Complex.tricomiIncompleteGamma (1 / 2) ((x : ℂ) ^ 2) := by
  let f : ℝ → ℂ := fun y => (erf y : ℂ) - y * Complex.tricomiIncompleteGamma (1 / 2) ((y : ℂ) ^ 2)
  have hf_deriv : ∀ y : ℝ, HasDerivAt f 0 y := fun y => by
    have herf : HasDerivAt (fun t : ℝ => (erf t : ℂ)) ((2 / √π * rexp (-y ^ 2) : ℝ) : ℂ) y :=
      (hasDerivAt_erf y).ofReal_comp
    have hsq : HasDerivAt (fun t : ℝ => ((t : ℂ) ^ 2)) (2 * (y : ℂ)) y := by
      simpa using ((hasDerivAt_pow 2 (y : ℂ)).comp_ofReal)
    have htric : HasDerivAt (fun t : ℝ => Complex.tricomiIncompleteGamma (1 / 2) ((t : ℂ) ^ 2))
        ((-(1 / 2 : ℂ) * Complex.tricomiIncompleteGamma (1 / 2 + 1) ((y : ℂ) ^ 2)) *
          (2 * (y : ℂ))) y :=
      (Complex.hasDerivAt_tricomiIncompleteGamma (1 / 2) ((y : ℂ) ^ 2)).comp y hsq
    have hmul : HasDerivAt (fun t : ℝ => (t : ℂ) *
        Complex.tricomiIncompleteGamma (1 / 2) ((t : ℂ) ^ 2))
        ((1 : ℂ) * Complex.tricomiIncompleteGamma (1 / 2) ((y : ℂ) ^ 2) +
          (y : ℂ) * ((-(1 / 2 : ℂ) * Complex.tricomiIncompleteGamma (1 / 2 + 1) ((y : ℂ) ^ 2)) *
            (2 * (y : ℂ)))) y :=
      Complex.ofRealCLM.hasDerivAt.mul htric
    have hrec := Complex.tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one
      (1 / 2) ((y : ℂ) ^ 2)
    have hΓ : Complex.Gamma (1 / 2 + 1) = ((√π / 2 : ℝ) : ℂ) := by
      have hcast : (1 / 2 + 1 : ℂ) = (((1 / 2 : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.Gamma_ofReal, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      push_cast
      ring
    have hπ : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    convert herf.sub hmul using 1
    rw [hrec, hΓ]
    push_cast
    field_simp
    ring
  have hconst : f x = f 0 :=
    is_const_of_deriv_eq_zero (fun y => (hf_deriv y).differentiableAt)
      (fun y => (hf_deriv y).deriv) x 0
  have hf0 : f 0 = 0 := by simp [f]
  exact sub_eq_zero.mp (hconst.trans hf0)

/-! ### Alternating Maclaurin series (DLMF 7.6.1) -/

/-- The alternating Maclaurin series of the error function (DLMF 7.6.1):
`erf x = ∑_{n ≥ 0} (2 / √π) (-1)^n x^{2n + 1} / (n! (2n + 1))` for all `x : ℝ`. -/
theorem hasSum_erf (x : ℝ) :
    HasSum (fun n : ℕ => 2 / √π * ((-1) ^ n * x ^ (2 * n + 1) / (n ! * (2 * n + 1))))
      (erf x) := by
  have ha : ∀ n : ℕ, (1 / 2 : ℂ) ≠ -n := fun n h => by
    have h2 : (2 * (n : ℂ) + 1) = 0 := by linear_combination 2 * h
    exact absurd h2 (by exact_mod_cast Nat.succ_ne_zero (2 * n))
  have h := (Complex.hasSum_tricomiIncompleteGamma_of_ne_neg_natCast ha ((x : ℂ) ^ 2)).mul_left
    (x : ℂ)
  rw [← ofReal_erf_eq_mul_tricomiIncompleteGamma x] at h
  have hΓ : Complex.Gamma (1 / 2) = (√π : ℂ) := by
    have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hcast, Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hπ : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  refine Complex.hasSum_ofReal.mp (h.congr_fun fun n => ?_)
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * n)
  have h12 : (1 / 2 : ℂ) + n = (2 * (n : ℂ) + 1) / 2 := by ring
  have hnf : ((n ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hΓ, h12]
  push_cast
  rw [neg_pow ((x : ℂ) ^ 2) n, ← pow_mul, pow_succ]
  field_simp

/-- The error function as a Maclaurin `tsum` (DLMF 7.6.1):
`erf x = (2 / √π) ∑_{n ≥ 0} (-1)^n x^{2n + 1} / (n! (2n + 1))`. -/
theorem erf_eq_tsum (x : ℝ) :
    erf x = 2 / √π * ∑' n : ℕ, (-1) ^ n * x ^ (2 * n + 1) / (n ! * (2 * n + 1)) := by
  rw [← (hasSum_erf x).tsum_eq, tsum_mul_left]

/-- For `0 ≤ y ≤ 3` the magnitudes `yⁿ / (n! (2n + 1))` of the terms of the erf series in
`y = x²` decrease. -/
theorem antitone_pow_div_factorial_mul_two_mul_add_one {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 3) :
    Antitone fun n : ℕ => y ^ n / (n ! * (2 * n + 1)) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity), Nat.factorial_succ]
  push_cast
  have h : y * (2 * n + 1) ≤ (n + 1) * (2 * (n + 1) + 1) := by
    have hn0 : (n : ℝ) ≤ n * n := by exact_mod_cast Nat.le_mul_self n
    nlinarith [mul_le_mul_of_nonneg_right hy (by positivity : (0 : ℝ) ≤ 2 * n + 1)]
  calc y ^ (n + 1) * (n ! * (2 * n + 1)) = y ^ n * n ! * (y * (2 * n + 1)) := by ring
    _ ≤ y ^ n * n ! * ((n + 1) * (2 * (n + 1) + 1)) := by gcongr
    _ = y ^ n * ((n + 1) * n ! * (2 * (n + 1) + 1)) := by ring

/-- For `0 < x`, dividing the Maclaurin series of `erf x` by `2x / √π` leaves an alternating
series in `x²` with sum `erf x / (2x / √π)`. -/
private theorem hasSum_erf_div {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (-1) ^ n * (x ^ 2) ^ n / (n ! * (2 * n + 1)))
      (erf x / (2 * x / √π)) := by
  have hc : 2 * x / √π ≠ 0 := by positivity
  refine (hasSum_mul_left_iff hc).1 ?_
  rw [mul_div_cancel₀ _ hc]
  convert hasSum_erf x using 2 with n
  rw [← pow_mul, pow_succ]
  ring

/-- For `0 ≤ x` with `x² ≤ 3`, partial sums of the Maclaurin series of `erf` (DLMF 7.6.1) with an
even number of terms are lower bounds:
`(2x / √π) ∑_{i < 2k} (-1)^i (x²)^i / (i! (2i + 1)) ≤ erf x`. -/
theorem mul_sum_range_two_mul_le_erf {x : ℝ} (hx : 0 ≤ x) (hx3 : x ^ 2 ≤ 3) (k : ℕ) :
    2 * x / √π * ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ 2) ^ i / (i ! * (2 * i + 1)) ≤
      erf x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have h := (hasSum_erf_div hx).tendsto_sum_nat
  simp_rw [mul_div_assoc] at h ⊢
  have h' := (antitone_pow_div_factorial_mul_two_mul_add_one (by positivity) hx3)
    |>.alternating_series_le_tendsto h k
  rwa [← le_div_iff₀' (by positivity)]

/-- For `0 ≤ x` with `x² ≤ 3`, partial sums of the Maclaurin series of `erf` (DLMF 7.6.1) with an
odd number of terms are upper bounds:
`erf x ≤ (2x / √π) ∑_{i < 2k + 1} (-1)^i (x²)^i / (i! (2i + 1))`. -/
theorem erf_le_mul_sum_range_two_mul_add_one {x : ℝ} (hx : 0 ≤ x) (hx3 : x ^ 2 ≤ 3) (k : ℕ) :
    erf x ≤ 2 * x / √π *
      ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ 2) ^ i / (i ! * (2 * i + 1)) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have h := (hasSum_erf_div hx).tendsto_sum_nat
  simp_rw [mul_div_assoc] at h ⊢
  have h' := (antitone_pow_div_factorial_mul_two_mul_add_one (by positivity) hx3)
    |>.tendsto_le_alternating_series h k
  rwa [← div_le_iff₀' (by positivity)]

/-! ### Positive-term series for `exp(x²) erf(x)` (DLMF 7.6.2) -/

/-- The Gamma-denominator series for `exp(x²) erf(x)` (DLMF 7.6.2):
`∑_{n ≥ 0} x^{2n + 1} / Γ(n + 3 / 2) = exp(x²) erf(x)` for all `x : ℝ`. This is the odd-index
subseries of the half-Gamma series `∑_{m ≥ 0} x^m / Γ(m / 2 + 1)`. -/
theorem hasSum_pow_two_mul_add_one_div_Gamma_add_three_halves (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (2 * n + 1) / Real.Gamma ((n : ℝ) + 3 / 2))
      (rexp (x ^ 2) * erf x) := by
  have h := (Complex.hasSum_tricomiIncompleteGamma (1 / 2) ((x : ℂ) ^ 2)).mul_left
    (cexp ((x : ℂ) ^ 2) * (x : ℂ))
  have hsum : cexp ((x : ℂ) ^ 2) * (x : ℂ) *
      Complex.tricomiIncompleteGamma (1 / 2) ((x : ℂ) ^ 2) =
      ((rexp (x ^ 2) * erf x : ℝ) : ℂ) := by
    rw [mul_assoc, ← ofReal_erf_eq_mul_tricomiIncompleteGamma x]
    push_cast
    ring
  rw [hsum] at h
  refine Complex.hasSum_ofReal.mp (h.congr_fun fun n => (?_ : _ = _).symm)
  have harg : (1 / 2 : ℂ) + n + 1 = (((n : ℝ) + 3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hexp : cexp ((x : ℂ) ^ 2) * cexp (-((x : ℂ) ^ 2)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [harg, Complex.Gamma_ofReal]
  calc cexp ((x : ℂ) ^ 2) * (x : ℂ) *
        (cexp (-((x : ℂ) ^ 2)) * ((x : ℂ) ^ 2) ^ n / ↑(Real.Gamma ((n : ℝ) + 3 / 2)))
      = (cexp ((x : ℂ) ^ 2) * cexp (-((x : ℂ) ^ 2))) *
          ((x : ℂ) * ((x : ℂ) ^ 2) ^ n) / ↑(Real.Gamma ((n : ℝ) + 3 / 2)) := by ring
    _ = ((x ^ (2 * n + 1) / Real.Gamma ((n : ℝ) + 3 / 2) : ℝ) : ℂ) := by
        rw [hexp, one_mul]
        push_cast
        rw [← pow_mul, ← pow_succ']

/-- The double-factorial series for `exp(x²) erf(x)` (DLMF 7.6.2):
`∑_{n ≥ 0} (2 / √π) 2^n x^{2n + 1} / (2n + 1)‼ = exp(x²) erf(x)` for all `x : ℝ`. -/
theorem hasSum_exp_sq_mul_erf (x : ℝ) :
    HasSum (fun n : ℕ => 2 / √π * (2 ^ n * x ^ (2 * n + 1) / (2 * n + 1)‼))
      (rexp (x ^ 2) * erf x) := by
  have hπ : √π ≠ 0 := by positivity
  refine (hasSum_pow_two_mul_add_one_div_Gamma_add_three_halves x).congr_fun fun n => ?_
  have harg : (n : ℝ) + 3 / 2 = (n : ℝ) + 1 + 1 / 2 := by ring
  have hdf : ((2 * n + 1)‼ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos (2 * n + 1)).ne'
  rw [harg, Real.Gamma_nat_add_one_add_half]
  field_simp
  ring

/-- DLMF 7.6.2: `erf x = (2 / √π) exp(-x²) ∑_{n ≥ 0} 2^n x^{2n + 1} / (2n + 1)‼` for all
`x : ℝ`. -/
theorem erf_eq_mul_exp_neg_sq_mul_tsum (x : ℝ) :
    erf x = 2 / √π * rexp (-x ^ 2) * ∑' n : ℕ, 2 ^ n * x ^ (2 * n + 1) / (2 * n + 1)‼ := by
  have h := (hasSum_exp_sq_mul_erf x).tsum_eq
  rw [tsum_mul_left] at h
  calc erf x = rexp (-x ^ 2) * (rexp (x ^ 2) * erf x) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = 2 / √π * rexp (-x ^ 2) * ∑' n : ℕ, 2 ^ n * x ^ (2 * n + 1) / (2 * n + 1)‼ := by
        rw [← h]
        ring

/-! ### The half-Gamma series and its Gaussian majorant (DLMF 7.6.3) -/

/-- The half-Gamma series (Mittag-Leffler `E_{1/2}` series, DLMF 7.6.3 on the imaginary axis):
`∑_{m ≥ 0} x^m / Γ(m / 2 + 1) = exp(x²) (1 + erf x) = exp(x²) erfc(-x)` for all `x : ℝ`. -/
theorem hasSum_pow_div_Gamma_div_two_add_one (x : ℝ) :
    HasSum (fun m : ℕ => x ^ m / Real.Gamma ((m : ℝ) / 2 + 1))
      (rexp (x ^ 2) * (1 + erf x)) := by
  have heven : HasSum (fun k : ℕ => x ^ (2 * k) / Real.Gamma ((↑(2 * k) : ℝ) / 2 + 1))
      (rexp (x ^ 2)) := by
    have hexp : HasSum (fun k : ℕ => (x ^ 2) ^ k / k !) (rexp (x ^ 2)) :=
      Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (x ^ 2)
    refine hexp.congr_fun fun k => ?_
    have hk : (↑(2 * k) : ℝ) / 2 + 1 = (k : ℝ) + 1 := by push_cast; ring
    rw [hk, Real.Gamma_nat_eq_factorial, pow_mul]
  have hodd : HasSum (fun k : ℕ => x ^ (2 * k + 1) / Real.Gamma ((↑(2 * k + 1) : ℝ) / 2 + 1))
      (rexp (x ^ 2) * erf x) := by
    refine (hasSum_pow_two_mul_add_one_div_Gamma_add_three_halves x).congr_fun fun k => ?_
    have hk : (↑(2 * k + 1) : ℝ) / 2 + 1 = (k : ℝ) + 3 / 2 := by push_cast; ring
    rw [hk]
  have hsum : rexp (x ^ 2) + rexp (x ^ 2) * erf x = rexp (x ^ 2) * (1 + erf x) := by ring
  rw [← hsum]
  exact HasSum.even_add_odd heven hodd

/-- Closed form for the `tsum` of the half-Gamma series (DLMF 7.6.3):
`∑_{m ≥ 0} x^m / Γ(m / 2 + 1) = exp(x²) (1 + erf x)` for all `x : ℝ`. -/
theorem tsum_pow_div_Gamma_div_two_add_one (x : ℝ) :
    (∑' m : ℕ, x ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) = rexp (x ^ 2) * (1 + erf x) :=
  (hasSum_pow_div_Gamma_div_two_add_one x).tsum_eq

end TauCeti.Real

namespace Real

/-- The half-Gamma series `∑_{m ≥ 0} x^m / Γ(m / 2 + 1)` is summable for every `x : ℝ`. -/
theorem summable_pow_div_Gamma_div_two_add_one (x : ℝ) :
    Summable fun m : ℕ => x ^ m / Real.Gamma ((m : ℝ) / 2 + 1) :=
  (TauCeti.Real.hasSum_pow_div_Gamma_div_two_add_one x).summable

/-- The half-Gamma series `∑_{m ≥ 0} x^m / Γ(m / 2 + 1)` is strictly positive for every `x : ℝ`
(including negative `x`, where the series alternates). -/
theorem tsum_pow_div_Gamma_div_two_add_one_pos (x : ℝ) :
    0 < ∑' m : ℕ, x ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
  rw [TauCeti.Real.tsum_pow_div_Gamma_div_two_add_one]
  have h1 : 0 < 1 + TauCeti.Real.erf x := by linarith [TauCeti.Real.neg_one_lt_erf x]
  positivity

/-- Sharp polynomial-free Gaussian majorant for the half-Gamma series:
`∑_{m ≥ 0} x^m / Γ(m / 2 + 1) < 2 exp(x²)` for every `x : ℝ`. -/
theorem tsum_pow_div_Gamma_div_two_add_one_lt_two_mul_exp (x : ℝ) :
    (∑' m : ℕ, x ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) < 2 * rexp (x ^ 2) := by
  rw [TauCeti.Real.tsum_pow_div_Gamma_div_two_add_one]
  have h1 : 1 + TauCeti.Real.erf x < 2 := by linarith [TauCeti.Real.erf_lt_one x]
  nlinarith [Real.exp_pos (x ^ 2)]

/-- Triangle inequality for `M`-shifted tails of the half-Gamma series: for every `x : ℝ` and
shift `M : ℕ`, `|∑_{k ≥ 0} x^{k + M} / Γ((k + M) / 2 + 1)|` is bounded by the `M`-shifted tail at
`|x|`. -/
theorem abs_tsum_pow_add_div_Gamma_div_two_add_one_le_tsum_abs (x : ℝ) (M : ℕ) :
    |∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)| ≤
      ∑' k : ℕ, |x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
  have hnorm : (fun k : ℕ => ‖x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)‖) =
      fun k : ℕ => |x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
    ext k
    rw [norm_div, norm_pow, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le]
  have hsum : Summable fun k : ℕ => ‖x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)‖ :=
    hnorm ▸ (summable_nat_add_iff M).2 (summable_pow_div_Gamma_div_two_add_one |x|)
  have hle := norm_tsum_le_tsum_norm hsum
  rwa [hnorm, Real.norm_eq_abs] at hle

/-- Every shifted tail of the half-Gamma series obeys the same polynomial-free Gaussian majorant
`< 2 exp(x²)` as the full series, for every `x : ℝ` and shift `M : ℕ`. -/
theorem tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (x : ℝ) (M : ℕ) :
    (∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) < 2 * rexp (x ^ 2) := by
  have hle := (le_abs_self _).trans (abs_tsum_pow_add_div_Gamma_div_two_add_one_le_tsum_abs x M)
  have hsplit := (summable_pow_div_Gamma_div_two_add_one |x|).sum_add_tsum_nat_add M
  have hpref : 0 ≤ ∑ m ∈ Finset.range M, |x| ^ m / Real.Gamma ((m : ℝ) / 2 + 1) :=
    Finset.sum_nonneg fun m _ => div_nonneg (by positivity)
      (Real.Gamma_pos_of_pos (by positivity)).le
  have hexp := tsum_pow_div_Gamma_div_two_add_one_lt_two_mul_exp |x|
  rw [sq_abs] at hexp
  linarith

/-- Every shifted tail of the half-Gamma series has absolute value strictly less than `2 exp(x²)`,
for every `x : ℝ` and shift `M : ℕ`. -/
theorem abs_tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (x : ℝ) (M : ℕ) :
    |∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)| < 2 * rexp (x ^ 2) :=
  calc |∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)|
      ≤ ∑' k : ℕ, |x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
        abs_tsum_pow_add_div_Gamma_div_two_add_one_le_tsum_abs x M
    _ < 2 * rexp (|x| ^ 2) := tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp |x| M
    _ = 2 * rexp (x ^ 2) := by rw [sq_abs]

/-- For `|u| ≤ 1`, every `M`-shifted tail of the scaled half-Gamma series at `x * u` is bounded in
absolute value by `2 exp(x²) |u|^M`, extracting `O(|u|^M)` vanishing near `u = 0` uniformly in
`M`. -/
theorem abs_tsum_mul_pow_add_div_Gamma_div_two_add_one_le_of_abs_le_one (x : ℝ) {u : ℝ}
    (hu : |u| ≤ 1) (M : ℕ) :
    |∑' k : ℕ, (x * u) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)| ≤
      2 * rexp (x ^ 2) * |u| ^ M := by
  have hterm : ∀ k : ℕ,
      |x * u| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) ≤
        |u| ^ M * (|x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) := fun k => by
    have hpow : |x * u| ^ (k + M) ≤ |u| ^ M * |x| ^ (k + M) := by
      rw [abs_mul, mul_pow, pow_add |u| k M]
      calc |x| ^ (k + M) * (|u| ^ k * |u| ^ M)
          ≤ |x| ^ (k + M) * (1 * |u| ^ M) := by
            gcongr
            exact pow_le_one₀ (abs_nonneg u) hu
        _ = |u| ^ M * |x| ^ (k + M) := by ring
    exact (div_le_div_of_nonneg_right hpow
      (Real.Gamma_pos_of_pos (by positivity)).le).trans_eq (mul_div_assoc _ _ _)
  have hsum₁ : Summable fun k : ℕ =>
      |x * u| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
    (summable_nat_add_iff M).2 (summable_pow_div_Gamma_div_two_add_one |x * u|)
  have hsum₂ : Summable fun k : ℕ =>
      |u| ^ M * (|x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
    ((summable_nat_add_iff M).2 (summable_pow_div_Gamma_div_two_add_one |x|)).mul_left (|u| ^ M)
  calc |∑' k : ℕ, (x * u) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)|
      ≤ ∑' k : ℕ, |x * u| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
        abs_tsum_pow_add_div_Gamma_div_two_add_one_le_tsum_abs (x * u) M
    _ ≤ ∑' k : ℕ, |u| ^ M * (|x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
        hsum₁.tsum_le_tsum hterm hsum₂
    _ = |u| ^ M * ∑' k : ℕ, |x| ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := tsum_mul_left
    _ ≤ |u| ^ M * (2 * rexp (|x| ^ 2)) := by
        gcongr
        exact (tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp |x| M).le
    _ = 2 * rexp (x ^ 2) * |u| ^ M := by rw [sq_abs]; ring

/-- For every `x : ℝ` and `L : ℕ`, the `2L`-shifted tail of the half-Gamma series is bounded by
`2 x^{2L} / L! * exp(x²)`, combining `O(x^{2L})` vanishing at `x = 0` with factorial decay in `L`
and Gaussian growth at infinity. -/
theorem tsum_pow_add_two_mul_div_Gamma_div_two_add_one_le (x : ℝ) (L : ℕ) :
    (∑' k : ℕ, x ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1)) ≤
      2 * x ^ (2 * L) / L ! * rexp (x ^ 2) := by
  have : 0 ≤ x ^ (2 * L) := by rw [pow_mul]; positivity
  have hterm : ∀ k : ℕ,
      x ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1) ≤
        x ^ (2 * L) / L ! * (|x| ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) := fun k => by
    have hs : (1 : ℝ) ≤ (k : ℝ) / 2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have harg : (↑(k + 2 * L) : ℝ) / 2 + 1 = (k : ℝ) / 2 + 1 + L := by push_cast; ring
    have hG : (Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))⁻¹ ≤
        (Real.Gamma ((k : ℝ) / 2 + 1))⁻¹ / L ! :=
      harg ▸ Real.inv_Gamma_add_natCast_le hs L
    calc x ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1)
        ≤ |x| ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1) :=
            div_le_div_of_nonneg_right (abs_pow x (k + 2 * L) ▸ le_abs_self _)
              (Real.Gamma_pos_of_pos (by positivity)).le
      _ = (|x| ^ (2 * L) * |x| ^ k) * (Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))⁻¹ := by
            rw [pow_add, mul_comm (|x| ^ k), div_eq_mul_inv]
      _ ≤ (|x| ^ (2 * L) * |x| ^ k) * ((Real.Gamma ((k : ℝ) / 2 + 1))⁻¹ / L !) := by
            gcongr
      _ = x ^ (2 * L) / L ! * (|x| ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) := by
            rw [pow_mul |x|, sq_abs, ← pow_mul]
            ring
  have hsum_tail : Summable fun k : ℕ =>
      x ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1) :=
    (summable_nat_add_iff (2 * L)).2 (summable_pow_div_Gamma_div_two_add_one x)
  have hsum_maj : Summable fun k : ℕ =>
      x ^ (2 * L) / L ! * (|x| ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) :=
    (summable_pow_div_Gamma_div_two_add_one |x|).mul_left (x ^ (2 * L) / L !)
  calc (∑' k : ℕ, x ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))
      ≤ ∑' k : ℕ, x ^ (2 * L) / L ! * (|x| ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) :=
          hsum_tail.tsum_le_tsum hterm hsum_maj
    _ = x ^ (2 * L) / L ! * ∑' k : ℕ, |x| ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := tsum_mul_left
    _ ≤ x ^ (2 * L) / L ! * (2 * rexp (|x| ^ 2)) := by
          gcongr
          exact (tsum_pow_div_Gamma_div_two_add_one_lt_two_mul_exp |x|).le
    _ = 2 * x ^ (2 * L) / L ! * rexp (x ^ 2) := by rw [sq_abs]; ring

/-- For every `x : ℝ` and any shift `M : ℕ` (even or odd), the `M`-shifted tail of the half-Gamma
series satisfies `|∑_{k ≥ 0} x^{k + M} / Γ((k + M) / 2 + 1)| ≤ 2 e |x|^M exp(x²)`. -/
theorem abs_tsum_pow_add_div_Gamma_div_two_add_one_le_mul_exp (x : ℝ) (M : ℕ) :
    |∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)| ≤
      2 * rexp 1 * |x| ^ M * rexp (x ^ 2) := by
  rcases le_total |x| 1 with hx | hx
  · have h := abs_tsum_mul_pow_add_div_Gamma_div_two_add_one_le_of_abs_le_one 1 hx M
    simp only [one_mul, one_pow] at h
    exact h.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg x)))
  · have h1 : (1 : ℝ) ≤ rexp 1 * |x| ^ M :=
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ rexp 1 * |x| ^ M :=
            mul_le_mul (Real.one_le_exp zero_le_one) (one_le_pow₀ hx) zero_le_one
              (Real.exp_nonneg 1)
    calc |∑' k : ℕ, x ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)|
        ≤ 2 * rexp (x ^ 2) := (abs_tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp x M).le
      _ = 2 * 1 * rexp (x ^ 2) := by ring
      _ ≤ 2 * (rexp 1 * |x| ^ M) * rexp (x ^ 2) := by gcongr
      _ = 2 * rexp 1 * |x| ^ M * rexp (x ^ 2) := by ring

/-- Continuity on `ℝ` of the `M`-shifted half-Gamma series
`z ↦ ∑_{k ≥ 0} z^{k + M} / Γ((k + M) / 2 + 1)`. -/
theorem continuous_tsum_pow_add_div_Gamma_div_two_add_one (M : ℕ) :
    Continuous fun z : ℝ => ∑' k : ℕ, z ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
  have heq : (fun z : ℝ => ∑' k : ℕ, z ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) =
      fun z : ℝ => rexp (z ^ 2) * (1 + TauCeti.Real.erf z) -
        ∑ m ∈ Finset.range M, z ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
    ext z
    have hsplit := (summable_pow_div_Gamma_div_two_add_one z).sum_add_tsum_nat_add M
    rw [TauCeti.Real.tsum_pow_div_Gamma_div_two_add_one] at hsplit
    linarith
  rw [heq]
  exact ((Real.continuous_exp.comp (continuous_pow 2)).mul
    (continuous_const.add TauCeti.Real.continuous_erf)).sub (by fun_prop)

/-- Continuity on `ℝ` of the half-Gamma series `z ↦ ∑_{m ≥ 0} z^m / Γ(m / 2 + 1)`. -/
theorem continuous_tsum_pow_div_Gamma_div_two_add_one :
    Continuous fun z : ℝ => ∑' m : ℕ, z ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
  simpa using continuous_tsum_pow_add_div_Gamma_div_two_add_one 0

end Real
