/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Euler's limit formula for the Gamma function in Pochhammer form

Euler's limit formula `Γ(s) = lim n^s n! / (s (s + 1) ⋯ (s + n))` is Mathlib's
`Complex.GammaSeq_tendsto_Gamma`. Written with the rising factorial
`(s)ₙ = s (s + 1) ⋯ (s + n - 1)`, it reads

`n^(s - 1) n! / (s)ₙ → Γ(s)` and `(s)ₙ / (n^(s - 1) n!) → 1 / Γ(s)` as `n → ∞`,

for every complex `s`. At the poles `s = -k` both sides of either limit are `0`: the rising
factorial vanishes for `n > k`, and Mathlib's `Γ(-k)` and `(Γ(-k))⁻¹` are `0`. The second limit is
the asymptotic `(s)ₙ ∼ n^(s - 1) n! / Γ(s)` from which the growth of hypergeometric coefficients
is read off.

## Main results

* `Complex.tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval`:
  `n^(s - 1) n! / (s)ₙ → Γ(s)`.
* `Complex.tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial`:
  `(s)ₙ / (n^(s - 1) n!) → (Γ(s))⁻¹`.

## References

* NIST Digital Library of Mathematical Functions, 5.8.1, <https://dlmf.nist.gov/5.8.E1>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/Basic/GaussSeries.lean`.
-/

public section

open Filter Polynomial
open scoped Nat Topology

namespace Complex

/-- **Euler's limit formula in Pochhammer form.** For every complex `s`,
`n^(s - 1) n! / (s)ₙ → Γ(s)` as `n → ∞`. -/
theorem tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval (s : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ (s - 1) * n ! / (ascPochhammer ℂ n).eval s) atTop
      (𝓝 (Gamma s)) := by
  have hlin : Tendsto (fun n : ℕ => s / n + 1) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat s).add_const 1
  have h := (GammaSeq_tendsto_Gamma s).mul hlin
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop ‖s‖] with n hn hs
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsn : s + n ≠ 0 := by
    intro h
    rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_natCast] at hs
    exact lt_irrefl _ hs
  rw [GammaSeq, Finset.prod_range_succ, ← TauCeti.ascPochhammer_eval_eq_prod_range,
    cpow_sub _ _ hn', cpow_one]
  rcases eq_or_ne ((ascPochhammer ℂ n).eval s) 0 with hp | hp
  · simp [hp]
  · field_simp

/-- **Euler's limit formula for `1 / Γ` in Pochhammer form.** For every complex `s`,
`(s)ₙ / (n^(s - 1) n!) → (Γ(s))⁻¹` as `n → ∞`; at the poles `s = -k` both sides are eventually
`0`. -/
theorem tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial (s : ℂ) :
    Tendsto (fun n : ℕ => (ascPochhammer ℂ n).eval s / ((n : ℂ) ^ (s - 1) * n !)) atTop
      (𝓝 (Gamma s)⁻¹) := by
  by_cases hs : ∀ m : ℕ, s ≠ -m
  · simpa only [inv_div] using
      (tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval s).inv₀ (Gamma_ne_zero hs)
  · push Not at hs
    obtain ⟨k, rfl⟩ := hs
    rw [Gamma_neg_nat_eq_zero, inv_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [ascPochhammer_eval_neg_natCast_of_lt hn, zero_div]

end Complex
