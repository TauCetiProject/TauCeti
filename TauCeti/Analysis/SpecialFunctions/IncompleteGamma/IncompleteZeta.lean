/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.Analysis.MellinTransform.ExpKernel
import TauCeti.NumberTheory.LSeries.RiemannZeta.Mellin

/-!
# The incomplete Riemann zeta function

For `1 < Re s` and `0 ≤ x`, expanding `1/(e^t − 1) = ∑_{k ≥ 1} e^{−kt}` under the integral (via
`TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul` from
`TauCeti.Analysis.MellinTransform.ExpKernel`) gives the incomplete Riemann zeta function as a
series of regularized incomplete Gamma functions,
`Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt = ∑_{k ≥ 1} k^{−s} P(s, kx)` (DLMF 8.22.2). As `x → ∞` the
left side tends to `Γ(s)⁻¹ ∫₀^∞ t^{s−1}/(e^t − 1) dt = ζ(s)` (DLMF 8.22.3), using
`TauCeti.integrableOn_cpow_div_exp_sub_one` and
`TauCeti.integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta`.

## Main results

* `TauCeti.hasSum_cpow_neg_mul_regularizedGamma` and
  `TauCeti.inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum`: DLMF 8.22.2;
* `TauCeti.tendsto_tsum_cpow_neg_mul_regularizedGamma_atTop`: DLMF 8.22.3, the limit
  `∑_{k ≥ 1} k^{−s} P(s, kx) → ζ(s)` as `x → ∞`.

## Implementation notes

The series are indexed by `k : ℕ`. In the statements of DLMF 8.22.2–8.22.3 the term `k = 0`
vanishes because `0^{−s} = 0` for `s ≠ 0`, so they match `zeta_eq_tsum_one_div_nat_cpow`.
Each finite integral is rescaled to a lower incomplete Gamma function by
`TauCeti.intervalIntegral_cpow_mul_exp_neg_mul`.

## References

* NIST Digital Library of Mathematical Functions, §8.22,
  <https://dlmf.nist.gov/8.22>.

The proofs are new.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Real Topology

namespace TauCeti

open Complex

/-- **DLMF 8.22.2**, as a `HasSum`: for `1 < Re s` and `0 ≤ x`, the series
`∑_{k ≥ 1} k^{−s} P(s, kx)` converges to `Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt`. -/
theorem hasSum_cpow_neg_mul_regularizedGamma {s : ℂ} (hs : 1 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun k : ℕ => (k : ℂ) ^ (-s) * regularizedGamma s (k * x))
      ((Gamma s)⁻¹ * ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) / (cexp t - 1)) := by
  have hs0 : 0 < s.re := by linarith
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
  have hs1 : -s ≠ 0 := neg_ne_zero.mpr fun h => by simp [h] at hs0
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.sum_range_one, Nat.cast_zero, zero_cpow hs1, zero_mul, sub_zero,
    intervalIntegral.integral_of_le hx]
  have hsum := (hasSum_setIntegral_cpow_mul_exp_neg_mul hs (c := 1) one_pos
    (A := Ioc 0 x) Ioc_subset_Ioi_self).mul_left (Gamma s)⁻¹
  simp only [sub_self, zero_mul, exp_zero, one_div, ← div_eq_mul_inv] at hsum
  convert hsum using 1
  funext k
  have h := intervalIntegral_cpow_mul_exp_neg_mul hs0 (Nat.cast_add_one_ne_zero k) hx
  rw [intervalIntegral.integral_of_le hx] at h
  push_cast at h ⊢
  rw [h, lowerIncompleteGamma_def]
  field_simp

/-- **DLMF 8.22.2**: for `1 < Re s` and `0 ≤ x`,
`Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt = ∑_{k ≥ 1} k^{−s} P(s, kx)`. -/
theorem inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum {s : ℂ} (hs : 1 < s.re)
    {x : ℝ} (hx : 0 ≤ x) :
    (Gamma s)⁻¹ * ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) / (cexp t - 1) =
      ∑' k : ℕ, (k : ℂ) ^ (-s) * regularizedGamma s (k * x) :=
  (hasSum_cpow_neg_mul_regularizedGamma hs hx).tsum_eq.symm

/-- **DLMF 8.22.3**: for `1 < Re s`, `∑_{k ≥ 1} k^{−s} P(s, kx) → ζ(s)` as `x → ∞`. -/
theorem tendsto_tsum_cpow_neg_mul_regularizedGamma_atTop {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun x : ℝ => ∑' k : ℕ, (k : ℂ) ^ (-s) * regularizedGamma s (k * x)) atTop
      (𝓝 (riemannZeta s)) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_cpow_div_exp_sub_one hs)
    tendsto_id).const_mul (Gamma s)⁻¹
  rw [integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta hs, inv_mul_cancel_left₀ hG] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum hs hx

end TauCeti
