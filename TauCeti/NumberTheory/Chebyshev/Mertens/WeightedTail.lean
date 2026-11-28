/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.Chebyshev.LogPsiAP
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.NumberTheory.Chebyshev.WeightedError

/-!
# Weighted Chebyshev tails in Mertens' theorem

`Chebyshev.logPsiAP_eq_mul_log_add_sub_integral` uses the finite Abel identity
`Chebyshev.logPsiAP_eq_psiAP_div_add_integral` to transfer bounds for
`E(t) = psiAP q a t - c * t` to the logarithmic progression sum. The errors to bound are
`E(x) / x` and the tail of `E(t) / t²` above `x`.
`Chebyshev.tendsto_logPsiAP_sub_mul_log_sub` isolates the endpoint error in the limit
using Mathlib's `MeasureTheory.tendsto_integral_Ioi_zero`.

At level one, `Chebyshev.sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add`
gives the main term `log x - γ` using `Chebyshev.integral_psi_sub_div_sq`. The endpoint
and tail bounds then control the difference from that main term.
`Chebyshev.tendsto_sum_vonMangoldt_div_sub_log` gives the limit `-γ` after subtracting
`log x`, using Mathlib's `Chebyshev.tendsto_psi_div_atTop`.

## References

* O. Ramaré, *Explicit estimates for the summatory function of Λ(n)/n from the one of Λ(n)*,
  Acta Arith. 159 (2013).
-/

public section

open ArithmeticFunction Filter Finset MeasureTheory Set
open scoped Chebyshev Topology

namespace Chebyshev

/-- If `E(t) = psiAP q a t - c * t` is absolutely integrable against `dt/t²` above one,
then for `x > 0` the logarithmic sum equals `c * log x` plus the constant
`c + ∫ t in Ioi 1, E(t) / t²` and the endpoint error, less the weighted tail.
At level one this is the transfer used by Ramaré (2013). -/
theorem logPsiAP_eq_mul_log_add_sub_integral {q : ℕ} {a : ZMod q} {c x : ℝ} (hx : 0 < x)
    (h : IntegrableOn (fun t : ℝ ↦ (psiAP q a t - c * t) / t ^ 2) (Ioi 1)) :
    logPsiAP q a x = c * Real.log x +
      (c + ∫ t in Ioi (1 : ℝ), (psiAP q a t - c * t) / t ^ 2) +
      (psiAP q a x - c * x) / x - ∫ t in Ioi x, (psiAP q a t - c * t) / t ^ 2 := by
  have hpos : uIcc 1 x ⊆ Ioi (0 : ℝ) := ordConnected_Ioi.uIcc_subset zero_lt_one hx
  have hne (t : ℝ) (ht : t ∈ uIcc 1 x) : t ≠ 0 := (hpos ht).ne'
  have hE : IntervalIntegrable (fun t : ℝ ↦ (psiAP q a t - c * t) / t ^ 2) volume 1 x := by
    simp only [div_eq_mul_inv]
    exact ((psiAP_mono q a).intervalIntegrable.sub
      (Continuous.intervalIntegrable (by fun_prop) 1 x)).mul_continuousOn
        ((continuousOn_id.pow 2).inv₀ fun t ht ↦ pow_ne_zero _ (hne t ht))
  have hinv : IntervalIntegrable (fun t : ℝ ↦ c * t⁻¹) volume 1 x :=
    (intervalIntegral.intervalIntegrable_inv hne continuousOn_id).const_mul c
  have hlog : (∫ t in (1 : ℝ)..x, c * t⁻¹) = c * Real.log x := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hx, div_one]
  have hsplit : (∫ t in (1 : ℝ)..x, psiAP q a t / t ^ 2) =
      (∫ t in (1 : ℝ)..x, (psiAP q a t - c * t) / t ^ 2) + c * Real.log x := by
    rw [← hlog, ← intervalIntegral.integral_add hE hinv]
    exact intervalIntegral.integral_congr fun t ht ↦ by
      have ht₀ : t ≠ 0 := hne t ht
      field
  have htail := intervalIntegral.integral_interval_add_Ioi' hE.symm h
  rw [intervalIntegral.integral_symm 1 x] at htail
  rw [logPsiAP_eq_psiAP_div_add_integral, hsplit, ← htail, sub_div,
    mul_div_cancel_right₀ _ hx.ne']
  ring

/-- Under weighted integrability above one, subtracting both `c * log x` and the
normalized endpoint error from the logarithmic progression sum leaves a term that tends to
`c + ∫ t in Ioi 1, (psiAP q a t - c * t) / t²`. If `psiAP q a x / x` tends to `c`, the
logarithmic sum centered by `c * log x` alone has the same limit. -/
theorem tendsto_logPsiAP_sub_mul_log_sub {q : ℕ} {a : ZMod q} {c : ℝ}
    (h : IntegrableOn (fun t : ℝ ↦ (psiAP q a t - c * t) / t ^ 2) (Ioi 1)) :
    Tendsto (fun x : ℝ ↦ logPsiAP q a x - c * Real.log x - (psiAP q a x / x - c)) atTop
      (𝓝 (c + ∫ t in Ioi (1 : ℝ), (psiAP q a t - c * t) / t ^ 2)) := by
  have htail : Tendsto (fun x : ℝ ↦ ∫ t in Ioi x, (psiAP q a t - c * t) / t ^ 2)
      atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  rw [← sub_zero (c + ∫ t in Ioi (1 : ℝ), (psiAP q a t - c * t) / t ^ 2)]
  refine (htail.const_sub _).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [logPsiAP_eq_mul_log_add_sub_integral hx h, sub_div, mul_div_cancel_right₀ _ hx.ne']
  ring

/-- For positive `x`, the inclusive sum of `Λ(n)/n` up to `x` equals `log x - γ` plus
the endpoint Chebyshev error divided by `x`, less the integral of that error against
`dt/t²` above `x`. This is the exact remainder used by Ramaré (2013). -/
theorem sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n =
      Real.log x - Real.eulerMascheroniConstant + (ψ x - x) / x -
        ∫ t in Ioi x, (ψ t - t) / t ^ 2 := by
  have heq := logPsiAP_eq_mul_log_add_sub_integral (q := 1) (a := 0) (c := 1) hx
  simp only [logPsiAP_one, psiAP_one, one_mul, integral_psi_sub_div_sq] at heq
  linear_combination heq (integrableOn_psi_sub_div_sq zero_lt_one)

/-- The inclusive sum of `Λ(n)/n` up to `x`, less `log x`, tends to Euler's constant
with a negative sign (the constant in Ramaré's 2013 estimates). -/
theorem tendsto_sum_vonMangoldt_div_sub_log :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hlim := tendsto_logPsiAP_sub_mul_log_sub (q := 1) (a := 0) (c := 1)
  simp only [logPsiAP_one, psiAP_one, one_mul, integral_psi_sub_div_sq] at hlim
  have h := (hlim (integrableOn_psi_sub_div_sq zero_lt_one)).add
    (tendsto_psi_div_atTop.sub_const 1)
  have hc : 1 + (-Real.eulerMascheroniConstant - 1) = -Real.eulerMascheroniConstant := by ring
  simpa only [sub_self, add_zero, sub_add_cancel, hc] using h

end Chebyshev
