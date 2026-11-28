/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.NumberTheory.Chebyshev.LogPsiAP
import TauCeti.NumberTheory.Chebyshev.WeightedError

/-!
# The weighted tail in the von Mangoldt form of Mertens' theorem

`Chebyshev.sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add` expresses the
error in the sum of `Λ(n) / n` as an endpoint value and an absolutely convergent tail of
`ψ(t) - t`. It combines the Abel identity `Chebyshev.logPsiAP_eq_psiAP_div_add_integral`
at modulus one with `Chebyshev.integral_psi_sub_div_sq`.
`Chebyshev.tendsto_sum_vonMangoldt_div_sub_log` uses Mathlib's prime number theorem
`Chebyshev.tendsto_psi_div_atTop` to identify the limiting constant as `-γ`.

## References

* O. Ramaré, *Explicit estimates for the summatory function of Λ(n)/n from the one of Λ(n)*,
  Acta Arith. 159 (2013).
-/

public section

open ArithmeticFunction Filter Finset MeasureTheory Set
open scoped Chebyshev Topology

namespace Chebyshev

/-- For positive `x`, the inclusive sum of `Λ(n)/n` up to `x` equals `log x - γ` plus
the endpoint Chebyshev error divided by `x`, less the integral of that error against
`dt/t²` above `x`. This is the exact remainder used by Ramaré (2013). -/
theorem sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n =
      Real.log x - Real.eulerMascheroniConstant + (ψ x - x) / x -
        ∫ t in Ioi x, (ψ t - t) / t ^ 2 := by
  have hAbel : (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) =
      ψ x / x + ∫ t in (1 : ℝ)..x, ψ t / t ^ 2 := by
    simpa only [logPsiAP_one, psiAP_one] using
      logPsiAP_eq_psiAP_div_add_integral 1 0 x
  have hE : IntervalIntegrable (fun t : ℝ ↦ (ψ t - t) / t ^ 2) volume 1 x :=
    intervalIntegrable_iff.mpr
      ((integrableOn_psi_sub_div_sq (lt_min zero_lt_one hx)).mono_set fun _ ht ↦ ht.1)
  have hne {t : ℝ} (ht : t ∈ uIcc 1 x) : t ≠ 0 :=
    ne_of_mem_of_not_mem ht (notMem_uIcc_of_lt zero_lt_one hx)
  have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 1 x :=
    (continuousOn_inv₀.mono fun _ ht ↦ mem_compl_singleton_iff.mpr (hne ht)).intervalIntegrable
  have hlog : (∫ t in (1 : ℝ)..x, t⁻¹) = Real.log x := by
    simpa only [div_one] using integral_inv_of_pos zero_lt_one hx
  have hsplit : (∫ t in (1 : ℝ)..x, ψ t / t ^ 2) =
      (∫ t in (1 : ℝ)..x, (ψ t - t) / t ^ 2) + Real.log x := by
    rw [← hlog, ← intervalIntegral.integral_add hE hinv]
    exact intervalIntegral.integral_congr fun t ht ↦ by
      have ht₀ : t ≠ 0 := hne ht
      field
  have htail := intervalIntegral.integral_Ioi_sub_Ioi'
    (integrableOn_psi_sub_div_sq zero_lt_one) (integrableOn_psi_sub_div_sq hx)
  rw [hAbel, hsplit, ← htail, integral_psi_sub_div_sq]
  rw [sub_div, div_self hx.ne']
  ring

/-- The inclusive sum of `Λ(n)/n` up to `x`, less `log x`, tends to Euler's constant
with a negative sign (the constant in Ramaré's 2013 estimates). -/
theorem tendsto_sum_vonMangoldt_div_sub_log :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have htail : Tendsto (fun x : ℝ ↦ ∫ t in Ioi x, (ψ t - t) / t ^ 2) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hlim : Tendsto (fun x : ℝ ↦
      -Real.eulerMascheroniConstant + (ψ x / x - 1) - ∫ t in Ioi x, (ψ t - t) / t ^ 2)
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    simpa only [sub_self, add_zero, sub_zero] using
      ((tendsto_psi_div_atTop.sub_const (1 : ℝ)).const_add
        (-Real.eulerMascheroniConstant)).sub htail
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add hx, sub_div, div_self hx.ne']
  ring

end Chebyshev
