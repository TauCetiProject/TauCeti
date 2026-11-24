/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.Analysis.MellinTransform.Sawtooth
import TauCeti.Analysis.SpecialFunctions.Pow.AtTop
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin

/-!
# Partial-sum asymptotics of the Riemann zeta function in the right half-plane

For `0 < Re s` and `s ≠ 1`, cutting the first-order Euler–Maclaurin formula
(`TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast`) at `N ≥ 1` expresses the difference
between the Dirichlet partial sum `∑ n ∈ Icc 1 N, n ^ (-s)` and the polar main term
`N ^ (1 - s) / (1 - s)` as `riemannZeta s` plus an `O(N ^ (-Re s))` remainder. Consequently both
`(∑ n ∈ Icc 1 N, n ^ (-s)) - N ^ (1 - s) / (1 - s)` and the shifted-cutoff variant with
`(N + 1) ^ (1 - s) / (1 - s)` converge to `riemannZeta s` as `N → ∞`.

## Main results

* `TauCeti.tendsto_sum_Icc_cpow_neg_sub_riemannZeta`:
  `(∑ n ∈ Icc 1 N, n ^ (-s)) - N ^ (1 - s) / (1 - s) → riemannZeta s` for `0 < Re s`, `s ≠ 1`.
* `TauCeti.tendsto_sum_Icc_cpow_neg_sub_succ_riemannZeta`:
  `(∑ n ∈ Icc 1 N, n ^ (-s)) - (N + 1) ^ (1 - s) / (1 - s) → riemannZeta s` for `0 < Re s`,
  `s ≠ 1`.

## References

* G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge University Press,
  1915.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- **Partial-sum asymptotic of `riemannZeta` on `0 < Re s`, `s ≠ 1`.** For every `s` in the right
half-plane `0 < Re s` other than the pole `s = 1`,
`(∑ n ∈ Icc 1 N, n ^ (-s)) - N ^ (1 - s) / (1 - s)` converges to `riemannZeta s` as `N → ∞`. -/
theorem tendsto_sum_Icc_cpow_neg_sub_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) -
      (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) := by
  have hbd : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-s) / 2) atTop (𝓝 0) := by
    simpa using (Complex.tendsto_natCast_cpow_neg_atTop hs).div_const (2 : ℂ)
  have htail : Tendsto (fun N : ℕ ↦ s * ∫ x in Set.Ioi (N : ℝ),
      (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ ↦ ‖s‖ * ((N : ℝ) ^ (-s.re) / (2 * s.re))) atTop (𝓝 0) := by
      simpa using (((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).div_const
        (2 * s.re)).const_mul ‖s‖
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_sawtooth_mul_cpow_le (Nat.cast_pos.mpr hN) hs) (norm_nonneg s)
  have hlim : Tendsto (fun N : ℕ ↦ riemannZeta s + (N : ℂ) ^ (-s) / 2 +
      s * ∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)))
      atTop (𝓝 (riemannZeta s)) := by
    simpa using (tendsto_const_nhds.add hbd).add htail
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hEM := riemannZeta_eq_sum_add_integral_sawtooth_natCast (Nat.one_le_iff_ne_zero.mp hN) hs hs₁
  have hpole : (N : ℂ) ^ (1 - s) / (s - 1) = -((N : ℂ) ^ (1 - s) / (1 - s)) := by
    rw [← div_neg, neg_sub]
  rw [hpole] at hEM
  linear_combination hEM

/-- **Partial-sum asymptotic of `riemannZeta` on `0 < Re s`, `s ≠ 1` (shifted cutoff `N + 1`).** -/
theorem tendsto_sum_Icc_cpow_neg_sub_succ_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) -
      (N + 1 : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 (riemannZeta s)) := by
  have hshift : Tendsto (fun N : ℕ ↦ ((N + 1 : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_natCast_add_one_cpow_sub_atTop (z := 1 - s) (by simp [hs])).div_const (1 - s)
  have h := (tendsto_sum_Icc_cpow_neg_sub_riemannZeta hs hs₁).sub hshift
  rw [sub_zero] at h
  refine h.congr fun N ↦ ?_
  ring

end TauCeti
