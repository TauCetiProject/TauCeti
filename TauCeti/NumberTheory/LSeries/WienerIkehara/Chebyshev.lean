/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.WienerIkehara.BoundaryGrowth
import TauCeti.Analysis.Asymptotics.SumWindow
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.NonnegTestFunction
import TauCeti.NumberTheory.LSeries.Positivity

/-!
# The Chebyshev bound behind Wiener--Ikehara

For nonnegative coefficients `a` whose Dirichlet series has the Wiener--Ikehara boundary data
(summability on `Re s > 1` and a remainder `G = LSeries a - A / (s - 1)` continuous on
`Re s ≥ 1`), the partial sums grow at most linearly:
`∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)`.

This is the Chebyshev-type bound that the Tauberian half of Wiener--Ikehara consumes to control
the tails of its test functions. It is derived from the boundary data and nonnegativity alone,
improving the crude `O(t log t)` bound `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`.

The argument has two steps.

* **A window bound.** Choose a smooth compactly supported test function `psi` whose Fourier
  transform is nonnegative, and at least some `c > 0` on a neighbourhood `|v| < η` of the origin
  (`TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`). The smoothed asymptotic
  `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` bounds the Fourier-weighted
  series `∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for large `x`. All of its summands are
  nonnegative, and those with `q x < n ≤ x`, where `q = exp (-π η)`, carry a weight at least
  `c / x`. Hence `∑_{q x < n ≤ x} ‖a n‖ ≤ K x`.
* **Summing the windows.** A window bound with a fixed ratio `q < 1` implies linear growth of the
  partial sums, by peeling off the window `(q x, x]` and recursing on `q x`
  (`TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`).

## Main results

* `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`: **the Chebyshev bound**
  `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)` for nonnegative coefficients with Wiener--Ikehara boundary data.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

open Asymptotics Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff Topology

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

/-- If `exp (-(π η)) x < n ≤ x`, the frequency `log (n / x) / 2π` lies within `η` of `0`. -/
private theorem dist_mul_log_div_lt {η x : ℝ} {n : ℕ} (hx : 0 < x)
    (hqn : Real.exp (-(π * η)) * x < n) (hnx : (n : ℝ) ≤ x) :
    dist (1 / (2 * π) * Real.log (n / x)) 0 < η := by
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hqn
  have hlog_le : Real.log (n / x) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hx).2 hnx)
  have hlog_ge : -(π * η) < Real.log (n / x) := by
    rw [← Real.log_exp (-(π * η))]
    exact Real.log_lt_log (by positivity) (by rw [lt_div_iff₀ hx]; exact hqn)
  have hη : 0 < η := by nlinarith [Real.pi_pos]
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hpi.le hlog_le)]
  have h1 := mul_lt_mul_of_pos_left hlog_ge hpi
  have h2 : 1 / (2 * π) * -(π * η) = -(η / 2) := by
    field_simp
  linarith

/-- For nonnegative coefficients with Wiener--Ikehara boundary data, the Fourier-weighted series
tested against a smooth compactly supported function converges at every scale `x > 0`. -/
private theorem summable_term_mul_fourier_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) {psi : ℝ → ℂ}
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ ↦
      _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)) := by
  have hGseg : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2) :=
    hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1
  have h := LSeriesSummable_mul_fourier_of_nonneg ha hGseg
    (fun sigma h1 _ ↦ hG' sigma (by simpa using h1)) (fun sigma h1 _ ↦ hsum sigma h1)
    hpsi hsupp hx
  refine h.congr fun n ↦ ?_
  by_cases hn : n = 0
  · simp [_root_.LSeries.term, hn]
  · simp only [_root_.LSeries.term, hn, ite_false]
    ring

/-- The window bound: nonnegative coefficients with Wiener--Ikehara boundary data have
`∑_{q x < n ≤ x} ‖a n‖ ≤ K x` for all large `x`, for some ratio `0 < q < 1` and constant `K`. -/
private theorem exists_eventually_sum_Ioc_norm_le_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) :
    ∃ q K : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ x : ℝ in atTop, ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, ‖a n‖ ≤ K * x := by
  obtain ⟨psi, hpsi, hsupp, hnn, hpos⟩ :=
    TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg (V := ℝ)
  -- The Fourier transform of `psi` is at least `c > 0` on `|v| < η`.
  set c : ℝ := (𝓕 psi 0).re / 2 with hc
  have hc0 : 0 < c := half_pos (Complex.pos_iff.1 hpos).1
  have hcont : Continuous fun v : ℝ ↦ (𝓕 psi v).re :=
    Complex.continuous_re.comp (TauCeti.continuous_fourier_of_integrable
      (hpsi.continuous.integrable_of_hasCompactSupport hsupp))
  obtain ⟨η, hη, hηc⟩ := Metric.eventually_nhds_iff.1
    (hcont.continuousAt.eventually (lt_mem_nhds (by linarith : c < (𝓕 psi 0).re)))
  -- The smoothed series is eventually bounded by `M`.
  have hT := tendsto_tsum_term_mul_fourier_atTop_of_nonneg ha hG hG' hsum hpsi hsupp
  set M : ℝ := ‖2 * (π : ℂ) * A * psi 0‖ + 1 with hM
  have hbound := hT.norm.eventually (gt_mem_nhds (by linarith : ‖2 * (π : ℂ) * A * psi 0‖ < M))
  set q : ℝ := Real.exp (-(π * η))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  refine ⟨q, M / c, hq0, hq1, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hxM hx
  set F : ℕ → ℂ := fun n ↦ 𝓕 psi (1 / (2 * π) * Real.log (n / x))
  set u : ℕ → ℂ := fun n ↦ _root_.LSeries.term a 1 n * F n
  have hunn : ∀ n, 0 ≤ u n := fun n ↦
    mul_nonneg (by simpa using _root_.LSeries.term_nonneg (ha n) 1) (hnn _)
  have husum : Summable u := summable_term_mul_fourier_of_nonneg ha hG hG' hsum hpsi hsupp hx
  have hre_sum : Summable fun n ↦ (u n).re := Complex.reCLM.summable husum
  -- Each summand in the window `(q x, x]` has real part at least `c / x * ‖a n‖`.
  have hwin : ∀ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, c / x * ‖a n‖ ≤ (u n).re := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn2).trans (Nat.floor_le hx.le)
    have hqn : q * x < n := Nat.lt_of_floor_lt hn1
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by positivity
    have hv := dist_mul_log_div_lt hx hqn hnx
    have hFn : c < (F n).re := hηc hv
    have hterm : _root_.LSeries.term a 1 n = ((‖a n‖ / n : ℝ) : ℂ) := by
      rw [_root_.LSeries.term_of_ne_zero hn0, cpow_one]
      conv_lhs => rw [Complex.eq_coe_norm_of_nonneg (ha n)]
      push_cast
      ring
    simp only [u, hterm, Complex.re_ofReal_mul]
    calc c / x * ‖a n‖ = ‖a n‖ / x * c := by ring
      _ ≤ ‖a n‖ / n * c := by gcongr
      _ ≤ ‖a n‖ / n * (F n).re := by gcongr
  have hsum_le : ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, (u n).re ≤ M := by
    refine (hre_sum.sum_le_tsum _ fun n _ ↦ (Complex.nonneg_iff.1 (hunn n)).1).trans ?_
    rw [← Complex.re_tsum husum]
    exact (Complex.re_le_norm _).trans hxM.le
  have hmain : c / x * ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, ‖a n‖ ≤ M := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hwin).trans hsum_le
  rw [div_mul_eq_mul_div, div_le_iff₀ hx] at hmain
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  linarith

/-- **The Chebyshev bound.** Nonnegative coefficients whose Dirichlet series is summable on
`Re s > 1` and has a boundary remainder `G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`
satisfy `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)`. -/
theorem isBigO_sum_Icc_norm_id_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) :
    (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖a n‖) =O[atTop] fun t ↦ t := by
  obtain ⟨q, K, hq0, hq1, h⟩ := exists_eventually_sum_Ioc_norm_le_of_boundary ha hG hG' hsum
  exact isBigO_sum_Icc_of_sum_Ioc_floor_mul_le (fun n ↦ norm_nonneg (a n)) hq0.le hq1 h

end TauCeti.LSeries
