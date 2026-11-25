/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
import TauCeti.Analysis.Complex.PowerSeries.Fejer
import TauCeti.Analysis.SpecificLimits.Cesaro.Basic
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.BlockCoefficients
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint
import TauCeti.Topology.Order.OrderClosed

/-!
# Continuous boundary values do not force Dirichlet convergence at `s = 1`

The bounded Dirichlet endpoint theorem (`boundedDirichlet_tendsto_ordered_at_one`) requires a
holomorphic continuation across an open neighbourhood of the closed half-plane `1 ≤ re s`. This
file proves that continuity up to the boundary line `re s = 1`—even together with holomorphy on
`1 < re s`, vanishing coefficients `a n → 0`, and vanishing Cesàro mean—does not suffice.

Taking Fejér's 1911 disc-algebra counterexample `(c, P)`
(`TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`) with base `b = 2` and
setting `a n = c (Nat.log 2 n)` (`n ≥ 1`, `a 0 = 0`), the block transfer
(`exists_continuousOn_LSeries_natLog`) and harmonic unboundedness
(`unbounded_sum_Icc_natLog_div`) in
`TauCeti.NumberTheory.LSeries.BoundaryConvergence.BlockCoefficients` produce a function
`F` continuous on `1 ≤ re s` and holomorphic on `1 < re s` agreeing with `LSeries a s`, while the
ordered harmonic partial sums `∑ n ∈ Icc 1 N, a n / n` are unbounded above and therefore converge to
no limit `L : ℂ` (`exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div`).

## References

* L. Fejér, *Sur les singularités de la série de Fourier des fonctions continues*, Ann. Sci.
  École Norm. Sup. (3) 28 (1911), 63–104.
* J. Korevaar, *Tauberian Theory: A Century of Developments*, Ch. III.
* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
-/

public section

open Filter MeasureTheory Set Metric Complex
open scoped Topology

namespace TauCeti.LSeries

/-- **Continuous boundary values do not suffice for bounded Dirichlet series at `s = 1`.**
There exist real coefficients `a : ℕ → ℝ` with `a 0 = 0`, `|a n| ≤ 1`, `a n → 0`, and vanishing
Cesàro mean `x⁻¹ * ∑ n ∈ Icc 1 ⌊x⌋₊, a n → 0`, together with a function `F : ℂ → ℂ` continuous on
the closed half-plane `1 ≤ re s` and holomorphic on `1 < re s` satisfying
`LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s)` for `1 < re s`, such that:

* the ordered harmonic partial sums `∑ n ∈ Icc 1 N, a n / n` are unbounded above and therefore
  converge to no limit `L : ℂ` as `N → ∞`;
* `F` admits no holomorphic continuation to any open neighbourhood of `{s | 1 ≤ s.re}`.

In particular, continuous boundary data on `re s = 1`—even alongside the vanishing mean value of
Wiener–Ikehara—cannot replace the open-neighbourhood analytic continuation in
`boundedDirichlet_tendsto_ordered_at_one`. -/
theorem exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div :
    ∃ (a : ℕ → ℝ) (F : ℂ → ℂ),
      a 0 = 0 ∧
      (∀ n, |a n| ≤ 1) ∧
      Tendsto a atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) ∧
      ContinuousOn F {s : ℂ | 1 ≤ s.re} ∧
      DifferentiableOn ℂ F {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s)) ∧
      (∀ B : ℝ, ∃ N : ℕ, B ≤ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) ∧
      (∀ L : ℂ, ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) / (n : ℂ))
        atTop (𝓝 L)) ∧
      (∀ (Ω : Set ℂ) (F' : ℂ → ℂ), IsOpen Ω → {s : ℂ | 1 ≤ s.re} ⊆ Ω →
        (∀ s : ℂ, 1 < s.re → F' s = F s) → ¬ DifferentiableOn ℂ F' Ω) := by
  obtain ⟨c, P, hc_bound, hc_zero, hP_cont, _, hP_sum, hc_unb⟩ :=
    exists_continuousOn_closedBall_hasSum_unbounded_sum_range
  set a : ℕ → ℝ := fun n ↦ if n = 0 then 0 else c (Nat.log 2 n)
  have ha0 : a 0 = 0 := by simp [a]
  have ha_bound : ∀ n, |a n| ≤ 1 := fun n ↦ by
    by_cases hn : n = 0 <;> simp [a, hn, hc_bound]
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    have hlog : Tendsto (Nat.log 2) atTop atTop :=
      tendsto_atTop_atTop.mpr fun K ↦ ⟨2 ^ K, fun _ hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩
    refine (hc_zero.comp hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [a, Nat.one_le_iff_ne_zero.mp hn]
  have hmean : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using tendsto_inv_smul_sum_Icc_floor ha_zero
  have hc_norm : ∀ n, ‖(c n : ℂ)‖ ≤ 1 := fun n ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hc_bound n
  obtain ⟨F, hF_cont, hF_diff, hF_series'⟩ :=
    exists_continuousOn_LSeries_natLog one_lt_two hc_norm hP_cont hP_sum
  have hF_series : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s) :=
    fun s hs ↦ (LSeriesHasSum_congr s (F s) fun {n} hn ↦ by simp [a, hn]).mpr
      (hF_series' s hs)
  have hunb_raw := unbounded_sum_Icc_natLog_div one_lt_two hc_bound hc_unb
  have hsum_eq (N : ℕ) :
      ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) = ∑ n ∈ Finset.Icc 1 N, c (Nat.log 2 n) / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [a, Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
  have hunb : ∀ B : ℝ, ∃ N : ℕ, B ≤ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) := fun B ↦ by
    obtain ⟨N, hN⟩ := hunb_raw B
    exact ⟨N, (hsum_eq N).symm ▸ hN⟩
  have hnot : ∀ L : ℂ, ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) / (n : ℂ))
      atTop (𝓝 L) :=
    fun _ ↦ TauCeti.not_tendsto_nhds_of_continuousAt_comp_eq Complex.continuous_re.continuousAt
      (fun N ↦ by simp only [Complex.re_sum, Complex.div_natCast_re, Complex.ofReal_re])
      hunb
  refine ⟨a, F, ha0, ha_bound, ha_zero, hmean, hF_cont, hF_diff, hF_series, hunb, hnot,
    fun Ω F' hΩ hsub heq hF' ↦ ?_⟩
  exact hnot (F' 1) (boundedDirichlet_tendsto_ordered_at_one
    (fun n _ ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using ha_bound n)
    hΩ hsub hF' fun s hs ↦ (heq s hs).symm ▸ hF_series s hs)

end TauCeti.LSeries
