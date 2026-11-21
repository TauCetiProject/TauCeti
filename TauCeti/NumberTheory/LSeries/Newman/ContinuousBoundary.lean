/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Complex.PowerSeries.Fejer
import TauCeti.Analysis.LaplaceTransform.UniformStep
import TauCeti.NumberTheory.LSeries.Newman.Tauberian
import TauCeti.Topology.Order.OrderClosed

/-!
# Continuous boundary values do not force Laplace convergence

Newman's Tauberian theorem (`newmanLaplace_tendsto_integral`) requires a holomorphic continuation
across an open neighbourhood of the closed right half-plane `0 ≤ re z`. This file proves that
continuity up to the imaginary axis—even together with holomorphy on `0 < re z`, `|f t| ≤ 1`,
and `f t → 0`—does not suffice.

Taking Fejér's 1911 disc-algebra counterexample `(c, P)`
(`TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`), whose real coefficients
satisfy `|c n| ≤ 1`, `c n → 0`, and unbounded partial sums `∑ n ∈ range N, c n`, the unit step
function `f t = c ⌊t⌋₊` has `|f t| ≤ 1`, `f t → 0`, and a Laplace transform transferred from `P`
(`TauCeti.exists_continuousOn_integral_floor_div_mul_cexp_neg_mul`) that extends continuously to
`0 ≤ re z` and holomorphically to `0 < re z`. Yet at `T = N`,
`∫ t in 0..N, f t = ∑ n ∈ range N, c n` is unbounded above, so `∫ t in 0..T, f t` fails to
converge and no holomorphic continuation exists on any open set containing `{z | 0 ≤ z.re}`
(`exists_bounded_continuousOn_laplace_not_tendsto_intervalIntegral`).
-/

public section

open Filter MeasureTheory Set Complex
open scoped Topology

namespace TauCeti.LSeries

/-- **Continuous boundary values do not suffice for Newman's Tauberian theorem.** There exist a
measurable real function `f : ℝ → ℝ` with `|f t| ≤ 1` and `f t → 0` as `t → ∞`, and a function
`G : ℂ → ℂ` continuous on the closed right half-plane `0 ≤ re z` and holomorphic on `0 < re z`
where it agrees with the Laplace transform of `f`, such that:

* the truncated integrals `∫ t in 0..T, f t` are unbounded above and therefore converge to no
  limit `L : ℂ` as `T → ∞`;
* `G` admits no holomorphic continuation to any open neighbourhood of `{z | 0 ≤ z.re}`. -/
theorem exists_bounded_continuousOn_laplace_not_tendsto_intervalIntegral :
    ∃ (f : ℝ → ℝ) (G : ℂ → ℂ),
      Measurable f ∧
      (∀ t, |f t| ≤ 1) ∧
      Tendsto f atTop (𝓝 0) ∧
      ContinuousOn G {z : ℂ | 0 ≤ z.re} ∧
      DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), (f t : ℂ) * cexp (-z * t)) ∧
      (∀ B : ℝ, ∃ T : ℝ, 0 ≤ T ∧ B ≤ ∫ t in (0 : ℝ)..T, f t) ∧
      (∀ L : ℂ, ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, (f t : ℂ)) atTop (𝓝 L)) ∧
      (∀ (Ω : Set ℂ) (G' : ℂ → ℂ), IsOpen Ω → {z : ℂ | 0 ≤ z.re} ⊆ Ω →
        (∀ z : ℂ, 0 < z.re → G' z = G z) → ¬ DifferentiableOn ℂ G' Ω) := by
  obtain ⟨c, P, hc_bound, hc_zero, hP_cont, _, hP_sum, hc_unb⟩ :=
    exists_continuousOn_closedBall_hasSum_unbounded_sum_range
  set f : ℝ → ℝ := fun t ↦ c ⌊t⌋₊
  have hc_norm : ∀ n, ‖(c n : ℂ)‖ ≤ 1 := fun n ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hc_bound n
  obtain ⟨G, hG_cont, hG_diff, hG_eq⟩ :=
    exists_continuousOn_integral_floor_div_mul_cexp_neg_mul hc_norm one_pos hP_cont hP_sum
  have hmeas : Measurable f := measurable_from_nat.comp Nat.measurable_floor
  have hf_bound : ∀ t : ℝ, |f t| ≤ 1 := fun t ↦ hc_bound ⌊t⌋₊
  have hG_laplace : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), (f t : ℂ) * cexp (-z * t) := by
    intro z hz
    simpa [f] using hG_eq z hz
  have hint_nat (N : ℕ) : ∫ t in (0 : ℝ)..(N : ℝ), f t = ∑ n ∈ Finset.range N, c n := by
    have hstep := intervalIntegral_floor_div_mul_cexp_neg_mul (c := fun n ↦ (c n : ℂ)) one_pos N 0
    simp only [mul_one, div_one, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero] at hstep
    apply Complex.ofReal_injective
    simpa [f, intervalIntegral.integral_ofReal, Complex.ofReal_sum] using hstep
  have hnot : ∀ L : ℂ, ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, (f t : ℂ)) atTop (𝓝 L) := by
    intro L hL
    have hre : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, c n) atTop (𝓝 L.re) :=
      ((Complex.continuous_re.tendsto L).comp (hL.comp tendsto_natCast_atTop_atTop)).congr
        fun N ↦ by simp [intervalIntegral.integral_ofReal, hint_nat]
    exact TauCeti.not_tendsto_nhds_of_forall_exists_le hc_unb L.re hre
  refine ⟨f, G, hmeas, hf_bound, hc_zero.comp tendsto_nat_floor_atTop, hG_cont, hG_diff,
    hG_laplace, fun B ↦ ?_, hnot, fun Ω G' hΩ hsub heq hG' ↦ ?_⟩
  · obtain ⟨N, hN⟩ := hc_unb B
    exact ⟨N, Nat.cast_nonneg N, (hint_nat N).symm ▸ hN⟩
  · exact hnot (G' 0) (newmanLaplace_tendsto_integral
      (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable
      (fun t _ ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using hf_bound t)
      hΩ hsub hG' fun z hz ↦ (heq z hz).trans (hG_laplace z hz))

end TauCeti.LSeries
