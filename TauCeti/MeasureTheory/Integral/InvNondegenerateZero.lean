/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local integrability of `1 / f` at nondegenerate zeros

Let `E` be a finite-dimensional real normed space of dimension `n ≥ 2` with an additive Haar
measure `μ`, and let `f : E → ℂ`. If `f` vanishes at `x₀` and is differentiable there with an
injective real derivative `L`, then `‖L h‖ ≥ m ‖h‖` for some `m > 0`, so
`‖f(x₀ + h)‖ ≥ (m / 2) ‖h‖` for small `h`, and `1 / f` is bounded near `x₀` by a multiple of
`‖x − x₀‖⁻¹`, which is integrable near `x₀` because `1 < n`
(`TauCeti.integrableAtFilter_inv_of_hasFDerivAt`). Consequently, a continuous `f` whose zeros all
have injective derivatives has a locally integrable inverse
(`TauCeti.locallyIntegrable_inv_of_hasFDerivAt`). Here `(f x)⁻¹ = 0` where `f x = 0`.
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set Module
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **`1 / f` is integrable near a nondegenerate zero.** In dimension `n ≥ 2`, if `f : E → ℂ`
vanishes at `x₀` and has an injective real derivative there, then `1 / f` is integrable on a
neighbourhood of `x₀`. -/
theorem integrableAtFilter_inv_of_hasFDerivAt (hE : 2 ≤ finrank ℝ E) {f : E → ℂ}
    {L : E →L[ℝ] ℂ} {x₀ : E} (hf : HasFDerivAt f L x₀) (h0 : f x₀ = 0) (hL : Function.Injective L)
    (hmeas : AEStronglyMeasurable (fun x => (f x)⁻¹) μ) :
    IntegrableAtFilter (fun x => (f x)⁻¹) (𝓝 x₀) μ := by
  -- A lower bound `‖L h‖ ≥ m ‖h‖`.
  obtain ⟨K, hK0, hK⟩ := (L : E →ₗ[ℝ] ℂ).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hL)
  set m : ℝ := (K : ℝ)⁻¹
  have hm : 0 < m := inv_pos.2 (by exact_mod_cast hK0)
  have hLm (h : E) : m * ‖h‖ ≤ ‖L h‖ := by
    have := hK.le_mul_dist h 0
    simp only [dist_zero_right, ContinuousLinearMap.coe_coe, map_zero] at this
    rw [inv_mul_le_iff₀ (by exact_mod_cast hK0)]
    exact this
  -- Near `x₀`, `‖f x‖ ≥ (m / 2) ‖x − x₀‖`.
  have hlo := hf.isLittleO.def (half_pos hm)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlo
  have hlower (y : E) (hy : y ∈ ball (0 : E) r) : m / 2 * ‖y‖ ≤ ‖f (x₀ + y)‖ := by
    have h := hball (x₀ + y) (by simpa [dist_eq_norm] using hy)
    simp only [h0, sub_zero, add_sub_cancel_left] at h
    have h2 := norm_sub_norm_le (L y) (L y - f (x₀ + y))
    rw [sub_sub_cancel] at h2
    have h3 : ‖L y - f (x₀ + y)‖ ≤ m / 2 * ‖y‖ := by rwa [norm_sub_rev]
    linarith [hLm y]
  -- Hence `‖1 / f(x₀ + y)‖ ≤ (2 / m) ‖y‖⁻¹` on the ball.
  have hdecay : ∀ y ∈ ball (0 : E) r, ‖(f (x₀ + y))⁻¹‖ ≤ 2 / m * ‖y‖ ^ (-(1 : ℝ)) := by
    intro y hy
    rw [Real.rpow_neg_one, norm_inv]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [h0]
    have hpos : 0 < m / 2 * ‖y‖ := mul_pos (half_pos hm) (norm_pos_iff.2 hy0)
    calc ‖f (x₀ + y)‖⁻¹ ≤ (m / 2 * ‖y‖)⁻¹ := inv_anti₀ hpos (hlower y hy)
      _ = 2 / m * ‖y‖⁻¹ := by field_simp
  have hmp : MeasurePreserving (x₀ + ·) μ μ := measurePreserving_add_left μ x₀
  have hint : IntegrableOn (fun y => (f (x₀ + y))⁻¹) (ball 0 r) μ := by
    refine integrableOn_ball_of_norm_le_rpow (by omega) (α := 1)
      (by exact_mod_cast (show 1 < finrank ℝ E by omega))
      ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hdecay)) ?_
    exact hmeas.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have hpre : (x₀ + ·) ⁻¹' ball x₀ r = ball (0 : E) r := by
    ext y
    simp [dist_eq_norm]
  refine ⟨ball x₀ r, ball_mem_nhds x₀ hr, ?_⟩
  rw [← hmp.integrableOn_comp_preimage (MeasurableEquiv.addLeft x₀).measurableEmbedding, hpre]
  exact hint

/-- **`1 / f` is locally integrable when every zero is nondegenerate.** In dimension `n ≥ 2`, if
`f : E → ℂ` is continuous and has an injective real derivative at each of its zeros, then `1 / f`
is locally integrable. -/
theorem locallyIntegrable_inv_of_hasFDerivAt (hE : 2 ≤ finrank ℝ E) {f : E → ℂ}
    (hf : Continuous f)
    (hzero : ∀ x, f x = 0 → ∃ L : E →L[ℝ] ℂ, HasFDerivAt f L x ∧ Function.Injective L) :
    LocallyIntegrable (fun x => (f x)⁻¹) μ := by
  have hmeas : AEStronglyMeasurable (fun x => (f x)⁻¹) μ :=
    (hf.measurable.inv).aestronglyMeasurable
  intro x
  by_cases hx : f x = 0
  · obtain ⟨L, hL, hinj⟩ := hzero x hx
    exact integrableAtFilter_inv_of_hasFDerivAt hE hL hx hinj hmeas
  · exact (hf.continuousAt.inv₀ hx).integrableAtFilter ⟨univ, univ_mem, hmeas.restrict⟩
      (μ.finiteAt_nhds x)

end TauCeti
