/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.BumpFunction.Basic
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Normalized smooth bumps on balls and scale-sharp Haar bounds

This file supplements Mathlib's `ContDiffBump.normed` API with set-integral formulas, half-space
integrals, and scale-sharp pointwise bounds against an additive Haar measure `μ`, and specializes
them to `(TauCeti.ballBump x₀ hρ).normed μ`, which is supported in
`Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ` and satisfies the scale-sharp bound
`‖(TauCeti.ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-finrank ℝ E)` with `C` independent of `x₀`
and `ρ`.

## Main results

* `ContDiffBump.setIntegral_normed`: for a locally finite measure `μ` positive on nonempty open
  sets, integrating `f.normed μ` over any superset of `Metric.closedBall c f.rOut` yields `1`.
* `ContDiffBump.setIntegral_normed_halfSpace`: integrating `f.normed μ` (for `f` centered at `0`)
  over the closed half-space `{y : E | 0 ≤ L y}` defined by any nonzero `L : E →L[ℝ] ℝ` yields
  `1 / 2`.
* `ContDiffBump.norm_normed_le`: explicit `O(f.rOut ^ (-finrank ℝ E))` pointwise bound on
  `f.normed μ` when `f.rOut ≤ K * f.rIn`.
* `TauCeti.tsupport_normed_ballBump_subset_ball`, `TauCeti.norm_normed_ballBump_le`,
  `TauCeti.exists_norm_normed_ballBump_le`: support containment inside `Metric.ball x₀ ρ` and
  explicit `O(ρ ^ (-finrank ℝ E))` pointwise bound for `(ballBump x₀ hρ).normed μ`.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set
open scoped ContDiff Topology

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- For a locally finite measure `μ` positive on nonempty open sets, integrating `f.normed μ` over
any set `s` containing `Metric.closedBall c f.rOut` yields `1`. -/
theorem setIntegral_normed {c : E} (f : ContDiffBump c) (μ : Measure E)
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {s : Set E} (hs : closedBall c f.rOut ⊆ s) :
    ∫ y in s, f.normed μ y ∂μ = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hys ↦
    image_eq_zero_of_notMem_tsupport (by rw [f.tsupport_normed_eq]; exact fun h ↦ hys (hs h))]
  exact f.integral_normed

section AddHaar

/-- Integrating `f.normed μ` (for any smooth bump `f` centered at `0`) over the closed half-space
`{y : E | 0 ≤ L y}` defined by any nonzero continuous linear functional `L : E →L[ℝ] ℝ` yields
`1 / 2`. -/
theorem setIntegral_normed_halfSpace (f : ContDiffBump (0 : E)) (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∫ y in {y : E | 0 ≤ L y}, f.normed μ y ∂μ = (1 : ℝ) / 2 := by
  simpa [f.integral_normed, one_div] using
    MeasureTheory.setIntegral_halfSpace_of_even (μ := μ) f.integrable_normed
      (fun y ↦ f.normed_neg y) hL

/-- Explicit `O(f.rOut ^ (-finrank ℝ E))` pointwise bound on `f.normed μ` with respect to an
additive Haar measure `μ` whenever `f.rOut ≤ K * f.rIn`. -/
theorem norm_normed_le {c : E} (f : ContDiffBump c) (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ℝ) (hK : f.rOut ≤ K * f.rIn) (y : E) :
    ‖f.normed μ y‖ ≤
      (K ^ finrank ℝ E / μ.real (closedBall (0 : E) 1)) * f.rOut ^ (-(finrank ℝ E : ℝ)) := by
  rw [Real.norm_of_nonneg (f.nonneg_normed y)]
  refine (f.normed_le_div_measure_closedBall_rOut μ K hK y).trans (le_of_eq ?_)
  rw [Measure.addHaar_real_closedBall' μ c f.rOut_pos.le, Real.rpow_neg f.rOut_pos.le,
    Real.rpow_natCast]
  ring

end AddHaar

end ContDiffBump

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)

/-- The topological support of `(ballBump x₀ hρ).normed μ` is contained in `Metric.ball x₀ ρ`. -/
theorem tsupport_normed_ballBump_subset_ball [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport ((ballBump x₀ hρ).normed μ) ⊆ ball x₀ ρ := by
  rw [(ballBump x₀ hρ).tsupport_normed_eq, ballBump_rOut]
  exact closedBall_subset_ball (half_lt_self hρ)

/-- Explicit `O(ρ ^ (-finrank ℝ E))` pointwise bound on `(ballBump x₀ hρ).normed μ` with respect to
an additive Haar measure `μ`, uniform in the center `x₀`, radius `ρ > 0`, and evaluation point
`y`. -/
theorem norm_normed_ballBump_le [μ.IsAddHaarMeasure] (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E) :
    ‖(ballBump x₀ hρ).normed μ y‖ ≤
      (4 ^ finrank ℝ E / μ.real (closedBall (0 : E) 1)) * ρ ^ (-(finrank ℝ E : ℝ)) := by
  refine ((ballBump x₀ hρ).norm_normed_le μ 2 (by simp; linarith) y).trans (le_of_eq ?_)
  rw [ballBump_rOut, Real.rpow_neg (by positivity), Real.rpow_neg hρ.le, Real.rpow_natCast,
    Real.rpow_natCast, div_pow, inv_div]
  have h4 : (4 : ℝ) ^ finrank ℝ E = (2 : ℝ) ^ finrank ℝ E * (2 : ℝ) ^ finrank ℝ E := by
    rw [← mul_pow]; norm_num
  rw [h4]
  ring

/-- Existential form of `norm_normed_ballBump_le`: there is a nonnegative constant `C`, depending
only on the ambient space and Haar measure `μ`, such that
`‖(ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-finrank ℝ E)`. -/
theorem exists_norm_normed_ballBump_le [μ.IsAddHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E),
      ‖(ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-(finrank ℝ E : ℝ)) :=
  ⟨4 ^ finrank ℝ E / μ.real (closedBall (0 : E) 1), by positivity, norm_normed_ballBump_le μ⟩

end TauCeti
