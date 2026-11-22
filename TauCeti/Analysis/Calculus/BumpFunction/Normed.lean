/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.BumpFunction.Basic
public import TauCeti.MeasureTheory.Measure.Comap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Integrals and bounds against normalized smooth bumps

Let `f` be a smooth bump centred at `c` in a finite-dimensional real normed space. Its normalized
form `f.normed μ` is continuous with compact support, so it makes every continuous function
integrable. Since it vanishes off the closed ball of radius `f.rOut` around `c`, an integral against
it may be taken over that compact ball, with the pullback of `μ`, which is a finite measure. There
`f.normed μ` still has integral one and averages constants to themselves.

This file also supplements Mathlib's `ContDiffBump.normed` API with set-integral formulas,
half-space integrals, and scale-sharp pointwise bounds against an additive Haar measure `μ`, and
specializes them to `(TauCeti.ballBump x₀ hρ).normed μ`, which is supported in
`Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ` and satisfies the scale-sharp bound
`‖(TauCeti.ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-finrank ℝ E)` with `C` independent of `x₀`
and `ρ`.

## Main declarations

* `ContDiffBump.integrable_normed_smul`: bump-weighted continuous functions are integrable.
* `ContDiffBump.integral_closedBall_normed_smul`: bump-weighted integrals over the closed ball of
  radius `f.rOut` are integrals over the whole space.
* `ContDiffBump.integral_closedBall_normed_smul_const`: over that closed ball, the normalized bump
  averages a constant to itself.
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

section Comap

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {c : E} (f : ContDiffBump c) (μ : Measure E) [IsLocallyFiniteMeasure μ]
  [μ.IsOpenPosMeasure]

/-- Bump-weighted continuous functions are integrable. -/
theorem integrable_normed_smul {g : E → G} (hg : Continuous g) :
    Integrable (fun x ↦ f.normed μ x • g x) μ :=
  (f.continuous_normed.smul hg).integrable_of_hasCompactSupport
    f.hasCompactSupport_normed.smul_right

/-- An integral against a normalized bump over the closed ball of radius `f.rOut`, with the
pullback of `μ`, is the integral over the whole space. -/
theorem integral_closedBall_normed_smul (g : E → G) :
    ∫ x : closedBall c f.rOut, f.normed μ x • g x ∂(μ.comap (↑)) =
      ∫ x, f.normed μ x • g x ∂μ := by
  rw [integral_subtype_comap measurableSet_closedBall (fun x ↦ f.normed μ x • g x)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (f := f.normed μ) (by rwa [f.tsupport_normed_eq]),
      zero_smul]

/-- A normalized bump has integral one over the closed ball of radius `f.rOut`. -/
theorem integral_closedBall_normed :
    ∫ x : closedBall c f.rOut, f.normed μ x ∂(μ.comap (↑)) = 1 := by
  have h := f.integral_closedBall_normed_smul μ (fun _ ↦ (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [h, f.integral_normed]

omit [μ.IsOpenPosMeasure] in
/-- Bump-weighted constants are integrable over the closed ball of radius `f.rOut`. -/
theorem integrable_closedBall_normed_smul_const (z : G) :
    Integrable (fun x : closedBall c f.rOut ↦ f.normed μ x • z) (μ.comap (↑)) :=
  ((f.continuous_normed.comp continuous_subtypeVal).smul continuous_const)
    |>.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- Over the closed ball of radius `f.rOut`, a normalized bump averages a constant to itself. -/
theorem integral_closedBall_normed_smul_const [CompleteSpace G] (z : G) :
    ∫ x : closedBall c f.rOut, f.normed μ x • z ∂(μ.comap (↑)) = z := by
  rw [integral_smul_const, f.integral_closedBall_normed, one_smul]

end Comap

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
  rw [Real.norm_of_nonneg ((ballBump x₀ hρ).nonneg_normed y)]
  refine ((ballBump x₀ hρ).normed_le_div_measure_closedBall_rIn μ y).trans (le_of_eq ?_)
  rw [ballBump_rIn, Measure.addHaar_real_closedBall' μ x₀ (by positivity),
    Real.rpow_neg hρ.le, Real.rpow_natCast, div_pow, one_div, mul_inv, inv_div]
  ring

/-- Existential form of `norm_normed_ballBump_le`: there is a nonnegative constant `C`, depending
only on the ambient space and Haar measure `μ`, such that
`‖(ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-finrank ℝ E)`. -/
theorem exists_norm_normed_ballBump_le [μ.IsAddHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E),
      ‖(ballBump x₀ hρ).normed μ y‖ ≤ C * ρ ^ (-(finrank ℝ E : ℝ)) :=
  ⟨4 ^ finrank ℝ E / μ.real (closedBall (0 : E) 1), by positivity, norm_normed_ballBump_le μ⟩

end TauCeti
