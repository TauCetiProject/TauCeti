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
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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

The measure `f.normedMeasure μ` with density `f.normed μ` against `μ` is a probability measure
concentrated on that closed ball, and integrating against it is integrating against `f.normed μ`.

As the outer radius tends to zero, the value of the normalized bump at its centre tends to
infinity, since its integral is one over a ball of vanishing measure.

## Main declarations

* `ContDiffBump.integrable_normed_smul`: bump-weighted continuous functions are integrable.
* `ContDiffBump.integral_closedBall_normed_smul`: bump-weighted integrals over the closed ball of
  radius `f.rOut` are integrals over the whole space.
* `ContDiffBump.integral_closedBall_normed_smul_const`: over that closed ball, the normalized bump
  averages a constant to itself.
* `ContDiffBump.normedMeasure`: the probability measure with density `f.normed μ`, with
  `ContDiffBump.integral_normedMeasure`, `ContDiffBump.integrable_normedMeasure_iff` and
  `ContDiffBump.ae_mem_closedBall_normedMeasure`.
* `ContDiffBump.tendsto_normed_center_atTop`: normalized bumps with outer radii tending to zero
  tend to infinity at their centre.
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

open Filter MeasureTheory Metric Module Set
open scoped ContDiff Topology

namespace ContDiffBump

section

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

/-- The probability measure with density `f.normed μ` against `μ`. -/
noncomputable def normedMeasure : Measure E :=
  μ.withDensity fun x ↦ ENNReal.ofReal (f.normed μ x)

instance : IsProbabilityMeasure (f.normedMeasure μ) :=
  ⟨by rw [normedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal f.integrable_normed (ae_of_all _ f.nonneg_normed),
    f.integral_normed, ENNReal.ofReal_one]⟩

omit [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- Integrating against `f.normedMeasure μ` is integrating against the density `f.normed μ`. -/
theorem integral_normedMeasure (g : E → G) :
    ∫ x, g x ∂f.normedMeasure μ = ∫ x, f.normed μ x • g x ∂μ := by
  rw [normedMeasure, integral_withDensity_eq_integral_toReal_smul
    f.continuous_normed.measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp [f.nonneg_normed]

omit [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- A function is integrable against `f.normedMeasure μ` exactly when its product with the density
`f.normed μ` is integrable against `μ`. -/
theorem integrable_normedMeasure_iff {g : E → G} :
    Integrable g (f.normedMeasure μ) ↔ Integrable (fun x ↦ f.normed μ x • g x) μ := by
  rw [normedMeasure, integrable_withDensity_iff_integrable_smul'
    f.continuous_normed.measurable.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp [f.nonneg_normed]

/-- The measure `f.normedMeasure μ` is concentrated on the closed ball of radius `f.rOut`. -/
theorem ae_mem_closedBall_normedMeasure : ∀ᵐ x ∂f.normedMeasure μ, x ∈ closedBall c f.rOut :=
  (ae_withDensity_iff f.continuous_normed.measurable.ennreal_ofReal).2
    (ae_of_all _ fun x hx ↦ ball_subset_closedBall <| by
      rw [← f.support_normed_eq (μ := μ)]
      exact fun h ↦ hx (by simp [h]))

omit [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- **Normalized bumps blow up at their centre.** In a nontrivial space, as the outer radii of
bumps `σ i` centred at `c` tend to zero, the values `(σ i).normed μ c` at the centre tend to
infinity: the bumps are one at `c`, and their integrals are at most the measures of the closed
balls of radius `(σ i).rOut`, which tend to zero. -/
theorem tendsto_normed_center_atTop [Nontrivial E] [μ.IsAddHaarMeasure] {ι : Type*}
    {l : Filter ι} {σ : ι → ContDiffBump c} (hσ : Tendsto (fun i ↦ (σ i).rOut) l (𝓝 0)) :
    Tendsto (fun i ↦ (σ i).normed μ c) l atTop := by
  have hval (i : ι) : (σ i).normed μ c = (∫ x, σ i x ∂μ)⁻¹ := by
    rw [normed_def, (σ i).one_of_mem_closedBall (mem_closedBall_self (σ i).rIn_pos.le), one_div]
  have hd : Module.finrank ℝ E ≠ 0 := Module.finrank_pos.ne'
  have hlim : Tendsto (fun i ↦ (σ i).rOut ^ Module.finrank ℝ E * μ.real (ball 0 1)) l (𝓝 0) := by
    simpa [zero_pow hd] using (hσ.pow (Module.finrank ℝ E)).mul_const (μ.real (ball 0 1))
  have hint : Tendsto (fun i ↦ ∫ x, σ i x ∂μ) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨squeeze_zero (fun i ↦ (σ i).integral_pos.le)
      (fun i ↦ ((σ i).integral_le_measure_closedBall μ).trans_eq
        (μ.addHaar_real_closedBall c (σ i).rOut_pos.le)) hlim,
      Eventually.of_forall fun i ↦ (σ i).integral_pos⟩
  simp_rw [hval]
  exact tendsto_inv_nhdsGT_zero.comp hint

end

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
  have h4 : (4 : ℝ) ^ finrank ℝ E = 2 ^ finrank ℝ E * 2 ^ finrank ℝ E := by
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
