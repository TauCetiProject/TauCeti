/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals against normalized bumps

Let `f` be a smooth bump centred at `c` in a finite-dimensional real normed space. Its normalized
form `f.normed μ` is continuous with compact support, so it makes every continuous function
integrable. Since it vanishes off the closed ball of radius `f.rOut` around `c`, an integral against
it may be taken over that compact ball, with the pullback of `μ`, which is a finite measure. There
`f.normed μ` still has integral one and averages constants to themselves.

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
  `ContDiffBump.integral_normedMeasure` and `ContDiffBump.ae_mem_closedBall_normedMeasure`.
* `ContDiffBump.tendsto_normed_center_atTop`: normalized bumps with outer radii tending to zero
  tend to infinity at their centre.
-/

public section

open Filter MeasureTheory Metric Topology

namespace ContDiffBump

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

end ContDiffBump
