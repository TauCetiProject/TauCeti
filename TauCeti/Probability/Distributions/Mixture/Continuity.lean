/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic

/-!
# Weak convergence of finite mixtures

Finite mixtures preserve weak convergence when their simplex weights converge and each
component with positive limiting weight converges weakly. Components whose limiting weights
vanish need not converge: their weighted total masses tend to zero.

The results use `ProbabilityMeasure` and its weak topology, and apply to arbitrary topological
measurable spaces with measurable open sets. In particular, no metrizability or sequential
convergence assumption is needed. Joint continuity follows when all component laws vary
continuously, including at the boundary of the simplex of weights.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory Topology
open scoped NNReal

namespace TauCeti.Probability

variable {I B D : Type*} [Fintype I] [MeasurableSpace B]

/-- Viewed as a finite measure, a probability mixture is the weighted sum of the finite
measures associated to its components. -/
@[simp]
theorem toFiniteMeasure_finiteMixtureMeasure (p : StdSimplex ℝ≥0 I)
    (K : I → ProbabilityMeasure B) :
    (@Measure.toProbabilityMeasure B _ (finiteMixtureMeasure p (fun i ↦ (K i : Measure B)))
      (isProbabilityMeasure_finiteMixtureMeasure (fun _ ↦ inferInstance))).toFiniteMeasure =
        ∑ i, p.weights i • (K i).toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  simp [finiteMixtureMeasure_def, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ← ENNReal.smul_def]

variable [TopologicalSpace B] [OpensMeasurableSpace B]

/-- Finite mixtures converge weakly if their weights converge and every component with
positive limiting weight converges weakly. No convergence of a disappearing component is
required. -/
theorem tendsto_finiteMixtureMeasure {F : Filter D} {p : D → StdSimplex ℝ≥0 I}
    {p₀ : StdSimplex ℝ≥0 I} {K : D → I → ProbabilityMeasure B}
    {K₀ : I → ProbabilityMeasure B} (hp : Tendsto p F (𝓝 p₀))
    (hK : ∀ i, 0 < p₀.weights i → Tendsto (fun d ↦ K d i) F (𝓝 (K₀ i))) :
    Tendsto (fun d ↦ @Measure.toProbabilityMeasure B _
      (finiteMixtureMeasure (p d) (fun i ↦ (K d i : Measure B)))
      (isProbabilityMeasure_finiteMixtureMeasure (fun _ ↦ inferInstance)))
      F (𝓝 (@Measure.toProbabilityMeasure B _
        (finiteMixtureMeasure p₀ (fun i ↦ (K₀ i : Measure B)))
        (isProbabilityMeasure_finiteMixtureMeasure (fun _ ↦ inferInstance)))) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  simp only [Function.comp_def, toFiniteMeasure_finiteMixtureMeasure]
  apply tendsto_finsetSum
  intro i _
  have hw := ((StdSimplex.continuous_weights_apply_nnreal i).tendsto p₀).comp hp
  by_cases hi : p₀.weights i = 0
  · simp only [hi, zero_smul]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa [FiniteMeasure.mass, hi, Function.comp_def] using hw
  · exact hw.smul (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto
      (K₀ i) |>.comp (hK i (pos_iff_ne_zero.mpr hi)))

variable [TopologicalSpace D]

/-- Continuous weights and weakly continuous probability components give a weakly continuous
finite mixture, also where some weights vanish. -/
theorem continuous_finiteMixtureMeasure {p : D → StdSimplex ℝ≥0 I}
    {K : D → I → ProbabilityMeasure B} (hp : Continuous p)
    (hK : ∀ i, Continuous fun d ↦ K d i) :
    Continuous (fun d ↦ @Measure.toProbabilityMeasure B _
      (finiteMixtureMeasure (p d) (fun i ↦ (K d i : Measure B)))
      (isProbabilityMeasure_finiteMixtureMeasure (fun _ ↦ inferInstance))) := by
  rw [continuous_iff_continuousAt]
  intro d
  exact tendsto_finiteMixtureMeasure hp.continuousAt fun i _ ↦ (hK i).continuousAt

end TauCeti.Probability
