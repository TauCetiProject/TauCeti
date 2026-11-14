/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Canonical pre-Brownian measure on product path space

Combining `ProbabilityTheory.BrownianReal.projectiveFamily` with Kolmogorov's extension theorem
`MeasureTheory.projectiveLimit` yields `TauCeti.Probability.brownianProjectiveLimit`, the canonical
probability measure on `(ℝ≥0 → ℝ)` (with the product `σ`-algebra) under which coordinate evaluation
satisfies `ProbabilityTheory.IsPreBrownianReal`.

## Main declarations

* `TauCeti.Probability.brownianProjectiveLimit`: Kolmogorov projective limit of
  `BrownianReal.projectiveFamily`.
* `TauCeti.Probability.isProjectiveLimit_brownianProjectiveLimit`,
  `TauCeti.Probability.isProjectiveLimit_projectiveFamily_iff`: projective-limit characterization.
* `TauCeti.Probability.isPreBrownianReal_eval_brownianProjectiveLimit`,
  `TauCeti.Probability.isPreBrownianReal_eval_iff`,
  `TauCeti.Probability.hasLaw_brownianProjectiveLimit_iff`: coordinate pre-Brownian motion and
  path-law universal property.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityTheory.BrownianReal
open scoped NNReal

namespace TauCeti.Probability

/-- Kolmogorov projective limit of `BrownianReal.projectiveFamily` on `ℝ≥0 → ℝ`. -/
def brownianProjectiveLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit projectiveFamily isProjectiveMeasureFamily_projectiveFamily

/-- `brownianProjectiveLimit` is a probability measure on `ℝ≥0 → ℝ`. -/
instance isProbabilityMeasure_brownianProjectiveLimit :
    IsProbabilityMeasure brownianProjectiveLimit := by
  unfold brownianProjectiveLimit; infer_instance

/-- `brownianProjectiveLimit` is the projective limit of `BrownianReal.projectiveFamily`. -/
theorem isProjectiveLimit_brownianProjectiveLimit :
    IsProjectiveLimit brownianProjectiveLimit projectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_projectiveFamily

/-- A measure on `ℝ≥0 → ℝ` is a projective limit of `projectiveFamily` iff it equals
`brownianProjectiveLimit`. -/
theorem isProjectiveLimit_projectiveFamily_iff {μ : Measure (ℝ≥0 → ℝ)} :
    IsProjectiveLimit μ projectiveFamily ↔ μ = brownianProjectiveLimit :=
  ⟨fun h ↦ h.unique isProjectiveLimit_brownianProjectiveLimit,
    fun h ↦ h ▸ isProjectiveLimit_brownianProjectiveLimit⟩

/-- Under `brownianProjectiveLimit`, evaluation `(t, ω) ↦ ω t` is a scalar pre-Brownian motion. -/
theorem isPreBrownianReal_eval_brownianProjectiveLimit :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) ↦ ω t) brownianProjectiveLimit :=
  ⟨fun I ↦ ⟨(Finset.measurable_restrict I).aemeasurable,
    isProjectiveLimit_brownianProjectiveLimit I⟩⟩

/-- Evaluation `(t, ω) ↦ ω t` satisfies `IsPreBrownianReal` under `μ` iff
`μ = brownianProjectiveLimit`. -/
theorem isPreBrownianReal_eval_iff {μ : Measure (ℝ≥0 → ℝ)} :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) ↦ ω t) μ ↔ μ = brownianProjectiveLimit :=
  ⟨fun h ↦ isProjectiveLimit_projectiveFamily_iff.mp fun I ↦ (h.hasLaw I).map_eq,
    fun h ↦ h ▸ isPreBrownianReal_eval_brownianProjectiveLimit⟩

/-- `ω ↦ (X · ω)` has law `brownianProjectiveLimit` under `P` iff `IsPreBrownianReal X P` and
`AEMeasurable (fun ω t ↦ X t ω) P`. -/
theorem hasLaw_brownianProjectiveLimit_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} :
    HasLaw (fun ω t ↦ X t ω) brownianProjectiveLimit P ↔
      IsPreBrownianReal X P ∧ AEMeasurable (fun ω t ↦ X t ω) P :=
  ⟨fun h ↦ ⟨⟨fun I ↦ (isPreBrownianReal_eval_brownianProjectiveLimit.hasLaw I).fun_comp h⟩,
      h.aemeasurable⟩,
    fun ⟨hX, hm⟩ ↦ ⟨hm, isProjectiveLimit_projectiveFamily_iff.mp fun I ↦ by
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hm]
      exact (hX.hasLaw I).map_eq⟩⟩

end TauCeti.Probability
