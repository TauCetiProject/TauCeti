/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic

/-!
# Affine transport of compound Poisson laws

Scaling a compound Poisson sum scales each jump and preserves its rate. Translation behaves
differently: it is applied once to the completed sum, rather than once to every jump. Thus the
law of `a + b * X` is the outer translate by `a` of the compound Poisson law whose jump measure
is the image of the original jump measure under `x ↦ b * x`.

The statement includes zero scaling and does not require the jump measure to be a probability
measure. It follows from `TauCeti.Probability.map_compoundPoissonMeasure`, applied only to the
additive scaling map, and composition of measure pushforwards.

## Main results

* `TauCeti.Probability.compoundPoissonMeasure_map_affine` — affine transport scales the jump
  measure and leaves translation as an outer pushforward;
* `ProbabilityTheory.HasLaw.affine_compoundPoissonMeasure` — the corresponding random-variable
  statement.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- The affine image of a compound Poisson law scales each jump but translates the completed
sum only once. The rate is unchanged, and the identity also holds at zero scale. -/
theorem compoundPoissonMeasure_map_affine (r : ℝ≥0) (μ : Measure ℝ) [SFinite μ]
    (a b : ℝ) :
    (compoundPoissonMeasure r μ).map (fun x ↦ a + b * x) =
      (compoundPoissonMeasure r (μ.map (fun x ↦ b * x))).map (fun x ↦ a + x) := by
  have hscale := map_compoundPoissonMeasure r μ (AddMonoidHom.mulLeft b)
    (by simpa only [AddMonoidHom.coe_mulLeft] using measurable_const_mul b)
  simp only [AddMonoidHom.coe_mulLeft] at hscale
  rw [← hscale, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Affine transport of a compound Poisson random variable scales its jump law and leaves the
translation as an outer pushforward. -/
theorem affine_compoundPoissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {r : ℝ≥0} {μ : Measure ℝ} [SFinite μ]
    (hX : HasLaw X (compoundPoissonMeasure r μ) P) (a b : ℝ) :
    HasLaw (fun ω ↦ a + b * X ω)
      ((compoundPoissonMeasure r (μ.map (fun x ↦ b * x))).map (fun x ↦ a + x)) P :=
  (HasLaw.mk (by fun_prop) (compoundPoissonMeasure_map_affine r μ a b)).fun_comp hX

end ProbabilityTheory.HasLaw
