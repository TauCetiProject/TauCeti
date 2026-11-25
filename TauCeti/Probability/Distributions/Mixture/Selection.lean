/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic
public import TauCeti.Probability.HasLaw

import TauCeti.MeasureTheory.Measure.Prod

/-!
# Independent categorical selection

An independent categorical selector and a source of random noise realize a finite mixture:
conditional on selecting `i`, apply the `i`th almost-everywhere measurable transformation to the
common noise.
The component law is the pushforward of the noise law by that transformation.

This gives the random-variable construction corresponding to `finiteMixtureMeasure_eq_bind`.
It allows the transformations to share one noise variable; no independence between the potential
component values is needed.

## Main results

* `MeasureTheory.Measure.map_uncurry_prod_eq_bind_map` identifies the pushforward of a product
  measure by an almost-everywhere measurable indexed family with a measure bind.
* `ProbabilityTheory.IndepFun.hasLaw_apply_bind` gives the corresponding law for an independent
  selector and noise variable.
* `TauCeti.Probability.map_uncurry_prod_eq_finiteMixtureMeasure` identifies the pushforward of a
  categorical product law by an indexed family with the corresponding finite mixture.
* `ProbabilityTheory.IndepFun.hasLaw_apply_finiteMixtureMeasure` gives the resulting law for an
  independent categorical selector and noise variable.
* `ProbabilityTheory.HasLaw.eval_finiteMixtureMeasure` selects directly from a finite family of
  potential random variables.
-/

public section

noncomputable section

open Convexity MeasureTheory

namespace TauCeti.Probability

variable {I A B : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace A] [MeasurableSpace B]

/-- An indexed family is almost-everywhere measurable for a categorical product law exactly when
every positive-weight component is almost-everywhere measurable. -/
theorem aemeasurable_uncurry_categoricalMeasure_prod_iff (p : StdSimplex NNReal I)
    (ρ : Measure A) [SFinite ρ] {f : I → A → B} :
    AEMeasurable (Function.uncurry f) ((categoricalMeasure p).prod ρ) ↔
      ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ := by
  rw [Measure.aemeasurable_uncurry_prod_iff]
  constructor
  · intro hf i hi
    exact hf i (by simpa [categoricalMeasure_singleton] using hi.ne')
  · intro hf i hi
    exact hf i (pos_iff_ne_zero.mpr <| by simpa [categoricalMeasure_singleton] using hi)

/-- An indexed family is almost-everywhere measurable for a categorical product law when every
positive-weight component is almost-everywhere measurable. -/
theorem aemeasurable_uncurry_categoricalMeasure_prod (p : StdSimplex NNReal I)
    (rho : Measure A) [SFinite rho] {f : I → A → B}
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) rho) :
    AEMeasurable (Function.uncurry f) ((categoricalMeasure p).prod rho) :=
  (aemeasurable_uncurry_categoricalMeasure_prod_iff p rho).2 hf

/-- Mapping a categorical law times a noise law by an indexed family that is almost-everywhere
measurable on the positive-weight components gives the finite mixture of their pushforwards. -/
theorem map_uncurry_prod_eq_finiteMixtureMeasure (p : StdSimplex NNReal I) (ρ : Measure A)
    [SFinite ρ] {f : I → A → B} (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ) :
    ((categoricalMeasure p).prod ρ).map (Function.uncurry f) =
      finiteMixtureMeasure p (fun i ↦ ρ.map (f i)) := by
  rw [Measure.map_uncurry_prod_eq_bind_map _ _
    (aemeasurable_uncurry_categoricalMeasure_prod p ρ hf), finiteMixtureMeasure_eq_bind]

/-- Mapping a categorical law times a function-valued law by evaluation gives the finite mixture
of its coordinate pushforwards. -/
theorem map_eval_prod_eq_finiteMixtureMeasure_map (p : StdSimplex NNReal I)
    (rho : Measure (I → B)) [SFinite rho] :
    ((categoricalMeasure p).prod rho).map (fun z ↦ z.2 z.1) =
      finiteMixtureMeasure p (fun i ↦ rho.map (Function.eval i)) := by
  rw [Measure.map_eval_prod_eq_bind_map, ← finiteMixtureMeasure_eq_bind]

/-- Evaluation under a categorical law times a product probability law gives the corresponding
finite mixture. -/
@[simp]
theorem map_eval_prod_pi_eq_finiteMixtureMeasure (p : StdSimplex NNReal I)
    (K : I → Measure B) [∀ i, IsProbabilityMeasure (K i)] :
    ((categoricalMeasure p).prod (Measure.pi K)).map (fun z ↦ z.2 z.1) =
      finiteMixtureMeasure p K := by
  rw [Measure.map_eval_prod_pi_eq_bind, ← finiteMixtureMeasure_eq_bind]

end TauCeti.Probability

namespace ProbabilityTheory

variable {Ω I A B : Type*} [MeasurableSpace Ω] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableSpace A] [MeasurableSpace B]
  {P : Measure Ω} {Z : Ω → I} {U : Ω → A} {p : StdSimplex NNReal I} {ρ : Measure A}
  {K : I → Measure B} {f : I → A → B}

/-- Applying an indexed family to an independent categorical selector and noise variable gives the
finite mixture of the component pushforwards. No independence between the potential values
`f i (U ω)` is required. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure_map (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ) :
    HasLaw (fun ω ↦ f (Z ω) (U ω))
      (TauCeti.Probability.finiteMixtureMeasure p (fun i ↦ ρ.map (f i))) P := by
  let _ : IsFiniteMeasure P := hZ.isFiniteMeasure
  let _ : IsFiniteMeasure ρ := hU.isFiniteMeasure_iff.mp inferInstance
  have h := hZU.hasLaw_apply_bind_map hZ hU
    (TauCeti.Probability.aemeasurable_uncurry_categoricalMeasure_prod p ρ hf)
  rw [← TauCeti.Probability.finiteMixtureMeasure_eq_bind] at h
  exact h

/-- Applying an indexed family to an independent categorical selector and common noise gives the
finite mixture of the component laws when every positive-weight component is realized by an
almost-everywhere measurable transformation. No condition is imposed on zero-weight components. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ)
    (hK : ∀ i, 0 < p.weights i → ρ.map (f i) = K i) :
    HasLaw (fun ω ↦ f (Z ω) (U ω)) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  have h := hZU.hasLaw_apply_finiteMixtureMeasure_map hZ hU hf
  rw [TauCeti.Probability.finiteMixtureMeasure_congr hK] at h
  exact h

/-- Evaluating a finite family of potential random variables at a categorical selector gives the
finite mixture of their laws when the selector is independent of every positive-weight component.
Dependence between the potential variables themselves is allowed. -/
theorem HasLaw.eval_finiteMixtureMeasure {Y : I → Ω → B}
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P)
    (hZY : ∀ i, 0 < p.weights i → IndepFun Z (Y i) P)
    (hY : ∀ i, 0 < p.weights i → HasLaw (Y i) (K i) P) :
    HasLaw (fun ω ↦ Y (Z ω) ω) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  rw [TauCeti.Probability.finiteMixtureMeasure_eq_bind]
  apply hZ.eval_bind
  · exact ae_iff_of_countable.2 fun i hi ↦ hZY i <|
      pos_iff_ne_zero.mpr <| by
        simpa [TauCeti.Probability.categoricalMeasure_singleton] using hi
  · exact ae_iff_of_countable.2 fun i hi ↦ hY i <|
      pos_iff_ne_zero.mpr <| by
        simpa [TauCeti.Probability.categoricalMeasure_singleton] using hi

end ProbabilityTheory
