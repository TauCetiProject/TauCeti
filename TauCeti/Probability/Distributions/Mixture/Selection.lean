/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Independent categorical selection

An independent categorical selector and a source of random noise realize a finite mixture:
conditional on selecting `i`, apply the `i`th measurable transformation to the common noise.
The component law is the pushforward of the noise law by that transformation.

This gives the random-variable construction corresponding to `finiteMixtureMeasure_eq_bind`.
It allows the transformations to share one noise variable; no independence between the potential
component values is needed.

## Main results

* `TauCeti.Probability.map_uncurry_prod_eq_finiteMixtureMeasure` identifies the pushforward of a
  product law by a measurable indexed family with the corresponding finite mixture.
* `ProbabilityTheory.IndepFun.hasLaw_apply_finiteMixtureMeasure` gives the resulting law for an
  independent categorical selector and noise variable.
* `ProbabilityTheory.IndepFun.hasLaw_select_finiteMixtureMeasure` selects directly from a finite
  family of potential random variables.
-/

public section

noncomputable section

open Convexity MeasureTheory

namespace TauCeti.Probability

variable {I A B : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace A] [MeasurableSpace B]

/-- Mapping a categorical law times a noise law by a measurable indexed family gives the finite
mixture of the component pushforwards. -/
theorem map_uncurry_prod_eq_finiteMixtureMeasure (p : StdSimplex NNReal I) (ρ : Measure A)
    [SFinite ρ] {f : I → A → B} (hf : Measurable (Function.uncurry f)) :
    ((categoricalMeasure p).prod ρ).map (Function.uncurry f) =
      finiteMixtureMeasure p (fun i ↦ ρ.map (f i)) := by
  rw [Measure.prod_eq_of_sfinite,
    Measure.map_bind Measurable.map_prodMk_left.aemeasurable hf.aemeasurable,
    finiteMixtureMeasure_eq_bind]
  apply Measure.bind_congr_right
  filter_upwards with i
  rw [Measure.map_map hf (by fun_prop)]
  rfl

end TauCeti.Probability

namespace ProbabilityTheory

variable {Ω I A B : Type*} [MeasurableSpace Ω] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableSpace A] [MeasurableSpace B]
  {P : Measure Ω} {Z : Ω → I} {U : Ω → A} {p : StdSimplex NNReal I} {ρ : Measure A}
  {K : I → Measure B} {f : I → A → B}

/-- An independent categorical selector chooses the corresponding component pushforward of a
common noise law. No independence between the potential values `f i (U ω)` is required.

The conclusion is stated directly as a `HasLaw` theorem on the native carrier `B`. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure_map (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : Measurable (Function.uncurry f)) :
    HasLaw (fun ω ↦ f (Z ω) (U ω))
      (TauCeti.Probability.finiteMixtureMeasure p (fun i ↦ ρ.map (f i))) P := by
  let _ : IsFiniteMeasure P := hZ.isFiniteMeasure
  let _ : IsFiniteMeasure ρ := hU.isFiniteMeasure_iff.mp inferInstance
  have hpair : HasLaw (fun ω ↦ (Z ω, U ω))
      ((TauCeti.Probability.categoricalMeasure p).prod ρ) P := by
    refine ⟨hZ.aemeasurable.prodMk hU.aemeasurable, ?_⟩
    rw [hZU.map_prod_eq_prod_map_map hZ.aemeasurable hU.aemeasurable, hZ.map_eq, hU.map_eq]
  have hmap := (hasLaw_map hf.aemeasurable).comp hpair
  rw [TauCeti.Probability.map_uncurry_prod_eq_finiteMixtureMeasure p ρ hf] at hmap
  exact hmap.congr (.of_forall fun _ ↦ rfl)

/-- An independent categorical selector chooses the corresponding component law when every
positive-weight component is realized as a measurable transformation of the common noise.
No condition is imposed on zero-weight components. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : Measurable (Function.uncurry f))
    (hK : ∀ i, 0 < p.weights i → ρ.map (f i) = K i) :
    HasLaw (fun ω ↦ f (Z ω) (U ω)) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  have h := hZU.hasLaw_apply_finiteMixtureMeasure_map hZ hU hf
  rw [TauCeti.Probability.finiteMixtureMeasure_congr hK] at h
  exact h

/-- Selecting from a finite family of potential random variables gives the finite mixture of
their laws when the selector is categorical and independent of the whole family. Dependence
between the potential variables themselves is allowed. -/
theorem IndepFun.hasLaw_select_finiteMixtureMeasure {Y : I → Ω → B}
    (hZY : IndepFun Z (fun ω i ↦ Y i ω) P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P)
    (hYmeas : AEMeasurable (fun ω i ↦ Y i ω) P)
    (hY : ∀ i, 0 < p.weights i → HasLaw (Y i) (K i) P) :
    HasLaw (fun ω ↦ Y (Z ω) ω) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  let Y' : Ω → I → B := fun ω i ↦ Y i ω
  have heval : Measurable (Function.uncurry fun i (y : I → B) ↦ y i) :=
    measurable_from_prod_countable_right fun i ↦ measurable_pi_apply i
  apply hZY.hasLaw_apply_finiteMixtureMeasure hZ (hasLaw_map hYmeas) heval
  intro i hi
  change (P.map Y').map (fun y ↦ y i) = K i
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply i).aemeasurable hYmeas]
  exact (hY i hi).map_eq

end ProbabilityTheory
