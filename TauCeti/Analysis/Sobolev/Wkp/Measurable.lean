/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable curves in `W^{k,p}(Ω)`

A curve in a Sobolev space `W^{k,p}(Ω)`, for instance the solution of an evolution equation
observed in a higher-order space, is often built by choosing, at almost every time, an element
of `W^{k,p}(Ω)` with a prescribed value in `Lᵖ(Ω)`. This file shows that such a choice is
automatically measurable when the prescribed values are: for finite `p`, a curve in
`W^{k,p}(Ω)` is almost everywhere strongly measurable as soon as its values in `Lᵖ(Ω)` are
(`TauCeti.Wkp.aestronglyMeasurable_of_ae_value_eq`).

An element of `W^{k,p}(Ω)` is determined by its value (`TauCeti.Wkp.ext`), and for finite `p` the
space is complete and second countable, hence Polish. The value map is therefore a continuous
injection of a Polish space into a Hausdorff space, which is a measurable embedding by the
Lusin–Souslin theorem (`Continuous.measurableEmbedding`).
-/

public section

namespace TauCeti

open MeasureTheory

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : TopologicalSpace.Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Measurability of curves in `W^{k,p}(Ω)` from their values.** For finite `p`, a curve `U` in
`W^{k,p}(Ω)` is almost everywhere strongly measurable as soon as its values in `Lᵖ(Ω)` agree
almost everywhere with an almost everywhere strongly measurable curve `g`. -/
theorem Wkp.aestronglyMeasurable_of_ae_value_eq [Fact (p ≠ ⊤)] {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {k : ℕ} {U : α → Wkp mu Omega p k} {g : α → Lp ℝ p (mu.restrict Omega)}
    (hg : AEStronglyMeasurable g ν) (hUg : ∀ᵐ t ∂ν, Wkp.value k (U t) = g t) :
    AEStronglyMeasurable U ν := by
  borelize (Wkp mu Omega p k) (↥(Lp ℝ p (mu.restrict Omega)))
  have hemb := (Wkp.valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.measurableEmbedding
    fun U₁ U₂ h => Wkp.ext k (by rwa [Wkp.valueL_apply, Wkp.valueL_apply] at h)
  refine (hemb.aemeasurable_comp_iff.1 (hg.aemeasurable.congr ?_)).aestronglyMeasurable
  filter_upwards [hUg] with t ht
  rw [Function.comp_apply, Wkp.valueL_apply, ht]

end TauCeti
