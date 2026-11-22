/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Strong measurability of continuous functions with compact range and complex exponentials

A continuous function from a space with the Borel `σ`-algebra to a pseudo-metrizable space is
strongly measurable as soon as its range lies in a compact set, since the range is then separable.
No countability assumption on the domain is needed.

Also provides `MeasureTheory.StronglyMeasurable.exp_I_mul_add` for the strong measurability of
`ω ↦ Complex.exp (Complex.I * α * (f ω : ℂ) + b)` when `f` is real-valued and strongly measurable.

## Main results

* `Continuous.stronglyMeasurable_of_range_subset_isCompact`: a continuous function whose range
  lies in a compact set is strongly measurable.
* `MeasureTheory.StronglyMeasurable.exp_I_mul_add`: complex exponential of a strongly measurable
  real function scaled by `I * α` and shifted by `b : ℂ`.
-/

public section

open MeasureTheory TopologicalSpace

/-- A continuous function whose range lies in a compact set is strongly measurable, without any
countability assumption on the domain. -/
theorem Continuous.stronglyMeasurable_of_range_subset_isCompact {X Z : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] {u : X → Z} (hu : Continuous u) {s : Set Z} (hs : IsCompact s)
    (hus : ∀ x, u x ∈ s) : StronglyMeasurable u := by
  borelize Z
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨hu.measurable, ?_⟩
  exact (hs.isSeparable).mono (Set.range_subset_iff.2 hus)

/-- A complex exponential of a real strongly measurable function `f` scaled by `I * α` and shifted
by a constant `b : ℂ` is strongly measurable. -/
theorem MeasureTheory.StronglyMeasurable.exp_I_mul_add {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) (α : ℂ) (b : ℂ) :
    StronglyMeasurable[m] (fun ω ↦ Complex.exp (Complex.I * α * (f ω : ℂ) + b)) :=
  Complex.continuous_exp.comp_stronglyMeasurable <| (stronglyMeasurable_const.mul
    (Complex.continuous_ofReal.comp_stronglyMeasurable hf)).add stronglyMeasurable_const
