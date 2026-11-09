/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Truncating a function to spanning sets

On a σ-finite measure space, multiplying a function `f` by the indicator of
`spanningSets μ N ∩ {x | ‖f x‖ ≤ N}` gives a sequence converging to `f` pointwise, and the sets are
measurable when `f` is strongly measurable.
-/

public section

open MeasureTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Every point eventually lies in `spanningSets μ N ∩ {x | ‖f x‖ ≤ N}`, so the indicator
functions of these sets multiplied into `f` converge to `f` pointwise. -/
theorem tendsto_indicator_spanningSets_inter_norm_le [SigmaFinite μ] {V : Type*}
    [NormedAddCommGroup V] (f : α → V) (x : α) :
    Filter.Tendsto (fun N : ℕ => (spanningSets μ N ∩ {y | ‖f y‖ ≤ N}).indicator f x)
      Filter.atTop (nhds (f x)) := by
  have h1 := eventually_mem_spanningSets μ x
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, ‖f x‖ ≤ N :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h1, h2] with N hN1 hN2
  exact (Set.indicator_of_mem (show x ∈ spanningSets μ N ∩ {y | ‖f y‖ ≤ N} from ⟨hN1, hN2⟩) f).symm

/-- The set where `f` is bounded by `N` and which lies in the `N`-th spanning set is measurable. -/
theorem measurableSet_spanningSets_inter_norm_le [SigmaFinite μ] {V : Type*}
    [NormedAddCommGroup V] {f : α → V} (hf : StronglyMeasurable f) (N : ℕ) :
    MeasurableSet (spanningSets μ N ∩ {x | ‖f x‖ ≤ N}) :=
  (measurableSet_spanningSets μ N).inter (measurableSet_le hf.norm.measurable measurable_const)

end MeasureTheory
