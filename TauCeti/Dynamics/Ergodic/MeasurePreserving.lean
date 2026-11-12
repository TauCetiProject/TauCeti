/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Trim

/-!
# Finiteness and trimming along measure-preserving maps

## Main results

* `MeasureTheory.MeasurePreserving.isFiniteMeasure` — a finite source measure makes the target of
  a measure-preserving map finite.
* `MeasureTheory.MeasurePreserving.trim_comap` — a measure-preserving map preserves the measures
  trimmed to a target sub-σ-algebra and its pullback on the source.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} {m : MeasurableSpace β}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {f g : α → β}

/-- A finite source measure makes the target of a measure-preserving map finite. -/
theorem isFiniteMeasure [IsFiniteMeasure μ] (hf : MeasurePreserving f μ ν) : IsFiniteMeasure ν :=
  hf.map_eq ▸ Measure.isFiniteMeasure_map μ f

/-- A measure-preserving map also preserves the measures trimmed to a sub-σ-algebra of the target
and its pullback on the source. -/
theorem trim_comap (hg : MeasurePreserving g μ ν) (hm : m ≤ mβ) :
    @MeasurePreserving α β (m.comap g) m g
      (μ.trim ((MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le)) (ν.trim hm) := by
  have hmeas : Measurable[m.comap g, m] g := measurable_iff_comap_le.mpr le_rfl
  refine @MeasurePreserving.mk α β (m.comap g) m g _ _ hmeas ?_
  refine @Measure.ext β m _ _ fun s hs ↦ ?_
  have hmg : m.comap g ≤ mα := (MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le
  have hs' : MeasurableSet[m.comap g] (g ⁻¹' s) := ⟨s, hs, rfl⟩
  rw [Measure.map_apply hmeas hs, trim_measurableSet_eq hmg hs', trim_measurableSet_eq hm hs]
  exact hg.measure_preimage (hm s hs).nullMeasurableSet

end MeasureTheory.MeasurePreserving
