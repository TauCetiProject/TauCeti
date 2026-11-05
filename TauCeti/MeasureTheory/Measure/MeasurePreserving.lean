/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Trim

/-!
# Measure-preserving maps on pulled-back σ-algebras

A measure-preserving map remains measure preserving when the target σ-algebra is replaced by a
sub-σ-algebra and the source is equipped with its pullback. This allows sigma-finiteness and
almost-everywhere statements to be transported on the smaller measurable spaces, as needed for
conditional expectations.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} {m : MeasurableSpace β}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {g : α → β}

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
