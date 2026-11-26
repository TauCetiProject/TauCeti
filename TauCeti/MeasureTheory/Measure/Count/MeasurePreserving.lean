/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Bijections preserve counting measure

A measurable bijection `f : α → β` maps counting measure on `α` to counting measure on `β`: the
preimage of a measurable set under a bijection has the same cardinality as the set. In particular
every permutation of a discrete measurable space preserves counting measure.
-/

public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measurable bijection preserves counting measure. -/
theorem measurePreserving_count {f : α → β} (hf : Measurable f) (hbij : f.Bijective) :
    MeasurePreserving f count count := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [map_apply hf hs, count_apply hs, count_apply (hf hs), Set.encard_preimage_of_bijective hbij]

end MeasureTheory.Measure
