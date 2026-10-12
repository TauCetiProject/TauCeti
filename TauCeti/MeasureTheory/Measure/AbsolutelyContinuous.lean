/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Domination by a measure charging every point

If a measure gives positive mass to every singleton, every null set is empty. It
therefore dominates any other measure, without a countability or finiteness
assumption. This is useful when a full-support discrete reference is used for
relative entropy.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A measure positive on every singleton dominates every measure: a null set cannot contain
any point. No finiteness or countability assumption is needed. -/
theorem absolutelyContinuous_of_forall_singleton_ne_zero
    (hν : ∀ x : α, ν {x} ≠ 0) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have hempty : s = ∅ := by
    apply Set.Subset.antisymm _ (Set.empty_subset s)
    intro y hy
    have hzero : ν {y} = 0 :=
      le_zero_iff.mp ((measure_mono (Set.singleton_subset_iff.mpr hy)).trans_eq hs)
    exact hν y hzero
  simp [hempty]

end TauCeti
