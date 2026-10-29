/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Measurable evaluation of extensions from order intervals

A continuous map on an order interval extends to the ambient linearly ordered space by its
endpoint values. Evaluation of this extension at a fixed point is measurable for the Borel
structure on the space of continuous maps. No compatibility between the order and topology
of the domain is needed.
-/

public section

open Set

namespace TauCeti

/-- On the space `C([a, b], X)` of continuous maps, evaluating the map extended by endpoint
values outside the order interval `[a, b]` at a fixed point is measurable. -/
theorem measurable_IccExtend_apply {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {a b : α} (hab : a ≤ b) (t : α) :
    Measurable fun γ : C(Icc a b, X) ↦ IccExtend hab γ t := by
  simp only [IccExtend_apply]
  exact (continuous_eval_const _).measurable

end TauCeti
