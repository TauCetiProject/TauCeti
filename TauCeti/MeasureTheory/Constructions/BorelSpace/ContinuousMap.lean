/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.Order.ProjIcc

/-!
# Measurable evaluation of extended continuous paths

A continuous path on a closed interval extends to the real line by its endpoint values.
Evaluation of this extension at a fixed time is measurable for the Borel structure on the
space of continuous paths, without any metric assumption on the codomain.
-/

public section

open Set

namespace TauCeti

/-- On the space `C([a, b], X)` of continuous paths, evaluating the path extended by constants
outside `[a, b]` at a fixed time is measurable. -/
theorem measurable_IccExtend_apply {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    Measurable fun γ : C(Icc a b, X) ↦ IccExtend hab γ t := by
  simp only [IccExtend_apply]
  exact (continuous_eval_const _).measurable

end TauCeti
