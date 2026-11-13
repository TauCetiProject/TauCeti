/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
public import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Topology.JordanCurve.Interval

/-!
# Jordan traces of absolutely continuous curves

The trace of a simple closed absolutely continuous curve in a Hausdorff pseudometric space
is a Jordan curve. This lets topological results about Jordan curves apply directly to
absolutely continuous parametrizations.
-/

public section

open Set

/-- The trace of a simple closed absolutely continuous curve on `[a, b]` (`a < b`, `γ a = γ b`,
`InjOn γ (Ico a b)`) is a Jordan curve. -/
theorem AbsolutelyContinuousOnInterval.isJordanCurve_image_uIcc
    {X : Type*} [PseudoMetricSpace X] [T2Space X] {γ : ℝ → X} {a b : ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) : TauCeti.IsJordanCurve (γ '' uIcc a b) := by
  rw [uIcc_of_le hab.le]
  exact TauCeti.isJordanCurve_image_Icc hab (uIcc_of_le hab.le ▸ hγ.continuousOn') hclosed hinj
