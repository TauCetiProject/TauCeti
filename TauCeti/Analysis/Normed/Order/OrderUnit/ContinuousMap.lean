/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic

/-!
# Order-unit norm on `C(K, ℝ)`

For a nonempty compact topological space `K`, the space `C(K, ℝ)` of continuous real-valued
functions with unit `1` and the supremum norm is an order-unit space
(`TauCeti.OrderUnit.isOrderUnitNorm_one_continuousMap`).
-/

public section

namespace TauCeti.OrderUnit

/-- `C(K, ℝ)` for a nonempty compact space `K`, with `e = 1`, is an order-unit space with the
supremum norm. -/
theorem isOrderUnitNorm_one_continuousMap {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [Nonempty K] : IsOrderUnitNorm (1 : C(K, ℝ)) where
  norm_e := norm_one
  norm_le_iff f r hr := by
    rw [ContinuousMap.norm_le f hr]
    simp only [Real.norm_eq_abs, abs_le, ContinuousMap.le_def, ContinuousMap.coe_smul,
      ContinuousMap.coe_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact forall_and

end TauCeti.OrderUnit
