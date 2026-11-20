/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Restrictions of continuous semilinear maps

This file supplements `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict` with density
properties of codomain restrictions of continuous semilinear maps.

## Main results

* `ContinuousLinearMap.denseRange_codRestrict_topologicalClosure`: corestricting a continuous
  semilinear map to the topological closure of its range yields a map with dense range.
-/

public section

namespace ContinuousLinearMap

/-- The corestriction of a continuous semilinear map to the closure of its range has dense range. -/
theorem denseRange_codRestrict_topologicalClosure {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ : R₁ →+* R₂} [RingHomSurjective σ] [AddCommMonoid M₁] [Module R₁ M₁] [TopologicalSpace M₁]
    [AddCommMonoid M₂] [Module R₂ M₂] [TopologicalSpace M₂] [ContinuousAdd M₂]
    [ContinuousConstSMul R₂ M₂] (g : M₁ →SL[σ] M₂) :
    DenseRange (g.codRestrict (LinearMap.range (g : M₁ →ₛₗ[σ] M₂)).topologicalClosure
      fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  exact (Submodule.topologicalClosure_coe _).subset

end ContinuousLinearMap
