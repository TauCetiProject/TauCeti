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
properties of codomain restrictions and retract-compression identities for invariant submodules.

## Main results

* `ContinuousLinearMap.denseRange_codRestrict_topologicalClosure`: corestricting a continuous
  semilinear map to the topological closure of its range yields a map with dense range.
* `ContinuousLinearMap.comp_comp_subtypeL_eq_restrict`: compressing a continuous semilinear map
  along a continuous linear retraction onto a target submodule equals its restriction.
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

/-- Compressing a continuous semilinear map `u` sending `S₁` into `S₂` along a continuous linear
retraction `r ∘ S₂.subtypeL = id` yields the restriction `u.restrict hs`. -/
theorem comp_comp_subtypeL_eq_restrict {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ : R₁ →+* R₂} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
    {u : M₁ →SL[σ] M₂} {S₁ : Submodule R₁ M₁} {S₂ : Submodule R₂ M₂}
    (hs : ∀ x ∈ S₁, u x ∈ S₂) {r : M₂ →L[R₂] S₂}
    (hri : r.comp S₂.subtypeL = .id R₂ S₂) :
    r.comp (u.comp S₁.subtypeL) = u.restrict hs := by
  ext1 x
  have hfix : r (S₂.subtypeL (u.restrict hs x)) = u.restrict hs x := by
    simpa only [comp_apply, id_apply] using DFunLike.congr_fun hri (u.restrict hs x)
  simpa only [comp_apply, Submodule.subtypeL_apply, restrict_apply] using hfix

end ContinuousLinearMap
