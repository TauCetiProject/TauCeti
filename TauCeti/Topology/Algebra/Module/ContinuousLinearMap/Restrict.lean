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
properties of codomain restrictions of continuous semilinear maps, and with the restriction of an
`R`-linear map to submodules over a larger ring `S` of scalars. Mathlib's
`ContinuousLinearMap.restrict` needs `R`-submodules; restricting to `Submodule.restrictScalars R`
would forget the `S`-module structure of the restricted spaces, for example the complex structure
of complex subspaces for a real-linear map.

## Main definitions

* `ContinuousLinearMap.restrictOfTower`: the restriction of an `R`-linear map `f` to submodules
  `p`, `q` over `S`, given that `f` maps `p` into `q`.

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

section Tower

variable {R S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [TopologicalSpace N] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The restriction of an `R`-linear map `f : M →L[R] N` mapping the submodule `p` into the
submodule `q`, as an `R`-linear map `p →L[R] q`. The submodules may be over a larger ring `S` of
scalars, whose module structure on `p` and `q` is kept. -/
def restrictOfTower (f : M →L[R] N) {p : Submodule S M} {q : Submodule S N}
    (h : ∀ x ∈ p, f x ∈ q) : p →L[R] q where
  toFun x := ⟨f x, h x x.property⟩
  map_add' x y := Subtype.ext (f.map_add x y)
  map_smul' c x := Subtype.ext (f.map_smul c (x : M))
  cont := (f.continuous.comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_restrictOfTower_apply (f : M →L[R] N) {p : Submodule S M} {q : Submodule S N}
    (h : ∀ x ∈ p, f x ∈ q) (x : p) : (f.restrictOfTower h x : N) = f x :=
  (rfl)

end Tower

end ContinuousLinearMap
