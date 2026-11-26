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
properties of codomain restrictions of continuous semilinear maps, and with the restriction and
corestriction of an `R`-linear map to submodules over a larger ring `S` of scalars. They are
Mathlib's `ContinuousLinearMap.restrict` and `ContinuousLinearMap.codRestrict` for the
`R`-submodules `Submodule.restrictScalars R`, stated with the `S`-submodules themselves as domain
and codomain, so that their `S`-module structure, for example the complex structure of complex
subspaces for a real-linear map, is directly available.

## Main definitions

* `ContinuousLinearMap.restrictOfTower`: the restriction of an `R`-linear map `f` to submodules
  `p`, `q` over `S`, given that `f` maps `p` into `q`.
* `ContinuousLinearMap.codRestrictOfTower`: the corestriction of an `R`-linear map `f` to a
  submodule `q` over `S` containing its values.

## Main results

* `LinearMap.denseRange_range_subtypeL_iff`: the bundled range inclusion has dense range exactly
  when the original semilinear map does.
* `ContinuousLinearMap.denseRange_codRestrict_topologicalClosure`: corestricting a continuous
  semilinear map to the topological closure of its range yields a map with dense range.
-/

public section

namespace LinearMap

/-- The bundled inclusion of a semilinear map's range has dense range exactly when the map does.
No topology on the source or continuity of the map or scalar actions is needed. -/
theorem denseRange_range_subtypeL_iff {R S V E : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} [RingHomSurjective σ] [AddCommMonoid V] [Module R V]
    [AddCommMonoid E] [Module S E] [TopologicalSpace E] (e : V →ₛₗ[σ] E) :
    DenseRange e.range.subtypeL ↔ DenseRange e := by
  rw [Submodule.coe_subtypeL]
  unfold DenseRange
  rw [← LinearMap.coe_range, Submodule.range_subtype, LinearMap.coe_range]

end LinearMap

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
    (h : ∀ x ∈ p, f x ∈ q) : p →L[R] q :=
  f.restrict (p := p.restrictScalars R) (q := q.restrictScalars R) h

@[simp]
theorem coe_restrictOfTower_apply (f : M →L[R] N) {p : Submodule S M} {q : Submodule S N}
    (h : ∀ x ∈ p, f x ∈ q) (x : p) : (f.restrictOfTower h x : N) = f x :=
  (rfl)

omit [Module S M] [IsScalarTower R S M] in
/-- The corestriction of an `R`-linear map `f : M →L[R] N` with values in the submodule `q`, as an
`R`-linear map `M →L[R] q`. The submodule may be over a larger ring `S` of scalars, whose module
structure on `q` is kept. -/
def codRestrictOfTower (f : M →L[R] N) {q : Submodule S N} (h : ∀ x, f x ∈ q) : M →L[R] q :=
  f.codRestrict (q.restrictScalars R) h

omit [Module S M] [IsScalarTower R S M] in
@[simp]
theorem coe_codRestrictOfTower_apply (f : M →L[R] N) {q : Submodule S N} (h : ∀ x, f x ∈ q)
    (x : M) : (f.codRestrictOfTower h x : N) = f x :=
  (rfl)

omit [Module S M] [IsScalarTower R S M] in
/-- The corestriction of a composite `f ∘L g` evaluates to `f (g x)`, for a membership proof stated
in terms of `f (g x)`. -/
@[simp]
theorem coe_codRestrictOfTower_comp_apply {L : Type*} [TopologicalSpace L] [AddCommMonoid L]
    [Module R L] (f : M →L[R] N) (g : L →L[R] M) {q : Submodule S N} (h : ∀ x, f (g x) ∈ q)
    (x : L) : ((f ∘L g).codRestrictOfTower h x : N) = f (g x) :=
  (rfl)

end Tower

end ContinuousLinearMap
