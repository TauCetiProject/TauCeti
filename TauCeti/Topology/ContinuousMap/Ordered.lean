/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered
public import TauCeti.Algebra.Order.Module.PositiveLinearMap

import TauCeti.Topology.ContinuousMap.Algebra

/-!
# Positive linear maps on spaces of continuous functions

Precomposition with a continuous map `f : C(α, β)` and evaluation at a point `x : α` preserve both
the module operations and the pointwise order on `C(α, M)` when `M` is an ordered topological
module, so they define positive linear maps (`ContinuousMap.compPositiveLinearMap` and
`ContinuousMap.evalPositiveLinearMap`).

On scalar-valued continuous functions `C(α, R)`, a positive linear map `φ` sends `const α c` to
`c • φ 1` (`ContinuousMap.map_const_eq_smul_map_one`), and therefore maps any function bounded above
(or below) pointwise by `c` into the corresponding side of `c • φ 1`.
-/

public section

namespace ContinuousMap

section PositiveLinearMap

variable (R M : Type*) {α β γ : Type*} [Semiring R] [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] [AddCommMonoid M] [PartialOrder M] [TopologicalSpace M] [ContinuousAdd M]
  [Module R M] [ContinuousConstSMul R M]

/-- Composition on the right by a continuous map, as a `PositiveLinearMap`. -/
def compPositiveLinearMap (f : C(α, β)) : C(β, M) →ₚ[R] C(α, M) where
  toLinearMap := (compCLM R M f).toLinearMap
  monotone' _ _ h x := h (f x)

@[simp]
theorem compPositiveLinearMap_apply (f : C(α, β)) (g : C(β, M)) :
    compPositiveLinearMap R M f g = g.comp f := by
  rw [← PositiveLinearMap.coe_toLinearMap]
  simp [compPositiveLinearMap]

@[simp]
theorem compPositiveLinearMap_id :
    compPositiveLinearMap R M (ContinuousMap.id α) = PositiveLinearMap.id R C(α, M) := by
  ext
  simp

theorem compPositiveLinearMap_comp (g : C(β, γ)) (f : C(α, β)) :
    compPositiveLinearMap R M (g.comp f) =
      (compPositiveLinearMap R M f).comp (compPositiveLinearMap R M g) := by
  ext
  simp

theorem compPositiveLinearMap_const (f : C(α, β)) (m : M) :
    compPositiveLinearMap R M f (const β m) = const α m := by
  simp

/-- Point evaluation of continuous functions, as a `PositiveLinearMap`. -/
def evalPositiveLinearMap (x : α) : C(α, M) →ₚ[R] M where
  toLinearMap := (evalCLM R x).toLinearMap
  monotone' _ _ h := h x

@[simp]
theorem evalPositiveLinearMap_apply (x : α) (f : C(α, M)) :
    evalPositiveLinearMap R M x f = f x := by
  rw [← PositiveLinearMap.coe_toLinearMap]
  simp [evalPositiveLinearMap]

end PositiveLinearMap

section ConstantBounds

variable {α R B Φ : Type*} [TopologicalSpace α] [Semiring R] [PartialOrder R] [TopologicalSpace R]
  [ContinuousAdd R] [ContinuousConstSMul R R] [AddCommMonoid B] [PartialOrder B] [Module R B]
  [FunLike Φ C(α, R) B] [LinearMapClass Φ R C(α, R) B] [OrderHomClass Φ C(α, R) B]

/-- A positive linear map on `C(α, R)` bounds above by `c • φ 1` any function bounded above
pointwise by `c`. -/
theorem apply_le_smul_map_one_of_forall_le (φ : Φ) {f : C(α, R)} {c : R} (hf : ∀ x, f x ≤ c) :
    φ f ≤ c • φ 1 := by
  rw [← map_const_eq_smul_map_one]
  exact OrderHomClass.mono φ fun x => hf x

/-- A positive linear map on `C(α, R)` bounds below by `c • φ 1` any function bounded below
pointwise by `c`. -/
theorem smul_map_one_le_apply_of_forall_le (φ : Φ) {f : C(α, R)} {c : R} (hf : ∀ x, c ≤ f x) :
    c • φ 1 ≤ φ f := by
  rw [← map_const_eq_smul_map_one]
  exact OrderHomClass.mono φ fun x => hf x

end ConstantBounds

end ContinuousMap
