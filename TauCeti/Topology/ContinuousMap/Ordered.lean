/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Positive linear maps on spaces of continuous functions

Precomposition with a continuous map `f : C(α, β)` and evaluation at a point `x : α` preserve both
the module operations and the pointwise order on `C(α, M)` when `M` is an ordered topological
module, so they define positive linear maps (`ContinuousMap.compPositiveLinearMap` and
`ContinuousMap.evalPositiveLinearMap`).

On scalar-valued continuous functions `C(α, R)`, the constant function `const α c` is `c • 1`. A
positive linear functional `φ` on `C(α, R)` therefore maps a function bounded above (or below) by a
constant `c` into the corresponding side of `c • φ 1`, and if a zero-preserving functional does not
vanish at `1`, the domain `α` must be nonempty.
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
    compPositiveLinearMap R M f g = g.comp f :=
  (rfl)

@[simp]
theorem compPositiveLinearMap_id :
    compPositiveLinearMap R M (ContinuousMap.id α) = PositiveLinearMap.id R C(α, M) := by
  ext
  rfl

theorem compPositiveLinearMap_comp (g : C(β, γ)) (f : C(α, β)) :
    compPositiveLinearMap R M (g.comp f) =
      (compPositiveLinearMap R M f).comp (compPositiveLinearMap R M g) :=
  (rfl)

theorem compPositiveLinearMap_const (f : C(α, β)) (m : M) :
    compPositiveLinearMap R M f (const β m) = const α m :=
  (rfl)

/-- Point evaluation of continuous functions, as a `PositiveLinearMap`. -/
def evalPositiveLinearMap (x : α) : C(α, M) →ₚ[R] M where
  toLinearMap := (evalCLM R x).toLinearMap
  monotone' _ _ h := h x

@[simp]
theorem evalPositiveLinearMap_apply (x : α) (f : C(α, M)) :
    evalPositiveLinearMap R M x f = f x :=
  (rfl)

end PositiveLinearMap

section Nonempty

variable {α A B Φ : Type*} [TopologicalSpace α] [TopologicalSpace A] [Zero A] [One A] [Zero B]
  [FunLike Φ C(α, A) B] [ZeroHomClass Φ C(α, A) B]

/-- If a zero-preserving map on `C(α, A)` does not vanish at `1`, then `α` is nonempty. -/
theorem nonempty_of_map_one_ne_zero (φ : Φ) (hφ : φ 1 ≠ 0) : Nonempty α := by
  by_contra! h
  have h10 : (1 : C(α, A)) = 0 := ext fun x => isEmptyElim x
  exact hφ (by rw [h10, map_zero])

end Nonempty

section ConstantBounds

variable {α R B Φ : Type*} [TopologicalSpace α] [Semiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommMonoid B] [Module R B]
  [FunLike Φ C(α, R) B] [LinearMapClass Φ R C(α, R) B]

/-- A linear map on `C(α, R)` evaluates at the constant function `c` to `c • φ 1`. -/
theorem map_const_eq_smul_map_one (φ : Φ) (c : R) :
    φ (const α c) = c • φ 1 := by
  have hc : const α c = c • (1 : C(α, R)) := by ext; simp
  rw [hc, map_smul]

variable [PartialOrder R] [PartialOrder B] [OrderHomClass Φ C(α, R) B]

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
