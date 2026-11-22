/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne

/-!
# Endpoint evaluations for morphisms to `⦋1⦌`

This file supplements `Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne` with the identification
of the endpoint maps `SimplexCategory.toMk₁ 0` and `SimplexCategory.toMk₁ (Fin.last (n + 1))`
with the constant morphisms `SimplexCategory.const ⦋n⦌ ⦋1⦌ 1` and
`SimplexCategory.const ⦋n⦌ ⦋1⦌ 0`.
-/

public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

/-- The zeroth morphism in the enumeration `toMk₁ : Fin (n + 2) → (⦋n⦌ ⟶ ⦋1⦌)` is the constant
morphism with value `1`. -/
@[simp]
lemma toMk₁_zero (n : ℕ) :
    toMk₁ (0 : Fin (n + 2)) = const ⦋n⦌ ⦋1⦌ 1 := by
  refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
  simp [toMk₁_apply]
  rfl

/-- The last morphism in the enumeration `toMk₁ : Fin (n + 2) → (⦋n⦌ ⟶ ⦋1⦌)` is the constant
morphism with value `0`. -/
@[simp]
lemma toMk₁_last (n : ℕ) :
    toMk₁ (Fin.last (n + 1)) = const ⦋n⦌ ⦋1⦌ 0 := by
  refine ConcreteCategory.hom_ext _ _ fun k ↦ ?_
  have hk : k.castSucc < Fin.last (n + 1) := Fin.castSucc_lt_last k
  simp [toMk₁_apply, hk]
  rfl

end SimplexCategory
