/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Lemmas for matrix and vector notation

This file collects elementary lemmas about `Matrix.vecCons` under post-composition and
pointwise evaluation of function-like entries, as well as postcomposing a pair `![a₀, a₁]` with a
function.

## Main results

* `Matrix.comp_vecCons`: composing a function with `Matrix.vecCons` pushes inside both arguments.
* `Matrix.eval_vecCons`: pointwise evaluation of `Matrix.vecCons` on a tuple of function-like
  objects.
* `Matrix.comp_vec2`: `f ∘ ![a₀, a₁] = ![f a₀, f a₁]`.
-/

public section

namespace Matrix

/-- Post-composition with a function pushes inside `Matrix.vecCons`. -/
theorem comp_vecCons {α β : Type*} {n : ℕ} (f : α → β) (x : α) (v : Fin n → α) :
    f ∘ vecCons x v = vecCons (f x) (f ∘ v) := by
  ext i
  cases i using Fin.cases <;> simp

/-- Pointwise evaluation at `x` pushes inside `Matrix.vecCons` on a tuple of function-like
objects. -/
theorem eval_vecCons {M : Type*} {V : M → Type*} {α : Type*} [DFunLike α M V]
    {n : ℕ} (a : α) (s : Fin n → α) (x : M) :
    (fun i ↦ vecCons a s i x) = vecCons (a x) (fun i ↦ s i x) := by
  ext i
  cases i using Fin.cases <;> simp

/-- Postcomposing a pair with a function applies the function to both entries. -/
theorem comp_vec2 {α β : Type*} (f : α → β) (a₀ a₁ : α) : f ∘ ![a₀, a₁] = ![f a₀, f a₁] :=
  (FinVec.map_eq f ![a₀, a₁]).symm

end Matrix
