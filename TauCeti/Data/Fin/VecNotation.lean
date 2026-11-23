/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Lemmas for matrix and vector notation

This file collects elementary `simp` lemmas about `Matrix.vecCons` under post-composition and
pointwise evaluation of function-like entries.

## Main results

* `Matrix.comp_vecCons`: composing a function with `Matrix.vecCons` pushes inside both arguments.
* `Matrix.eval_vecCons`: pointwise evaluation of `Matrix.vecCons` on a tuple of function-like
  objects.
-/

public section

namespace Matrix

/-- Post-composition with a function pushes inside `Matrix.vecCons`. -/
@[simp]
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

end Matrix
