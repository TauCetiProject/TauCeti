/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Updating a vector written with `Matrix.vecCons`

Updating `vecCons x u` at `0` replaces its head, and updating it at `i.succ` updates the tail at
`i`. The first form is `Fin.update_cons_zero` and the second `Fin.cons_update`, restated for the
non-dependent `Matrix.vecCons`. Since a numeral `k + 1 : Fin n` is not syntactically a successor,
the numerals `1`, `2` and `3` get their own lemmas, so that `simp` rewrites
`Function.update ![a, b, c, d] 2 x` to `![a, b, x, d]`.

## Main results

* `Matrix.update_vecCons_zero` and `Matrix.update_vecCons_succ`: updating at the head and in the
  tail.
* `Matrix.update_vecCons_one`, `Matrix.update_vecCons_two` and `Matrix.update_vecCons_three`:
  updating at the numerals `1`, `2` and `3`.
-/

public section

namespace Matrix

variable {α : Type*} {n : ℕ}

/-- Updating `vecCons x u` at `0` replaces the head `x`. -/
@[simp]
theorem update_vecCons_zero (x : α) (u : Fin n → α) (y : α) :
    Function.update (vecCons x u) 0 y = vecCons y u :=
  Fin.update_cons_zero (α := fun _ ↦ α) x u y

/-- Updating `vecCons x u` at `i.succ` updates the tail `u` at `i`. -/
@[simp]
theorem update_vecCons_succ (x : α) (u : Fin n → α) (i : Fin n) (y : α) :
    Function.update (vecCons x u) i.succ y = vecCons x (Function.update u i y) :=
  (Fin.cons_update (α := fun _ ↦ α) x u i y).symm

/-- Updating `vecCons x u` at `1` updates the tail `u` at `0`. -/
@[simp]
theorem update_vecCons_one (x : α) (u : Fin (n + 1) → α) (y : α) :
    Function.update (vecCons x u) 1 y = vecCons x (Function.update u 0 y) :=
  update_vecCons_succ x u 0 y

/-- Updating `vecCons x u` at `2` updates the tail `u` at `1`. -/
@[simp]
theorem update_vecCons_two (x : α) (u : Fin (n + 2) → α) (y : α) :
    Function.update (vecCons x u) 2 y = vecCons x (Function.update u 1 y) :=
  update_vecCons_succ x u 1 y

/-- Updating `vecCons x u` at `3` updates the tail `u` at `2`. -/
@[simp]
theorem update_vecCons_three (x : α) (u : Fin (n + 3) → α) (y : α) :
    Function.update (vecCons x u) 3 y = vecCons x (Function.update u 2 y) :=
  update_vecCons_succ x u 2 y

end Matrix
