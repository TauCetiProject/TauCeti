/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Update

/-!
# Evaluating a function updated on a finite set

Mathlib's `Function.updateFinset x s y` replaces the values of `x` on the finite set `s` by those
of `y`. This file evaluates it at a single index: inside `s` it takes the value of `y`
(`Function.updateFinset_apply_of_mem`), and outside `s` the value of `x`
(`Function.updateFinset_apply_of_notMem`). A function `z` agreeing with `x` off `s` is the update
of `x` on `s` by its own restriction to `s` (`Function.updateFinset_restrict_of_eqOn_compl`).
-/

public section

namespace Function

section Apply

variable {ι : Type*} {π : ι → Sort*} [DecidableEq ι] {x : ∀ i, π i} {s : Finset ι}
  {y : ∀ i : s, π i} {i : ι}

/-- Inside `s`, a function updated on `s` takes the new value. -/
@[simp]
theorem updateFinset_apply_of_mem (hi : i ∈ s) : updateFinset x s y i = y ⟨i, hi⟩ :=
  by simp [updateFinset_def, hi]

/-- Outside `s`, a function updated on `s` keeps its old value. -/
@[simp]
theorem updateFinset_apply_of_notMem (hi : i ∉ s) : updateFinset x s y i = x i :=
  by simp [updateFinset_def, hi]

end Apply

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] {x z : ∀ i, π i} {s : Finset ι}

/-- A function `z` agreeing with `x` off `s` is the update of `x` on `s` by the restriction of `z`
to `s`. Mathlib's `Function.updateFinset_restrict` is the case `z = x`. -/
theorem updateFinset_restrict_of_eqOn_compl (h : ∀ i ∉ s, z i = x i) :
    updateFinset x s (s.restrict z) = z := by
  ext i
  by_cases hi : i ∈ s
  · rw [updateFinset_apply_of_mem hi, Finset.restrict_def]
  · rw [updateFinset_apply_of_notMem hi, h i hi]

end Function
