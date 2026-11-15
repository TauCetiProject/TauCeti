/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Tuples of algebraic integers

Basic facts about tuples `y : ι → 𝓞 K` of algebraic integers and their images in `K`.

## Main results

* `NumberField.RingOfIntegers.coe_tuple_eq_zero_iff`: a tuple of algebraic integers is zero
  exactly when its image in `K` is zero.
-/

public section

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] {ι : Type*}

/-- A tuple of algebraic integers is zero exactly when its image in `K` is zero. -/
@[simp]
theorem coe_tuple_eq_zero_iff {y : ι → 𝓞 K} : (fun i ↦ (y i : K)) = 0 ↔ y = 0 := by
  simp [funext_iff]

end NumberField.RingOfIntegers
