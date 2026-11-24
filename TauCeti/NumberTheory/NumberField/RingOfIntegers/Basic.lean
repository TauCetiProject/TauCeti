/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Countable

/-!
# Basic facts about rings of integers

The ring of integers `𝓞 K` of a number field is countable, being a finitely generated
`ℤ`-module. This file also records basic facts about tuples `y : ι → 𝓞 K` of algebraic integers
and their images in `K`.

## Main results

* `NumberField.instCountableRingOfIntegers`: the ring of integers of a number field is countable.
* `NumberField.RingOfIntegers.coe_tuple_eq_zero_iff`: a tuple of algebraic integers is zero
  exactly when its image in `K` is zero.
-/

public section

namespace NumberField

/-- The ring of integers of a number field is countable, being a finitely generated
`ℤ`-module. -/
instance instCountableRingOfIntegers (K : Type*) [Field K] [NumberField K] :
    Countable (𝓞 K) :=
  Countable.of_moduleFinite (R := ℤ)

end NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] {ι : Type*}

/-- A tuple of algebraic integers is zero exactly when its image in `K` is zero. -/
@[simp]
theorem coe_tuple_eq_zero_iff {y : ι → 𝓞 K} : (fun i ↦ (y i : K)) = 0 ↔ y = 0 := by
  simp [funext_iff]

end NumberField.RingOfIntegers
