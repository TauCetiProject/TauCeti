/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Units bounded at every infinite place

Only finitely many units of the ring of integers of a number field have absolute value at most
`B` at every infinite place: such a unit is an algebraic integer all of whose conjugates are
bounded by `B`, and there are finitely many of those
(`NumberField.Embeddings.finite_of_norm_le`). This finiteness is what makes the certification
of a fundamental unit a finite search.

## Main results

* `NumberField.Units.finite_setOf_forall_apply_le`: the set of units with absolute value at most
  `B` at every infinite place is finite.
-/

public section

open NumberField NumberField.InfinitePlace
open scoped NumberField

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Finiteness of bounded units.** Only finitely many units have absolute value at most `B` at
every infinite place. -/
theorem finite_setOf_forall_apply_le (B : ℝ) :
    {u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, w u ≤ B}.Finite := by
  refine ((Embeddings.finite_of_norm_le K ℂ B).preimage (coe_injective K).injOn).subset
    fun u hu => ⟨RingOfIntegers.isIntegral_coe (u : 𝓞 K), fun φ => hu (InfinitePlace.mk φ)⟩

end NumberField.Units
