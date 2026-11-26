/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Nonzero ideals of infinite rings

In an infinite ring without zero divisors, every nonzero ideal is infinite
(`Ideal.infinite_of_ne_bot`): right multiplication by a nonzero element of the ideal embeds the
ring into it.
-/

public section

namespace Ideal

/-- In an infinite ring without zero divisors, every nonzero ideal is infinite. -/
theorem infinite_of_ne_bot {R : Type*} [Ring R] [NoZeroDivisors R] [Infinite R] {I : Ideal R}
    (hI : I ≠ ⊥) : (I : Set R).Infinite := by
  -- Right multiplication by a nonzero `x ∈ I` embeds `R` into `I`.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact Set.infinite_of_injective_forall_mem (mul_left_injective₀ hx0) fun y ↦ I.mul_mem_left y hx

end Ideal
