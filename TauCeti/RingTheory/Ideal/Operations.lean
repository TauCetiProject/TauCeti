/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.LinearAlgebra.Pi

/-!
# Complements on ideal multiplication and the ideal action

This file collects general facts about the multiplication of ideals and about the action `I • N`
of an ideal on a module, complementing `Mathlib/RingTheory/Ideal/Operations.lean`.

## Main results

* `Ideal.eq_one_of_mul_eq_one`: the only factorization of the unit ideal is the trivial one, so a
  factor of `1` is `1`. This is the ideal-theoretic cancellation step behind the fact that the
  divisor antidiagonal of the unit ideal is a singleton.
* `Ideal.smul_top_eq_top_of_pi`: an ideal that expands the whole of a product of modules expands
  the whole of every factor.
-/

public section

namespace Ideal

section Mul

variable {R : Type*} [CommSemiring R] {I J : Ideal R}

/-- If two ideals multiply to the unit ideal, then the first ideal is the unit ideal. -/
theorem eq_one_of_mul_eq_one (h : I * J = 1) : I = 1 := by
  have hle : (1 : Ideal R) ≤ I := by
    rw [← h]
    exact Ideal.mul_le_left
  rw [Ideal.one_eq_top, eq_top_iff]
  simpa [Ideal.one_eq_top] using hle

end Mul

section Pi

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)]

/-- **Expanding a product expands every factor**: if `I • ⊤ = ⊤` in `∀ i, M i` then `I • ⊤ = ⊤` in
each `M i`. Faithful flatness of a product is decided factorwise through this, since
`Module.FaithfullyFlat` is flatness together with `m • ⊤ ≠ ⊤` at every maximal ideal. -/
theorem smul_top_eq_top_of_pi (I : Ideal R) (h : I • (⊤ : Submodule R (∀ i, M i)) = ⊤) (i : ι) :
    I • (⊤ : Submodule R (M i)) = ⊤ := by
  have := congrArg (Submodule.map (LinearMap.proj (R := R) (φ := M) i)) h
  rwa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Function.surjective_eval i)] at this

end Pi

end Ideal

end
