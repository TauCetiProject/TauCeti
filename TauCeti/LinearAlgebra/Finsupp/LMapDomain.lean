/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Linear maps induced by permutations of the index type

A permutation `π` of `α` induces the linear endomorphism `Finsupp.lmapDomain M R π` of `α →₀ M`,
which moves the coefficient at `a` to `π a`. This file records that the powers of this
endomorphism are induced by the powers of `π`.

## Main results

* `Equiv.Perm.lmapDomain_pow`: `lmapDomain M R π ^ n = lmapDomain M R (π ^ n)`.
-/

public section

namespace Equiv.Perm

variable {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The powers of the linear map induced by a permutation are induced by its powers. -/
theorem lmapDomain_pow (π : Perm α) (n : ℕ) :
    Finsupp.lmapDomain M R π ^ n = Finsupp.lmapDomain M R ⇑(π ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, coe_one, Finsupp.lmapDomain_id, Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, coe_mul, Finsupp.lmapDomain_comp, Module.End.mul_eq_comp]

end Equiv.Perm
