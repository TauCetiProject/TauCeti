/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Commute

/-!
# Alternating signs preserve additive subgroups

A sign `(-1) ^ j` from a ring of scalars acts on a module as `1` or as negation, so it maps every
additive subgroup of the module into itself (`TauCeti.neg_one_pow_smul_mem`), even one that is not
closed under the scalar action. Alternating sums such as boundaries of cubes and simplices have
this form.
-/

public section

namespace TauCeti

/-- A sign `(-1) ^ j` from the scalars preserves membership in any set closed under negation, such
as an additive subgroup. -/
theorem neg_one_pow_smul_mem {R M S : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [SetLike S M] [NegMemClass S M] {H : S} {x : M} (hx : x ∈ H) (j : ℕ) :
    ((-1 : R) ^ j) • x ∈ H := by
  rcases neg_one_pow_eq_or R j with h | h <;> simp [h, hx]

end TauCeti
