/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The subgroup of even Dirichlet characters

A Dirichlet character `χ` of level `n` is even when `χ (-1) = 1` (`DirichletCharacter.Even`).
The even characters form a subgroup of the group of Dirichlet characters of level `n`: the
characters trivial on the subgroup `{±1}` of `(ℤ/nℤ)ˣ`. Under the character correspondence for
the `n`-th cyclotomic field it is the subgroup attached to the maximal real subfield.

## Main definitions

* `TauCeti.DirichletCharacter.evenSubgroup`: the subgroup of even Dirichlet characters of level `n`.

## Main statements

* `DirichletCharacter.mem_evenSubgroup_iff`: membership in `evenSubgroup` is evenness.
-/

public section

namespace TauCeti.DirichletCharacter

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The subgroup of even Dirichlet characters of level `n`, those with `χ (-1) = 1`. -/
def evenSubgroup : Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ.Even}
  mul_mem' {χ ψ} (hχ : χ.Even) (hψ : ψ.Even) := by
    rw [Set.mem_ofPred_eq, DirichletCharacter.Even, MulChar.mul_apply, hχ, hψ, mul_one]
  one_mem' := MulChar.one_apply isUnit_one.neg
  inv_mem' {χ} (hχ : χ.Even) := by
    rw [Set.mem_ofPred_eq, DirichletCharacter.Even, MulChar.inv_apply_eq_inv, hχ,
      Ring.inverse_one]

end TauCeti.DirichletCharacter

namespace DirichletCharacter

variable {R : Type*} [CommRing R] {n : ℕ}

@[simp]
theorem mem_evenSubgroup_iff (χ : DirichletCharacter R n) :
    χ ∈ TauCeti.DirichletCharacter.evenSubgroup R n ↔ χ.Even :=
  Iff.rfl

end DirichletCharacter
