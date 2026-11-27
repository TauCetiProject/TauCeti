/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# An additive subgroup as a `ℤ`-submodule

An additive subgroup `S` of an additive commutative group and the `ℤ`-submodule
`S.toIntSubmodule` have the same elements, so they are `ℤ`-linearly equivalent
(`AddSubgroup.toIntSubmoduleEquiv`). Module-theoretic facts about one transfer to the other.

## Main definitions

* `AddSubgroup.toIntSubmoduleEquiv`: the `ℤ`-linear equivalence `S.toIntSubmodule ≃ₗ[ℤ] S`.
-/

public section

variable {M : Type*} [AddCommGroup M]

namespace AddSubgroup

/-- An additive subgroup and its `ℤ`-submodule have the same elements, so they are `ℤ`-linearly
equivalent. -/
def toIntSubmoduleEquiv (S : AddSubgroup M) : S.toIntSubmodule ≃ₗ[ℤ] S where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := Subtype.ext (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_toIntSubmoduleEquiv_apply (S : AddSubgroup M) (x : S.toIntSubmodule) :
    (S.toIntSubmoduleEquiv x : M) = x :=
  (rfl)

@[simp]
theorem coe_toIntSubmoduleEquiv_symm_apply (S : AddSubgroup M) (x : S) :
    (S.toIntSubmoduleEquiv.symm x : M) = x :=
  (rfl)

end AddSubgroup
