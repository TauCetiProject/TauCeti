/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Membership in the integer submodule of an additive subgroup

The integer submodule corresponding to an additive subgroup has the same elements.
-/

public section

/-- Membership is unchanged when an additive subgroup is viewed as an integer submodule. -/
@[simp]
theorem AddSubgroup.mem_toIntSubmodule {M : Type*} [AddCommGroup M]
    (S : AddSubgroup M) (x : M) : x ∈ S.toIntSubmodule ↔ x ∈ S :=
  Iff.rfl
