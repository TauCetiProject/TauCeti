/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.CSA

/-!
# `FreeGroup (Fin 2) × ℤ` is not CSA

The free group on two generators is nonabelian, but its product with a nontrivial abelian group
has a nonidentity central element. This provides a concrete test of commutation transitivity.
-/

public section

namespace Group

/-- The product of the free group on two generators with `ℤ` is not CSA. -/
theorem not_isCSA_prod_int :
    ¬ IsCSA (FreeGroup (Fin 2) × Multiplicative ℤ) := by
  apply not_isCSA_prod_of_nontrivial
  intro hcomm
  exact not_subsingleton (Fin 2) (FreeGroup.isMulCommutative_iff_subsingleton.mp hcomm)

end Group
