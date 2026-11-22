/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Solvability of `PSL(n, R)`

`PSL(n, R)` is the quotient of `SL(n, R)` by its abelian center, so `PSL(n, R)` is solvable if
and only if `SL(n, R)` is solvable (`TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_iff`).
-/

public section

namespace TauCeti.Matrix.ProjectiveSpecialLinearGroup

/-- Since `PSL(n, R)` is the quotient of `SL(n, R)` by its abelian center, `PSL(n, R)` is solvable
if and only if `SL(n, R)` is solvable. -/
theorem isSolvable_iff (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    Group.IsSolvable (_root_.Matrix.ProjectiveSpecialLinearGroup n R) ↔
      Group.IsSolvable (_root_.Matrix.SpecialLinearGroup n R) :=
  ⟨fun _ ↦ Group.isSolvable_of_subgroup_quotient
    (Subgroup.center (_root_.Matrix.SpecialLinearGroup n R)), fun _ ↦ inferInstance⟩

end TauCeti.Matrix.ProjectiveSpecialLinearGroup
