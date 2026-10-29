/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Commute

/-!
# Commutation with `1 - a • u`

An element of a ring commuting with `u` also commutes with `1 - a • u`, for any scalar `a` acting
compatibly with the multiplication. For an operator `u`, `1 - a • u` is the operator whose
generalised kernel at a zero `a` of the Fredholm determinant of `u` carries the Riesz projector.
-/

public section

namespace Commute

variable {R A : Type*} [Ring A] [SMul R A] [IsScalarTower R A A] [SMulCommClass R A A] {u x : A}

/-- An element commuting with `u` commutes with `1 - a • u`, on the left. -/
theorem one_sub_smul_left (h : Commute u x) (a : R) : Commute (1 - a • u) x :=
  (Commute.one_left x).sub_left (h.smul_left a)

/-- An element commuting with `u` commutes with `1 - a • u`, on the right. -/
theorem one_sub_smul_right (h : Commute x u) (a : R) : Commute x (1 - a • u) :=
  (h.symm.one_sub_smul_left a).symm

end Commute
