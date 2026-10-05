/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel

/-!
# Cancelling a unit from an affine combination

If `u` is a unit of the scalar ring, then `x = u • y + (1 - u) • x` forces `x = y`: the equation
says `u • (x - y) = 0`. Such equations arise as module relations whose two sides share a term,
for example the relation of an under-strand at a crossing of a link diagram whose incoming arc is
also its outgoing arc.
-/

public section

namespace TauCeti

/-- If `u` is a unit, then `x = u • y + (1 - u) • x` forces `x = y`. -/
theorem _root_.IsUnit.eq_of_eq_smul_add_one_sub_smul {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {u : R} (hu : IsUnit u) {x y : M} (h : x = u • y + (1 - u) • x) : x = y := by
  have h' : u • (x - y) = 0 := calc
    u • (x - y) = x - (u • y + (1 - u) • x) := by rw [smul_sub, sub_smul, one_smul]; abel
    _ = 0 := by rw [← h, sub_self]
  exact sub_eq_zero.1 (hu.smul_eq_zero.1 h')

end TauCeti
