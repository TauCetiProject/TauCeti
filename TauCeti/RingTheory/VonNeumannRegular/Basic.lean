/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Von Neumann regularity under multiplication

A semigroup is von Neumann regular if each element `a` admits `b` with `a * b * a = a`.
This includes Boolean rings and is invariant under passing to the opposite semigroup.
-/

public section

namespace TauCeti

/-- A semigroup is von Neumann regular if each element `a` has an inner inverse `b`. -/
@[mk_iff]
class IsVonNeumannRegularRing (R : Type*) [Semigroup R] : Prop where
  exists_mul_mul_eq_self (a : R) : ∃ b : R, a * b * a = a

namespace IsVonNeumannRegularRing

variable {R : Type*}

/-- A Boolean ring is von Neumann regular. -/
instance [BooleanRing R] : IsVonNeumannRegularRing R :=
  ⟨fun a ↦ ⟨1, by simp [BooleanRing.mul_self]⟩⟩

variable [Semigroup R]

/-- Von Neumann regularity is invariant under passing to the opposite semigroup. -/
@[simp]
theorem mulOpposite_iff : IsVonNeumannRegularRing Rᵐᵒᵖ ↔ IsVonNeumannRegularRing R := by
  constructor
  · intro h
    constructor
    intro a
    obtain ⟨b, hb⟩ := h.exists_mul_mul_eq_self (MulOpposite.op a)
    refine ⟨b.unop, ?_⟩
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, mul_assoc]
      using congrArg MulOpposite.unop hb
  · intro h
    constructor
    intro a
    obtain ⟨b, hb⟩ := h.exists_mul_mul_eq_self a.unop
    exact ⟨MulOpposite.op b, MulOpposite.unop_injective (by simpa only
      [MulOpposite.unop_mul, MulOpposite.unop_op, mul_assoc] using hb)⟩

/-- The opposite of a von Neumann regular ring is von Neumann regular. -/
instance [IsVonNeumannRegularRing R] : IsVonNeumannRegularRing Rᵐᵒᵖ :=
  mulOpposite_iff.mpr inferInstance

end IsVonNeumannRegularRing

end TauCeti
