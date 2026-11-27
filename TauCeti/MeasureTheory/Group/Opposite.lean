/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Invariant measures on the opposite magma

Right multiplication on the original magma becomes left multiplication on its opposite.
-/

public section

namespace MeasureTheory

open MulOpposite in
/-- Sending a right-invariant measure to the opposite magma makes it left-invariant. -/
@[to_additive /-- Sending a right-addition-invariant measure to the additive opposite makes it
left-addition-invariant. -/]
instance Measure.isMulLeftInvariant_map_op
    {G : Type*} [Mul G] [MeasurableSpace G] [MeasurableConstSMul Gᵐᵒᵖ G]
    (ν : Measure G) [ν.IsMulRightInvariant] : (Measure.map op ν).IsMulLeftInvariant := by
  have hr (a : G) : Measurable (· * a) := measurable_const_smul (op a)
  refine ⟨fun g ↦ ?_⟩
  have hl : Measurable (g * ·) := measurable_mul_op.comp ((hr (unop g)).comp measurable_mul_unop)
  have hcomp : (g * ·) ∘ op = op ∘ (· * unop g) := by
    funext s
    rw [Function.comp_apply, Function.comp_apply, MulOpposite.op_mul, op_unop]
  rw [Measure.map_map hl measurable_mul_op, hcomp,
    ← Measure.map_map measurable_mul_op (hr (unop g)),
    map_mul_right_eq_self]

end MeasureTheory
