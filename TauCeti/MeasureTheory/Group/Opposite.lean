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
theorem Measure.IsMulRightInvariant.isMulLeftInvariant_map_op
    {G : Type*} [Mul G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulRightInvariant] : (Measure.map op ν).IsMulLeftInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have hcomp : (g * ·) ∘ op = op ∘ (· * unop g) := by
    funext s
    rw [Function.comp_apply, Function.comp_apply, MulOpposite.op_mul, op_unop]
  rw [Measure.map_map (measurable_const_mul g) measurable_mul_op, hcomp,
    ← Measure.map_map measurable_mul_op (measurable_mul_const (unop g)),
    map_mul_right_eq_self]

end MeasureTheory
