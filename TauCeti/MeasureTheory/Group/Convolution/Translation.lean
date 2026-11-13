/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.Power

/-!
# Translations of convolution laws

Translating two summands by `a` and `b` translates their convolution by `a + b`.
Consequently, translating each of `n` summands by `a` translates the convolution power by
`n • a`. These identities hold for measures on measurable commutative additive monoids,
including measures of arbitrary total mass and the zeroth convolution power.
-/

public section

open scoped MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddCommMonoid α] [MeasurableAdd₂ α]

/-- The convolution of translated measures is the translation of their convolution by the
sum of the two offsets. -/
theorem conv_map_add (μ ν : Measure α) [SFinite ν] (a b : α) :
    (μ.map (a + ·)) ∗ (ν.map (b + ·)) = (μ ∗ ν).map (a + b + ·) := by
  rw [conv, map_prod_map μ ν (measurable_const_add a) (measurable_const_add b),
    map_map measurable_add ((measurable_const_add a).prodMap (measurable_const_add b)), conv,
    map_map (measurable_const_add (a + b)) measurable_add]
  congr 1
  funext x
  simp [add_left_comm, add_comm]

/-- Translating each summand translates an `n`-fold convolution by `n` times the offset.
At `n = 0` both sides are the point mass at zero. -/
theorem convolutionPower_map_add (μ : Measure α) [SFinite μ] (a : α) (n : ℕ) :
    (μ.map (a + ·)).convolutionPower n = (μ.convolutionPower n).map (n • a + ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convolutionPower_succ, ih, conv_map_add, convolutionPower_succ, succ_nsmul]

end MeasureTheory.Measure
