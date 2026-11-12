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
`n • a`. The identity `MeasureTheory.Measure.conv_map_const_add` requires the second measure
to be s-finite, while `MeasureTheory.Measure.convolutionPower_map_const_add` requires the
original measure to be s-finite. They apply on measurable commutative additive monoids,
allow arbitrary total mass, and include the zeroth convolution power. The binary identity also
has a multiplicative form, `MeasureTheory.Measure.mconv_map_const_mul`, on commutative monoids.

Nonzero translations are not additive homomorphisms, so
`MeasureTheory.Measure.map_conv_addMonoidHom` and `MeasureTheory.Measure.map_convolutionPower`
do not transport the shifts needed for affine convolution laws. These translation identities
supply that step.
-/

public section

open scoped MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Multiplying two measures by constants multiplies their multiplicative convolution by
the product of those constants. -/
@[to_additive /-- The convolution of translated measures is the translation
of their convolution by the sum of the two offsets. -/]
theorem mconv_map_const_mul [CommMonoid α] [MeasurableMul₂ α]
    (μ ν : Measure α) [SFinite ν] (a b : α) :
    (μ.map (a * ·)) ∗ₘ (ν.map (b * ·)) = (μ ∗ₘ ν).map (a * b * ·) := by
  rw [mconv, map_prod_map μ ν (measurable_const_mul a) (measurable_const_mul b),
    map_map measurable_mul ((measurable_const_mul a).prodMap (measurable_const_mul b)), mconv,
    map_map (measurable_const_mul (a * b)) measurable_mul]
  congr 1
  funext x
  simp [mul_left_comm, mul_comm]

variable [AddCommMonoid α] [MeasurableAdd₂ α]

/-- Translating each summand translates an `n`-fold convolution by `n` times the offset.
At `n = 0` both sides are the point mass at zero. -/
theorem convolutionPower_map_const_add (μ : Measure α) [SFinite μ] (a : α) (n : ℕ) :
    (μ.map (a + ·)).convolutionPower n = (μ.convolutionPower n).map (n • a + ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convolutionPower_succ, ih, conv_map_const_add, convolutionPower_succ, succ_nsmul]

end MeasureTheory.Measure
