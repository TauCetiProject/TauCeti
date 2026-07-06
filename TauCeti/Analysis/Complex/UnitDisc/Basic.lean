/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Basic API for the complex unit disc

This file collects small API lemmas for Mathlib's `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open Complex

namespace Complex.UnitDisc

/-- Rotating the disc origin by a circle element fixes it. This is the `smul_zero`
normalization for Mathlib's `Circle` action on `Complex.UnitDisc`, which is a bare
`MulAction` and so does not get the generic `smul_zero` simp lemma. -/
@[simp]
lemma circle_smul_zero (u : Circle) : u • (0 : _root_.Complex.UnitDisc) = 0 := by
  ext
  simp

/-- A circle rotation of a disc point vanishes exactly when the point does. This is the
`smul_eq_zero` normalization for Mathlib's `Circle` action on `Complex.UnitDisc`. -/
@[simp]
lemma circle_smul_eq_zero_iff (u : Circle) {z : _root_.Complex.UnitDisc} :
    u • z = 0 ↔ z = 0 := by
  rw [← _root_.Complex.UnitDisc.coe_eq_zero, _root_.Complex.UnitDisc.coe_circle_smul, mul_eq_zero]
  simp

end Complex.UnitDisc

/-- A fixed circle rotation is continuous on the bundled open disc. -/
lemma continuous_circle_smul_unitDisc (u : Circle) :
    Continuous fun z : Complex.UnitDisc => u • z := by
  rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
  -- The embedding criterion reduces continuity to the scalar coercion of the bundled disc.
  change Continuous fun z : Complex.UnitDisc => ((u • z : Complex.UnitDisc) : ℂ)
  simp only [Complex.UnitDisc.coe_circle_smul]
  exact continuous_const.mul Complex.UnitDisc.continuous_coe

/-- Circle rotations act continuously on the bundled open unit disc. -/
instance instContinuousConstSMulCircleUnitDisc :
    ContinuousConstSMul Circle Complex.UnitDisc where
  continuous_const_smul := continuous_circle_smul_unitDisc

end TauCeti
