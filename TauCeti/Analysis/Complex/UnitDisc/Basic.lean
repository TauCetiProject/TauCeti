/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic

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

end TauCeti
