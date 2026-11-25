/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.Linarith

/-!
# The reflection of a closed real interval

The reflection `y ↦ a + b - y` of `[a, b]` is a strictly decreasing involutive homeomorphism.
For `[0, 1]` it is Mathlib's `unitInterval.symmHomeomorph`.

## Main definitions

* `TauCeti.iccReflect a b`: the reflection `y ↦ a + b - y` of `[a, b]`.

## Main results

* `TauCeti.iccReflect_iccReflect`, `TauCeti.iccReflect_symm`: the reflection is an involution.
* `TauCeti.strictAnti_iccReflect`: the reflection is strictly decreasing.
-/

public section

open Set

namespace TauCeti

variable {a b : ℝ}

/-- The reflection `y ↦ a + b - y` of `[a, b]`, a strictly decreasing involutive homeomorphism. -/
def iccReflect (a b : ℝ) : Icc a b ≃ₜ Icc a b where
  toFun y := ⟨a + b - y, by constructor <;> linarith [y.property.1, y.property.2]⟩
  invFun y := ⟨a + b - y, by constructor <;> linarith [y.property.1, y.property.2]⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_iccReflect_apply (y : Icc a b) : (iccReflect a b y : ℝ) = a + b - y :=
  (rfl)

@[simp]
theorem iccReflect_symm : (iccReflect a b).symm = iccReflect a b :=
  (rfl)

@[simp]
theorem iccReflect_iccReflect (y : Icc a b) : iccReflect a b (iccReflect a b y) = y :=
  (iccReflect a b).symm_apply_apply y

theorem strictAnti_iccReflect : StrictAnti (iccReflect a b) := fun _ _ h =>
  Subtype.coe_lt_coe.1 (by
    rw [coe_iccReflect_apply, coe_iccReflect_apply]
    linarith [Subtype.coe_lt_coe.2 h])

end TauCeti
