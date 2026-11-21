/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Evaluating concatenations and reversals of generalized loops

Mathlib's `GenLoop.transAt i f g` concatenates two generalized loops along the `i`-th cube
direction, running `f` on `tᵢ ≤ 1/2` and `g` on `tᵢ ≥ 1/2`, each at double speed. Its defining
formula clamps the rescaled coordinate with `Set.projIcc`. This file states the two halves of
that formula without the clamp: on each half, the concatenation is `f` or `g` evaluated at the
point whose `i`-th coordinate is replaced by any `a` with the rescaled value; on the seam
`tᵢ = 1/2` it is the base point. Read through the affine maps `TauCeti.cubeLeftHalf i` and
`TauCeti.cubeRightHalf i` of the cube onto these halves, the concatenation is `f` and `g`
themselves. The file also evaluates
the reversal `GenLoop.symmAt i f`, and reads Mathlib's `HomotopyGroup.mul_spec`,
`HomotopyGroup.inv_spec` and `HomotopyGroup.one_def` in the additive group
`Additive (HomotopyGroup N X x)`.

## Main declarations

* `GenLoop.transAt_apply_of_le`: on the first half, `transAt i f g` runs `f` at double speed.
* `GenLoop.transAt_apply_of_lt`: on the second half, `transAt i f g` runs `g` at double speed.
* `GenLoop.transAt_apply_of_coe_eq_half`: on the seam `tᵢ = 1/2`, `transAt i f g` is the base
  point.
* `GenLoop.transAt_apply_cubeLeftHalf`, `GenLoop.transAt_apply_cubeRightHalf`: through the
  halving maps of the cube, `transAt i f g` is `f` on the first half and `g` on the second.
* `GenLoop.symmAt_apply`: `symmAt i f` runs `f` backwards in the `i`-th direction.
* `HomotopyGroup.ofMul_transAt`, `HomotopyGroup.ofMul_symmAt` and `HomotopyGroup.ofMul_const`:
  concatenation, reversal and the constant loop in `Additive (HomotopyGroup N X x)`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

open TauCeti

variable {N X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N]

/-- On the first half of the `i`-th direction, `transAt i f g` runs `f` at double speed. -/
theorem transAt_apply_of_le (i : N) (f g : Ω^ N X x) {t : I^N} (h : (t i : ℝ) ≤ 1 / 2) {a : I}
    (ha : (a : ℝ) = 2 * t i) :
    transAt i f g t = f (Function.update t i a) := by
  rw [one_div] at h
  simp [transAt, coe_copy, h, ← ha]

/-- On the second half of the `i`-th direction, `transAt i f g` runs `g` at double speed. -/
theorem transAt_apply_of_lt (i : N) (f g : Ω^ N X x) {t : I^N} (h : 1 / 2 < (t i : ℝ)) {a : I}
    (ha : (a : ℝ) = 2 * t i - 1) :
    transAt i f g t = g (Function.update t i a) := by
  rw [one_div] at h
  simp [transAt, coe_copy, h.not_ge, ← ha]

/-- On the seam `tᵢ = 1/2`, `transAt i f g` is the base point. -/
theorem transAt_apply_of_coe_eq_half (i : N) (f g : Ω^ N X x) {t : I^N}
    (h : (t i : ℝ) = 1 / 2) : transAt i f g t = x := by
  rw [transAt_apply_of_le i f g h.le (a := 1) (by rw [h]; norm_num)]
  exact boundary f _ ⟨i, Or.inr (by simp)⟩

/-- The concatenation `transAt i f g` runs `f` on the half `tᵢ ≤ 1/2` of the cube, read through
`TauCeti.cubeLeftHalf i`. -/
theorem transAt_apply_cubeLeftHalf (i : N) (f g : Ω^ N X x) (y : I^N) :
    transAt i f g (cubeLeftHalf i y) = f y := by
  rw [transAt_apply_of_le i f g (a := y i)
    (by rw [coe_cubeLeftHalf_apply_self]; linarith [unitInterval.le_one (y i)])
    (by rw [coe_cubeLeftHalf_apply_self]; ring), update_cubeLeftHalf_self]

/-- The concatenation `transAt i f g` runs `g` on the half `tᵢ ≥ 1/2` of the cube, read through
`TauCeti.cubeRightHalf i`. -/
theorem transAt_apply_cubeRightHalf (i : N) (f g : Ω^ N X x) (y : I^N) :
    transAt i f g (cubeRightHalf i y) = g y := by
  rcases (unitInterval.nonneg (y i)).eq_or_lt with h | h
  · -- Only the face `tᵢ = 0` is mapped to the seam, where both sides are the base point.
    rw [transAt_apply_of_coe_eq_half i f g (by rw [coe_cubeRightHalf_apply_self, ← h]; ring)]
    exact (boundary g y ⟨i, Or.inl (Subtype.ext h.symm)⟩).symm
  · rw [transAt_apply_of_lt i f g (a := y i)
      (by rw [coe_cubeRightHalf_apply_self]; linarith)
      (by rw [coe_cubeRightHalf_apply_self]; ring), update_cubeRightHalf_self]

/-- `symmAt i f` runs `f` backwards in the `i`-th direction. -/
@[simp]
theorem symmAt_apply (i : N) (f : Ω^ N X x) (t : I^N) :
    symmAt i f t = f (Function.update t i (σ (t i))) := by
  simp [symmAt, coe_copy, ← Function.update_apply]

end GenLoop

namespace HomotopyGroup

variable {N X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] [Nonempty N]

/-- Concatenation in the `i`-th direction is addition in `Additive (HomotopyGroup N X x)`, with
the summands in the order of `HomotopyGroup.mul_spec`. -/
@[simp]
theorem ofMul_transAt (i : N) (p q : Ω^ N X x) :
    Additive.ofMul (α := HomotopyGroup N X x) ⟦GenLoop.transAt i p q⟧ =
      Additive.ofMul (α := HomotopyGroup N X x) ⟦q⟧ +
        Additive.ofMul (α := HomotopyGroup N X x) ⟦p⟧ := by
  rw [← mul_spec]
  rfl

/-- Reversal in the `i`-th direction is negation in `Additive (HomotopyGroup N X x)`. -/
@[simp]
theorem ofMul_symmAt (i : N) (p : Ω^ N X x) :
    Additive.ofMul (α := HomotopyGroup N X x) ⟦GenLoop.symmAt i p⟧ =
      -Additive.ofMul (α := HomotopyGroup N X x) ⟦p⟧ := by
  rw [← inv_spec]
  rfl

/-- The class of the constant loop is zero in `Additive (HomotopyGroup N X x)`. -/
theorem ofMul_const : Additive.ofMul (α := HomotopyGroup N X x) ⟦GenLoop.const⟧ = 0 := by
  rw [← one_def]
  rfl

end HomotopyGroup
