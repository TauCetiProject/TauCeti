/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Evaluating concatenations and reversals of generalized loops

Mathlib's `GenLoop.transAt i f g` concatenates two generalized loops along the `i`-th cube
direction, running `f` on `tᵢ ≤ 1/2` and `g` on `tᵢ ≥ 1/2`, each at double speed. Its defining
formula clamps the rescaled coordinate with `Set.projIcc`. This file states the two halves of
that formula without the clamp: on each half, the concatenation is `f` or `g` evaluated at the
point whose `i`-th coordinate is replaced by any `a` with the rescaled value. Conversely, the maps
`TauCeti.Cube.firstHalf i` and `TauCeti.Cube.secondHalf i` of the cube onto its two halves in the
`i`-th direction pull the concatenation back to `f` and to `g`. It also evaluates
the reversal `GenLoop.symmAt i f`, and reads Mathlib's `HomotopyGroup.mul_spec`,
`HomotopyGroup.inv_spec` and `HomotopyGroup.one_def` in the additive group
`Additive (HomotopyGroup N X x)`.

## Main declarations

* `GenLoop.transAt_apply_of_le`: on the first half, `transAt i f g` runs `f` at double speed.
* `GenLoop.transAt_apply_of_lt`: on the second half, `transAt i f g` runs `g` at double speed.
* `TauCeti.Cube.firstHalf`, `TauCeti.Cube.secondHalf`: the maps of the cube onto its two halves
  in the `i`-th direction, with their coordinates `TauCeti.Cube.coe_firstHalf_apply_self`,
  `TauCeti.Cube.firstHalf_apply_of_ne` and their analogues for `secondHalf`.
* `GenLoop.transAt_firstHalf`, `GenLoop.transAt_secondHalf`: `transAt i f g` restricts to `f` and
  to `g` on the two halves.
* `GenLoop.symmAt_apply`: `symmAt i f` runs `f` backwards in the `i`-th direction.
* `HomotopyGroup.ofMul_transAt`, `HomotopyGroup.ofMul_symmAt` and `HomotopyGroup.ofMul_const`:
  concatenation, reversal and the constant loop in `Additive (HomotopyGroup N X x)`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace TauCeti.Cube

variable {N : Type*} [DecidableEq N]

/-- The map of the cube onto its first half `y i ≤ 1 / 2` in the `i`-th direction, halving the
`i`-th coordinate. -/
noncomputable def firstHalf (i : N) (y : I^N) : I^N :=
  Function.update y i (Set.projIcc 0 1 zero_le_one ((y i : ℝ) / 2))

/-- The map of the cube onto its second half `1 / 2 ≤ y i` in the `i`-th direction, the affine
map `s ↦ (s + 1) / 2` in the `i`-th coordinate. -/
noncomputable def secondHalf (i : N) (y : I^N) : I^N :=
  Function.update y i (Set.projIcc 0 1 zero_le_one (((y i : ℝ) + 1) / 2))

theorem firstHalf_apply (i : N) (y : I^N) :
    firstHalf i y = Function.update y i (Set.projIcc 0 1 zero_le_one ((y i : ℝ) / 2)) :=
  (rfl)

theorem secondHalf_apply (i : N) (y : I^N) :
    secondHalf i y = Function.update y i (Set.projIcc 0 1 zero_le_one (((y i : ℝ) + 1) / 2)) :=
  (rfl)

/-- The `i`-th coordinate of `firstHalf i y` is half the `i`-th coordinate of `y`. -/
@[simp]
theorem coe_firstHalf_apply_self (i : N) (y : I^N) : (firstHalf i y i : ℝ) = y i / 2 := by
  rw [firstHalf_apply, Function.update_self,
    Set.projIcc_of_mem _ ⟨by linarith [(y i).2.1], by linarith [(y i).2.2]⟩]

/-- The `i`-th coordinate of `secondHalf i y` is `(y i + 1) / 2`. -/
@[simp]
theorem coe_secondHalf_apply_self (i : N) (y : I^N) :
    (secondHalf i y i : ℝ) = (y i + 1) / 2 := by
  rw [secondHalf_apply, Function.update_self,
    Set.projIcc_of_mem _ ⟨by linarith [(y i).2.1], by linarith [(y i).2.2]⟩]

/-- The coordinates of `firstHalf i y` other than the `i`-th are those of `y`. -/
@[simp]
theorem firstHalf_apply_of_ne {i j : N} (h : j ≠ i) (y : I^N) : firstHalf i y j = y j :=
  Function.update_of_ne h _ _

/-- The coordinates of `secondHalf i y` other than the `i`-th are those of `y`. -/
@[simp]
theorem secondHalf_apply_of_ne {i j : N} (h : j ≠ i) (y : I^N) : secondHalf i y j = y j :=
  Function.update_of_ne h _ _

@[fun_prop]
theorem continuous_firstHalf (i : N) : Continuous (firstHalf i) :=
  continuous_id.update i (continuous_projIcc.comp (by fun_prop))

@[fun_prop]
theorem continuous_secondHalf (i : N) : Continuous (secondHalf i) :=
  continuous_id.update i (continuous_projIcc.comp (by fun_prop))

end TauCeti.Cube

namespace GenLoop

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

/-- The concatenation `transAt i f g` restricts to `f` on the first half of the cube in the `i`-th
direction. -/
theorem transAt_firstHalf (i : N) (f g : Ω^ N X x) (y : I^N) :
    transAt i f g (TauCeti.Cube.firstHalf i y) = f y := by
  have h := TauCeti.Cube.coe_firstHalf_apply_self i y
  rw [transAt_apply_of_le i f g (a := y i) (by rw [h]; linarith [(y i).2.2]) (by rw [h]; ring),
    TauCeti.Cube.firstHalf_apply, Function.update_idem, Function.update_eq_self]

/-- The concatenation `transAt i f g` restricts to `g` on the second half of the cube in the `i`-th
direction. -/
theorem transAt_secondHalf (i : N) (f g : Ω^ N X x) (y : I^N) :
    transAt i f g (TauCeti.Cube.secondHalf i y) = g y := by
  have h := TauCeti.Cube.coe_secondHalf_apply_self i y
  rcases (y i).2.1.eq_or_lt with h0 | h0
  · -- On the seam `y i = 0` both loops take the base point value.
    rw [transAt_apply_of_le i f g (a := 1) (by rw [h, ← h0]; norm_num) (by rw [h, ← h0]; norm_num),
      GenLoop.boundary f _ ⟨i, Or.inr (Function.update_self ..)⟩,
      GenLoop.boundary g y ⟨i, Or.inl (Subtype.ext h0.symm)⟩]
  · rw [transAt_apply_of_lt i f g (a := y i) (by rw [h]; linarith) (by rw [h]; ring),
      TauCeti.Cube.secondHalf_apply, Function.update_idem, Function.update_eq_self]

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
