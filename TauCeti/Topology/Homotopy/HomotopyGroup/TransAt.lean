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
point whose `i`-th coordinate is replaced by any `a` with the rescaled value. It also evaluates
the reversal `GenLoop.symmAt i f`, and reads Mathlib's `HomotopyGroup.mul_spec`,
`HomotopyGroup.inv_spec` and `HomotopyGroup.one_def` in the additive group
`Additive (HomotopyGroup N X x)`.

## Main declarations

* `GenLoop.transAt_apply_of_le`: on the first half, `transAt i f g` runs `f` at double speed.
* `GenLoop.transAt_apply_of_lt`: on the second half, `transAt i f g` runs `g` at double speed.
* `GenLoop.symmAt_apply`: `symmAt i f` runs `f` backwards in the `i`-th direction.
* `HomotopyGroup.ofMul_transAt`, `HomotopyGroup.ofMul_symmAt` and `HomotopyGroup.ofMul_const`:
  concatenation, reversal and the constant loop in `Additive (HomotopyGroup N X x)`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N]

/-- On the first half of the `i`-th direction, `transAt i f g` runs `f` at double speed. -/
theorem transAt_apply_of_le (i : N) (f g : Ω^ N X x) {t : I^N} (h : (t i : ℝ) ≤ 1 / 2) {a : I}
    (ha : (a : ℝ) = 2 * t i) :
    transAt i f g t = f (Function.update t i a) := by
  simp only [transAt, coe_copy]
  rw [ite_eq_left h, Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ f (Function.update t i b)) (Subtype.ext ha.symm)

/-- On the second half of the `i`-th direction, `transAt i f g` runs `g` at double speed. -/
theorem transAt_apply_of_lt (i : N) (f g : Ω^ N X x) {t : I^N} (h : 1 / 2 < (t i : ℝ)) {a : I}
    (ha : (a : ℝ) = 2 * t i - 1) :
    transAt i f g t = g (Function.update t i a) := by
  simp only [transAt, coe_copy]
  rw [ite_eq_right (not_le.2 h), Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ g (Function.update t i b)) (Subtype.ext ha.symm)

/-- `symmAt i f` runs `f` backwards in the `i`-th direction. -/
@[simp]
theorem symmAt_apply (i : N) (f : Ω^ N X x) (t : I^N) :
    symmAt i f t = f (Function.update t i (σ (t i))) := by
  rw [symmAt, coe_copy]
  exact congrArg f (funext fun j ↦ (Function.update_apply t i _ j).symm)

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
-- Reduce the constant class before expanding its multiplicative representative.
@[simp↓ 1100]
theorem ofMul_const : Additive.ofMul (α := HomotopyGroup N X x) ⟦GenLoop.const⟧ = 0 := by
  rw [← one_def]
  rfl

end HomotopyGroup
