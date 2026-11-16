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
point whose `i`-th coordinate is replaced by any `a` with the rescaled value; on the seam
`tᵢ = 1/2` it is the base point. For spheres, the two halves of the square `I^(Fin 2)` along the
first coordinate are the images of affine maps of the square, and the concatenation
`transAt 0 q p` reads as `q` and `p` through them. The file also evaluates
the reversal `GenLoop.symmAt i f`, and reads Mathlib's `HomotopyGroup.mul_spec`,
`HomotopyGroup.inv_spec` and `HomotopyGroup.one_def` in the additive group
`Additive (HomotopyGroup N X x)`.

## Main declarations

* `GenLoop.transAt_apply_of_le`: on the first half, `transAt i f g` runs `f` at double speed.
* `GenLoop.transAt_apply_of_lt`: on the second half, `transAt i f g` runs `g` at double speed.
* `GenLoop.transAt_apply_of_coe_eq_half`: on the seam `tᵢ = 1/2`, `transAt i f g` is the base
  point.
* `TauCeti.squareLeftHalf`, `TauCeti.squareRightHalf`: the affine maps of the square `I^(Fin 2)`
  onto its left and right halves `s ≤ 1/2` and `s ≥ 1/2`.
* `GenLoop.transAt_apply_squareLeftHalf`, `GenLoop.transAt_apply_squareRightHalf`: the
  concatenation `transAt 0 q p` of two spheres runs `q` on the left half of the square and `p` on
  the right half.
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

/-- `symmAt i f` runs `f` backwards in the `i`-th direction. -/
@[simp]
theorem symmAt_apply (i : N) (f : Ω^ N X x) (t : I^N) :
    symmAt i f t = f (Function.update t i (σ (t i))) := by
  simp [symmAt, coe_copy, ← Function.update_apply]

end GenLoop

namespace TauCeti

/-! ### The halves of the square -/

/-- The affine map `(s, t) ↦ (s / 2, t)` of the square onto its left half. -/
noncomputable def squareLeftHalf : C(Fin 2 → I, Fin 2 → I) where
  toFun y := ![⟨(y 0 : ℝ) / 2, by linarith [unitInterval.nonneg (y 0)],
    by linarith [unitInterval.le_one (y 0)]⟩, y 1]
  continuous_toFun := by fun_prop

/-- The affine map `(s, t) ↦ ((s + 1) / 2, t)` of the square onto its right half. -/
noncomputable def squareRightHalf : C(Fin 2 → I, Fin 2 → I) where
  toFun y := ![⟨((y 0 : ℝ) + 1) / 2, by linarith [unitInterval.nonneg (y 0)],
    by linarith [unitInterval.le_one (y 0)]⟩, y 1]
  continuous_toFun := by fun_prop

@[simp]
theorem coe_squareLeftHalf_apply_zero (y : Fin 2 → I) :
    (squareLeftHalf y 0 : ℝ) = y 0 / 2 :=
  (rfl)

@[simp]
theorem squareLeftHalf_apply_one (y : Fin 2 → I) : squareLeftHalf y 1 = y 1 :=
  (rfl)

@[simp]
theorem coe_squareRightHalf_apply_zero (y : Fin 2 → I) :
    (squareRightHalf y 0 : ℝ) = (y 0 + 1) / 2 :=
  (rfl)

@[simp]
theorem squareRightHalf_apply_one (y : Fin 2 → I) : squareRightHalf y 1 = y 1 :=
  (rfl)

end TauCeti

namespace GenLoop

open TauCeti

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The concatenation `GenLoop.transAt 0 q p` runs `q` on the left half of the square. -/
theorem transAt_apply_squareLeftHalf (p q : Ω^ (Fin 2) X x) (y : Fin 2 → I) :
    transAt 0 q p (squareLeftHalf y) = q y := by
  have hle : ((squareLeftHalf y 0 : I) : ℝ) ≤ 1 / 2 := by
    simp only [coe_squareLeftHalf_apply_zero]
    linarith [unitInterval.le_one (y 0)]
  rw [transAt, coe_copy, ite_eq_left hle]
  congr 1
  funext i
  fin_cases i
  · have h2 : (2 : ℝ) * (squareLeftHalf y 0 : I) = y 0 := by
      rw [coe_squareLeftHalf_apply_zero]
      ring
    simp only [Fin.zero_eta, Function.update_self, h2, Set.projIcc_val]
  · simp

/-- The concatenation `GenLoop.transAt 0 q p` runs `p` on the right half of the square. -/
theorem transAt_apply_squareRightHalf (p q : Ω^ (Fin 2) X x) (y : Fin 2 → I) :
    transAt 0 q p (squareRightHalf y) = p y := by
  rw [transAt, coe_copy]
  split_ifs with hle
  · -- Only the left edge `s = 0` is mapped to the seam, and both sides are the base point there.
    have hy : (y 0 : ℝ) = 0 := by
      rw [coe_squareRightHalf_apply_zero] at hle
      linarith [unitInterval.nonneg (y 0)]
    have h2 : (2 : ℝ) * (squareRightHalf y 0 : I) = 1 := by
      rw [coe_squareRightHalf_apply_zero, hy]
      ring
    refine (boundary q _ ⟨0, Or.inr ?_⟩).trans (boundary p y ⟨0, Or.inl ?_⟩).symm
    · rw [Function.update_self, h2]
      exact Subtype.ext (by simp)
    · exact Subtype.ext hy
  · congr 1
    funext i
    fin_cases i
    · have h2 : (2 : ℝ) * (squareRightHalf y 0 : I) - 1 = y 0 := by
        rw [coe_squareRightHalf_apply_zero]
        ring
      simp only [Fin.zero_eta, Function.update_self, h2, Set.projIcc_val]
    · simp

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
