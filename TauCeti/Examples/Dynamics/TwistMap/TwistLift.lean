/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.TwistLift
public import TauCeti.Topology.Order.IccReflect

/-!
# Examples of twist lifts of a closed strip

Checks for `TauCeti.IsTwistLift` on the closed strip `ℝ × [0, 1]` with period `1`
(Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, Section 9.2).

* The shear `(x, y) ↦ (x + y, y)` is a positive twist lift
  (`TauCeti.Examples.TwistLift.isTwistLift_shear`), and its inverse `(x, y) ↦ (x - y, y)` is a
  negative one: it commutes with the deck translation, preserves both boundary lines, and its
  first coordinate decreases in `y`.
* Conjugating the shear by the reflection `y ↦ 1 - y` of `[0, 1]` gives `(x, y) ↦ (x + 1 - y, y)`,
  a negative twist lift (`TauCeti.isTwistLift_symm_stripFiberConj_iff`).
* The rigid rotation `(x, y) ↦ (x + 1/4, y)` is not a twist lift: its first coordinate does not
  depend on `y`.
-/

public section

noncomputable section

open Set

namespace TauCeti.Examples.TwistLift

/-- The shear `(x, y) ↦ (x + y, y)` of the closed strip `ℝ × [0, 1]`. -/
def shear : ℝ × Icc (0 : ℝ) 1 ≃ₜ ℝ × Icc (0 : ℝ) 1 where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem shear_apply (p : ℝ × Icc (0 : ℝ) 1) : shear p = (p.1 + p.2, p.2) :=
  (rfl)

@[simp]
theorem shear_symm_apply (p : ℝ × Icc (0 : ℝ) 1) : shear.symm p = (p.1 - p.2, p.2) :=
  (rfl)

/-- The shear `(x, y) ↦ (x + y, y)` is a positive twist lift with period `1`. -/
theorem isTwistLift_shear : IsTwistLift 1 shear where
  apply_add_period p := by ext <;> simp; ring
  snd_apply_of_eq_left p hp := by simpa using hp
  snd_apply_of_eq_right p hp := by simpa using hp
  strictMono_fst_apply x y z h := by simpa using Subtype.coe_lt_coe.2 h

/-- The inverse shear `(x, y) ↦ (x - y, y)` is a negative twist lift: it commutes with the deck
translation, preserves both boundary lines, and its first coordinate decreases in `y`. -/
example :
    (∀ p : ℝ × Icc (0 : ℝ) 1,
        shear.symm (p.1 + 1, p.2) = ((shear.symm p).1 + 1, (shear.symm p).2)) ∧
      (∀ p : ℝ × Icc (0 : ℝ) 1, (p.2 : ℝ) = 0 → ((shear.symm p).2 : ℝ) = 0) ∧
      (∀ p : ℝ × Icc (0 : ℝ) 1, (p.2 : ℝ) = 1 → ((shear.symm p).2 : ℝ) = 1) ∧
      ∀ x : ℝ, StrictAnti fun y : Icc (0 : ℝ) 1 => (shear.symm (x, y)).1 :=
  (isTwistLift_symm_iff one_ne_zero).1 (by simpa using isTwistLift_shear)

/-- Conjugating the shear by the reflection `y ↦ 1 - y` of `[0, 1]` gives
`(x, y) ↦ (x + 1 - y, y)`. -/
example (p : ℝ × Icc (0 : ℝ) 1) :
    stripFiberConj (iccReflect 0 1) shear p = (p.1 + 1 - p.2, p.2) := by
  ext
  · simp; ring
  · simp

/-- The conjugate of the shear by the reflection `y ↦ 1 - y` is a negative twist lift. -/
example : IsTwistLift 1 (stripFiberConj (iccReflect 0 1) shear).symm :=
  (isTwistLift_symm_stripFiberConj_iff one_ne_zero strictAnti_iccReflect).2 isTwistLift_shear

/-- The rigid rotation `(x, y) ↦ (x + 1/4, y)` of the closed strip. -/
def rotation : ℝ × Icc (0 : ℝ) 1 ≃ₜ ℝ × Icc (0 : ℝ) 1 :=
  (Homeomorph.addRight (1 / 4 : ℝ)).prodCongr (Homeomorph.refl _)

/-- The rigid rotation `(x, y) ↦ (x + 1/4, y)` is not a twist lift: its first coordinate is
constant on every vertical. -/
example : ¬IsTwistLift 1 rotation := by
  intro h
  have := h.strictMono_fst_apply 0 (show (⟨0, by simp⟩ : Icc (0 : ℝ) 1) < ⟨1, by simp⟩ from
    Subtype.coe_lt_coe.1 (by simp))
  simp [rotation] at this

end TauCeti.Examples.TwistLift
