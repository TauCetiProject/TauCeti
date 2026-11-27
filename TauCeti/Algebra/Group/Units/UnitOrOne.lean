/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Units.Hom

/-!
# The unit associated to an element, with identity as default

Assign an element its corresponding unit when it is invertible, and the identity otherwise.
For example, this labels integers by units modulo a cyclotomic order without restricting
prime sums to invertible residues in advance. The assignment respects powers and commutes
with maps that reflect invertibility.
-/

public section

namespace Units

variable {M N : Type*} [Monoid M] [Monoid N]

/-- The unit corresponding to `a`, or the identity if `a` is not a unit. -/
noncomputable def unitOrOne (a : M) : Mˣ := by
  classical
  exact if h : IsUnit a then h.unit else 1

/-- The underlying element of the label of an invertible element is that element. -/
@[simp] theorem val_unitOrOne_of_isUnit {a : M} (h : IsUnit a) :
    (unitOrOne a : M) = a := by
  simp [unitOrOne, h]

/-- Nonunits receive the identity label. -/
@[simp] theorem unitOrOne_of_not_isUnit {a : M} (h : ¬ IsUnit a) :
    unitOrOne a = 1 := by
  simp [unitOrOne, h]

/-- Labelling a unit recovers the original unit. -/
@[simp] theorem unitOrOne_val (u : Mˣ) : unitOrOne (u : M) = u :=
  Units.ext (val_unitOrOne_of_isUnit u.isUnit)

/-- The identity element receives the identity label. -/
@[simp] theorem unitOrOne_one : unitOrOne (1 : M) = 1 := by
  simpa only [Units.val_one] using unitOrOne_val (1 : Mˣ)

/-- The label of a power is the corresponding power of the label, even for nonunits. -/
@[simp] theorem unitOrOne_pow (a : M) (k : ℕ) : unitOrOne (a ^ k) = unitOrOne a ^ k := by
  obtain rfl | hk := eq_or_ne k 0
  · simp only [pow_zero, unitOrOne_one]
  by_cases ha : IsUnit a
  · apply Units.ext
    simp [val_unitOrOne_of_isUnit (ha.pow k), val_unitOrOne_of_isUnit ha]
  · rw [unitOrOne_of_not_isUnit (mt (isUnit_pow_iff hk).mp ha), unitOrOne_of_not_isUnit ha, one_pow]

/-- A nonidentity label occurs exactly at its underlying element. -/
theorem unitOrOne_eq_iff_of_ne_one {a : M} {u : Mˣ} (hu : u ≠ 1) :
    unitOrOne a = u ↔ a = (u : M) := by
  constructor
  · intro h
    have ha : IsUnit a := by
      by_contra hna
      exact hu (h.symm.trans (unitOrOne_of_not_isUnit hna))
    rw [← val_unitOrOne_of_isUnit ha, h]
  · rintro rfl
    exact unitOrOne_val u

/-- A monoid map commutes with unit labels if it reflects invertibility at the given element. -/
theorem map_unitOrOne (f : M →* N) (a : M) (h : IsUnit (f a) → IsUnit a) :
    Units.map f (unitOrOne a) = unitOrOne (f a) := by
  by_cases ha : IsUnit a
  · exact Units.ext (by simp [val_unitOrOne_of_isUnit ha, val_unitOrOne_of_isUnit (ha.map f)])
  · simp [unitOrOne_of_not_isUnit ha, unitOrOne_of_not_isUnit (mt h ha)]

end Units
