/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Oriented angles between three vectors with positive sign

For vectors `x`, `y`, `z` of an oriented real inner product space of dimension two such that
`y` and `z` make oriented angles of positive sign (i.e. in `(0, π)`) with `x`, Mathlib's
`Orientation.oangle_sub_left` gives `oangle y z = oangle x z - oangle x y`, and this identity
holds for the real representatives in `(-π, π]` as well (`Orientation.oangle_toReal_sub`, from
`Real.Angle.toReal_sub_of_sign_eq`). Consequently the real angles from `x` add
(`Orientation.oangle_toReal_add_of_sign_eq_one`), and the sign of `oangle y z` is the order of
the real angles of `y` and `z` measured from `x` (`Orientation.oangle_sign_eq_one_iff_toReal_lt`).
-/

public section

open Real

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- For two vectors `y`, `z` making oriented angles of positive sign with `x`, the real oriented
angle from `y` to `z` is the difference of their real angles from `x`. -/
theorem oangle_toReal_sub {x y z : V} (h₁ : (o.oangle x y).sign = 1)
    (h₂ : (o.oangle x z).sign = 1) :
    (o.oangle y z).toReal = (o.oangle x z).toReal - (o.oangle x y).toReal := by
  rw [← o.oangle_sub_left (o.left_ne_zero_of_oangle_sign_eq_one h₁)
    (o.right_ne_zero_of_oangle_sign_eq_one h₁) (o.right_ne_zero_of_oangle_sign_eq_one h₂)]
  exact Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 (by rw [h₁]; decide)).2
    (h₂.trans h₁.symm)

/-- For two vectors `y`, `z` making oriented angles of positive sign with `x`, the real angles from
`x` add: the angle to `z` is the angle to `y` plus the angle from `y` to `z`. -/
theorem oangle_toReal_add_of_sign_eq_one {x y z : V} (h₁ : (o.oangle x y).sign = 1)
    (h₂ : (o.oangle x z).sign = 1) :
    (o.oangle x z).toReal = (o.oangle x y).toReal + (o.oangle y z).toReal := by
  rw [o.oangle_toReal_sub h₁ h₂]
  ring

/-- For two vectors `y`, `z` making oriented angles of positive sign with `x`, the oriented angle
from `y` to `z` is positive exactly when the angle of `y` from `x` is smaller than that of `z`. -/
theorem oangle_sign_eq_one_iff_toReal_lt {x y z : V} (h₁ : (o.oangle x y).sign = 1)
    (h₂ : (o.oangle x z).sign = 1) :
    (o.oangle y z).sign = 1 ↔ (o.oangle x y).toReal < (o.oangle x z).toReal := by
  rw [← o.oangle_sub_left (o.left_ne_zero_of_oangle_sign_eq_one h₁)
    (o.right_ne_zero_of_oangle_sign_eq_one h₁) (o.right_ne_zero_of_oangle_sign_eq_one h₂)]
  exact Real.Angle.sign_sub_eq_one_iff_toReal_lt h₁ h₂

end Orientation
