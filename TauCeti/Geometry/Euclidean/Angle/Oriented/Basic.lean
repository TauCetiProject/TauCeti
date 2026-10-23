/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Oriented angles between three vectors of a common nonzero sign

For vectors `x`, `y`, `z` of an oriented real inner product space of dimension two such that
`y` and `z` lie on the same open side of the line through `x` — their oriented angles from `x`
have the same nonzero sign — Mathlib's `Orientation.oangle_sub_left` gives
`oangle y z = oangle x z - oangle x y`, and this identity holds for the real representatives in
`(-π, π]` as well (`Orientation.oangle_toReal_sub_of_sign_eq`, from
`Real.Angle.toReal_sub_of_sign_eq`). Consequently the real angles from `x` add
(`Orientation.oangle_toReal_add_of_sign_eq`), and `oangle y z` has positive sign exactly when the
real angle of `y` from `x` is smaller than that of `z`
(`Orientation.oangle_sign_eq_one_iff_toReal_lt_of_sign_eq`).
-/

public section

open Real

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- For two vectors `y`, `z` on the same open side of the line through `x` (their oriented angles
from `x` have the same nonzero sign), the real oriented angle from `y` to `z` is the difference of
their real angles from `x`. -/
theorem oangle_toReal_sub_of_sign_eq {x y z : V} (hs : (o.oangle x y).sign = (o.oangle x z).sign)
    (h0 : (o.oangle x y).sign ≠ 0) :
    (o.oangle y z).toReal = (o.oangle x z).toReal - (o.oangle x y).toReal := by
  rw [← o.oangle_sub_left (o.left_ne_zero_of_oangle_sign_ne_zero h0)
    (o.right_ne_zero_of_oangle_sign_ne_zero h0) (o.right_ne_zero_of_oangle_sign_ne_zero (hs ▸ h0))]
  exact Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 h0).2 hs.symm

/-- For two vectors `y`, `z` on the same open side of the line through `x`, the real angles from `x`
add: the angle to `z` is the angle to `y` plus the angle from `y` to `z`. -/
theorem oangle_toReal_add_of_sign_eq {x y z : V} (hs : (o.oangle x y).sign = (o.oangle x z).sign)
    (h0 : (o.oangle x y).sign ≠ 0) :
    (o.oangle x z).toReal = (o.oangle x y).toReal + (o.oangle y z).toReal := by
  rw [o.oangle_toReal_sub_of_sign_eq hs h0]
  ring

/-- For two vectors `y`, `z` on the same open side of the line through `x`, the oriented angle from
`y` to `z` is positive exactly when the angle of `y` from `x` is smaller than that of `z`. -/
theorem oangle_sign_eq_one_iff_toReal_lt_of_sign_eq {x y z : V}
    (hs : (o.oangle x y).sign = (o.oangle x z).sign) (h0 : (o.oangle x y).sign ≠ 0) :
    (o.oangle y z).sign = 1 ↔ (o.oangle x y).toReal < (o.oangle x z).toReal := by
  rw [← o.oangle_sub_left (o.left_ne_zero_of_oangle_sign_ne_zero h0)
    (o.right_ne_zero_of_oangle_sign_ne_zero h0) (o.right_ne_zero_of_oangle_sign_ne_zero (hs ▸ h0))]
  exact Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq hs h0

end Orientation
