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

Reversing the middle vector adds a half-turn: the real angles from `u` to `w` and from `-w` to `v`
add up to the real angle from `u` to `v` plus `π` whenever their sum is positive
(`Orientation.oangle_toReal_add_oangle_neg_left_toReal`). These are the signed exterior angles at
a point where the common boundary arc of two adjacent plane domains meets their outer boundary:
the two domains traverse the common arc in opposite directions, their interior angles add, and the
two exterior angles sum to the exterior angle of the union plus `π`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 9.
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

/-- **Exterior angles across a reversed edge.** For nonzero `u`, `w`, `v`, the real oriented
angles `α₁` from `u` to `w` and `α₂` from `-w` to `v` satisfy `α₁ + α₂ = α + π`, where `α` is the
real oriented angle from `u` to `v`, provided `0 < α₁ + α₂`. For the exterior angles of two
adjacent domains at an endpoint of their common boundary arc, this hypothesis says that the joined
interior angle `(π - α₁) + (π - α₂)` is less than `2π`. -/
theorem oangle_toReal_add_oangle_neg_left_toReal {u w v : V} (hu : u ≠ 0) (hw : w ≠ 0)
    (hv : v ≠ 0) (hpos : 0 < (o.oangle u w).toReal + (o.oangle (-w) v).toReal) :
    (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal + π := by
  set a := (o.oangle u w).toReal + (o.oangle (-w) v).toReal - π with ha
  have hangle : (a : Real.Angle) = o.oangle u v := by
    rw [ha, Real.Angle.coe_sub, Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal,
      o.oangle_neg_left hw hv, ← add_assoc, o.oangle_add hu hw hv, add_sub_cancel_right]
  have hmem : -π < a ∧ a ≤ π := by
    have h₁ := Real.Angle.toReal_le_pi (o.oangle u w)
    have h₂ := Real.Angle.toReal_le_pi (o.oangle (-w) v)
    constructor <;> linarith
  rw [← hangle, Real.Angle.toReal_coe_eq_self_iff.mpr hmem, ha]
  ring

end Orientation
