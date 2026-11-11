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

Reversing the middle vector adds a half-turn: modulo `2π`, the angles from `u` to `w` and from
`-w` to `v` add up to the angle from `u` to `v` plus `π` (`Orientation.oangle_add_oangle_neg_left`).
The sum of the real representatives of the first two angles is therefore the real representative
of the third one plus `π` or minus `π`
(`Orientation.oangle_toReal_add_oangle_neg_left_toReal_eq_add_pi_or_eq_sub_pi`): plus `π` exactly
when this sum is positive (`Orientation.oangle_toReal_add_oangle_neg_left_toReal`,
`Orientation.oangle_toReal_add_oangle_neg_left_toReal_eq_add_pi_iff`), and minus `π` exactly when
it is nonpositive (`Orientation.oangle_toReal_add_oangle_neg_left_toReal_eq_sub_pi_iff`). These
are the general facts `Real.Angle.toReal_add_toReal_eq_add_pi_or_eq_sub_pi`,
`Real.Angle.toReal_add_toReal_eq_add_pi_iff` and `Real.Angle.toReal_add_toReal_eq_sub_pi_iff` about
angles `θ₁ + θ₂ = θ + π`, applied to the half-turn law.

These are the signed exterior angles at a point where the common boundary arc of two adjacent
plane domains meets their outer boundary: the two domains traverse the common arc in opposite
directions, and the interior angle at a corner is `π` minus the exterior angle. In the first case
the interior angles of the two domains add up to the interior angle of the union, so that the two
exterior angles sum to the exterior angle of the union plus `π`. In the second case the interior
angles of the two domains add up to at least `2π`.

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

/-- Reversing the middle vector adds a half-turn: for nonzero `u`, `w`, `v`, the oriented angles
from `u` to `w` and from `-w` to `v` add up to the oriented angle from `u` to `v` plus `π`. -/
theorem oangle_add_oangle_neg_left {u w v : V} (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0) :
    o.oangle u w + o.oangle (-w) v = o.oangle u v + π := by
  rw [o.oangle_neg_left hw hv, ← add_assoc, o.oangle_add hu hw hv]

/-- **Exterior angles across a reversed edge.** For nonzero `u`, `w`, `v`, the real oriented
angles `α₁` from `u` to `w` and `α₂` from `-w` to `v` satisfy `α₁ + α₂ = α + π`, where `α` is the
real oriented angle from `u` to `v`, provided `0 < α₁ + α₂`. For the exterior angles of two
adjacent domains at an endpoint of their common boundary arc, this hypothesis says that the joined
interior angle `(π - α₁) + (π - α₂)` is less than `2π`. -/
theorem oangle_toReal_add_oangle_neg_left_toReal {u w v : V} (hu : u ≠ 0) (hw : w ≠ 0)
    (hv : v ≠ 0) (hpos : 0 < (o.oangle u w).toReal + (o.oangle (-w) v).toReal) :
    (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal + π :=
  (Real.Angle.toReal_add_toReal_eq_add_pi_iff (o.oangle_add_oangle_neg_left hu hw hv)).2 hpos

/-- For nonzero `u`, `w`, `v`, the real oriented angles `α₁` from `u` to `w` and `α₂` from `-w` to
`v` satisfy `α₁ + α₂ = α + π`, where `α` is the real oriented angle from `u` to `v`, if and only if
`0 < α₁ + α₂`. -/
theorem oangle_toReal_add_oangle_neg_left_toReal_eq_add_pi_iff {u w v : V} (hu : u ≠ 0)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal + π ↔
      0 < (o.oangle u w).toReal + (o.oangle (-w) v).toReal :=
  Real.Angle.toReal_add_toReal_eq_add_pi_iff (o.oangle_add_oangle_neg_left hu hw hv)

/-- For nonzero `u`, `w`, `v`, the real oriented angles `α₁` from `u` to `w` and `α₂` from `-w` to
`v` satisfy `α₁ + α₂ = α - π`, where `α` is the real oriented angle from `u` to `v`, if and only if
`α₁ + α₂ ≤ 0`. For the exterior angles of two adjacent domains at an endpoint of their common
boundary arc, this condition says that the joined interior angle `(π - α₁) + (π - α₂)` is at least
`2π`. -/
theorem oangle_toReal_add_oangle_neg_left_toReal_eq_sub_pi_iff {u w v : V} (hu : u ≠ 0)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal - π ↔
      (o.oangle u w).toReal + (o.oangle (-w) v).toReal ≤ 0 :=
  Real.Angle.toReal_add_toReal_eq_sub_pi_iff (o.oangle_add_oangle_neg_left hu hw hv)

/-- For nonzero `u`, `w`, `v`, the sum of the real oriented angles from `u` to `w` and from `-w` to
`v` is the real oriented angle from `u` to `v` plus `π` or minus `π`. -/
theorem oangle_toReal_add_oangle_neg_left_toReal_eq_add_pi_or_eq_sub_pi {u w v : V} (hu : u ≠ 0)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal + π ∨
      (o.oangle u w).toReal + (o.oangle (-w) v).toReal = (o.oangle u v).toReal - π :=
  Real.Angle.toReal_add_toReal_eq_add_pi_or_eq_sub_pi (o.oangle_add_oangle_neg_left hu hw hv)

end Orientation
