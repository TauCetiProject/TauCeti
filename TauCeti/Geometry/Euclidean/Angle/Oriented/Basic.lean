/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Analysis.InnerProductSpace.TwoDim

/-!
# Real representatives of oriented angles, and oriented angles in complex coordinates

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

On `ℂ` with its standard orientation, the oriented angle from `w` to `z` is the argument of the
quotient `z / w` (`Complex.oangle_eq_arg_div`), and `arg (z / w)` is its real representative in
`(-π, π]` (`Complex.oangle_toReal_eq_arg_div`); Mathlib's `Complex.angle_eq_abs_arg` is the
unoriented counterpart. So for nonzero `w` and `z` the real oriented angle is the difference
`arg z - arg w` exactly when this difference lies in `(-π, π]` (`Complex.arg_div_eq_sub_arg_iff`),
for instance when `w` and `z` both lie in the open upper, lower or right half-plane
(`Complex.arg_div_of_im_pos`, `Complex.arg_div_of_im_neg`, `Complex.arg_div_of_re_pos`).

A positively oriented orthonormal basis `b` of an oriented plane identifies it with `ℂ` by
`Complex.isometryOfOrthonormal b`, and this identification preserves oriented angles
(`Orientation.oangle_isometryOfOrthonormal`). Hence the signed exterior angle at a corner of a
curve in an oriented plane, the real oriented angle from the incoming tangent to the outgoing one,
is `arg (z⁺ / z⁻)`, where `z⁻` and `z⁺` are the complex coordinates of the two tangents in any such
basis.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 9.
-/

public section

open Real

attribute [local instance] Complex.finrank_real_complex_fact

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

/-- The identification of an oriented plane with `ℂ` given by a positively oriented orthonormal
basis `b` preserves oriented angles: the oriented angle from `x₀ b₀ + y₀ b₁` to `x₁ b₀ + y₁ b₁` is
the oriented angle from `x₀ + y₀ i` to `x₁ + y₁ i` in `ℂ`. -/
theorem oangle_isometryOfOrthonormal {b : OrthonormalBasis (Fin 2) ℝ V}
    (hb : b.toBasis.orientation = o) (z w : ℂ) :
    o.oangle (Complex.isometryOfOrthonormal b z) (Complex.isometryOfOrthonormal b w) =
      Complex.orientation.oangle z w := by
  subst hb
  rw [oangle_map_complex _ _ (Complex.map_isometryOfOrthonormal_symm_orientation b),
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply, Complex.oangle]

end Orientation

namespace Complex

/-- The oriented angle from `w` to `z` in `ℂ` is the argument of `z / w`. -/
theorem oangle_eq_arg_div (w z : ℂ) : Complex.orientation.oangle w z = arg (z / w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [Complex.oangle, ← arg_real_mul (z / w) (normSq_pos.2 hw), normSq_eq_conj_mul_self,
      mul_assoc, mul_div_cancel₀ z hw]

/-- The real representative in `(-π, π]` of the oriented angle from `w` to `z` in `ℂ` is the
argument of `z / w`. -/
theorem oangle_toReal_eq_arg_div (w z : ℂ) :
    (Complex.orientation.oangle w z).toReal = arg (z / w) := by
  rw [oangle_eq_arg_div, arg_coe_angle_toReal_eq_arg]

end Complex
