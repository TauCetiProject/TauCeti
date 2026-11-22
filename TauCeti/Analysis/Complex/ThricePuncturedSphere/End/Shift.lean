/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.End.Coordinate
public import TauCeti.Analysis.Complex.RealChart

/-!
# Translations along the ends of the thrice-punctured sphere

Each end lift of the thrice-punctured sphere `S = ℂ ∖ {0, 1}` is a scaled exponential
`z ↦ c_q + b_q exp (-2πz)` about the center `c_q` of the end
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_eq`). Translating the end coordinate
`z` by `L` towards the puncture, that is by `±L` with the sign `±` of the end, is therefore the
affine map

`χ_{q,L}(w) = c_q + e^{-2π (±L)} (w - c_q)`

(`TauCeti.ThricePuncturedSphere.Puncture.endShift`): a contraction towards `0` or `1` on an input
end, and a dilation about `0` on the output end at `∞`. It sends the point with end coordinate `z`
to the point with end coordinate `z ± L`
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_add_endSign_mul`,
`TauCeti.ThricePuncturedSphere.Puncture.endCoord_endShift`), and it fixes the center of the end.

Perturbation data on spheres with long necks along the ends, such as the data of the capped
comparison family of Floer theory, are translates of fixed data beyond the necks. Reading a map
through `χ_{q,L}` is how the piece of such a sphere beyond the neck at `q` is seen in coordinates
that do not depend on `L`.

## Main definitions

* `TauCeti.ThricePuncturedSphere.Puncture.endShift q L`: the translation by `±L` along the end `q`.

## Main results

* `TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_add_endSign_mul`: the end lift of a
  translated end coordinate.
* `TauCeti.ThricePuncturedSphere.Puncture.endCoord_endShift`: the end coordinate of a translated
  point.
* `TauCeti.ThricePuncturedSphere.Puncture.hasDerivAt_endShift`: the translation is affine with the
  positive real derivative `e^{-2π (±L)}`.
-/

public section

open Real
open TauCeti.Complex (realChart contDiff_realChart)

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The translation by `±L` along the end `q`, where `±` is the sign of the end: the homothety
`w ↦ c_q + e^{-2π (±L)} (w - c_q)` with center the center `c_q` of the end (`AffineMap.homothety`).
It sends the point with end coordinate `z` to the point with end coordinate `z ± L`
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_add_endSign_mul`). -/
noncomputable def endShift (q : Puncture) (L : ℝ) : ℂ → ℂ :=
  AffineMap.homothety q.endCenter (Real.exp (-(2 * π * (q.endSign * L))) : ℂ)

theorem endShift_eq (q : Puncture) (L : ℝ) :
    q.endShift L =
      fun w ↦ q.endCenter + (Real.exp (-(2 * π * (q.endSign * L))) : ℂ) * (w - q.endCenter) :=
  funext fun w ↦ by
    rw [endShift, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul, add_comm]

theorem endShift_apply (q : Puncture) (L : ℝ) (w : ℂ) :
    q.endShift L w =
      q.endCenter + (Real.exp (-(2 * π * (q.endSign * L))) : ℂ) * (w - q.endCenter) := by
  rw [endShift_eq]

/-- The translation fixes the center of the end. -/
@[simp]
theorem endShift_endCenter (q : Puncture) (L : ℝ) : q.endShift L q.endCenter = q.endCenter :=
  AffineMap.homothety_apply_same _ _

/-- Translating by `0` is the identity. -/
@[simp]
theorem endShift_zero (q : Puncture) : q.endShift 0 = id := by
  rw [endShift, mul_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
    AffineMap.homothety_one, AffineMap.coe_id]

/-- The translations along an end compose additively. -/
@[simp]
theorem endShift_endShift (q : Puncture) (L L' : ℝ) (w : ℂ) :
    q.endShift L (q.endShift L' w) = q.endShift (L + L') w := by
  rw [endShift, endShift, endShift, ← AffineMap.homothety_mul_apply, ← Complex.ofReal_mul,
    ← Real.exp_add, show -(2 * π * (q.endSign * L)) + -(2 * π * (q.endSign * L')) =
      -(2 * π * (q.endSign * (L + L'))) by ring]

/-- The translation is affine with the positive real derivative `e^{-2π (±L)}`. -/
theorem hasDerivAt_endShift (q : Puncture) (L : ℝ) (w : ℂ) :
    HasDerivAt (q.endShift L) (Real.exp (-(2 * π * (q.endSign * L))) : ℂ) w := by
  simpa [endShift, AffineMap.homothety_linear] using
    (AffineMap.homothety q.endCenter (Real.exp (-(2 * π * (q.endSign * L))) : ℂ)).hasDerivAt
      (x := w)

theorem endShift_injective (q : Puncture) (L : ℝ) : Function.Injective (q.endShift L) :=
  AffineMap.homothety_injective _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')

/-- The translation is smooth. -/
theorem contDiff_endShift (q : Puncture) (L : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℂ n (q.endShift L) := by
  rw [endShift_eq]
  exact contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))

/-- The translation is smooth in the real coordinates. -/
theorem contDiff_realChart_endShift (q : Puncture) (L : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (realChart (q.endShift L)) :=
  contDiff_realChart (q.contDiff_endShift L)

/-- **The translation in end coordinates.** The point with end coordinate `z ± L` on the end `q`
is the translate of the point with end coordinate `z`. -/
theorem cylindricalEndLift_add_endSign_mul (q : Puncture) (L : ℝ) (z : ℂ) :
    q.cylindricalEndLift (z + ↑(q.endSign * L)) = q.endShift L (q.cylindricalEndLift z) := by
  rw [cylindricalEndLift_eq, cylindricalEndLift_eq, endShift_apply, add_sub_cancel_left,
    Complex.ofReal_exp, mul_add, Complex.exp_add]
  push_cast
  ring_nf

/-- The chain rule for the translation: the derivative of the end lift at `z ± L` is
`e^{-2π (±L)}` times its derivative at `z`. -/
theorem deriv_cylindricalEndLift_add_endSign_mul (q : Puncture) (L : ℝ) (z : ℂ) :
    deriv q.cylindricalEndLift (z + ↑(q.endSign * L)) =
      (Real.exp (-(2 * π * (q.endSign * L))) : ℂ) * deriv q.cylindricalEndLift z := by
  rw [deriv_cylindricalEndLift, deriv_cylindricalEndLift, cylindricalEndLift_add_endSign_mul,
    endShift_apply]
  ring

/-- **The end coordinate of a translated point.** Away from the center of the end, translating a
point by `±L` along the end `q` adds `±L` to its end coordinate. No integer shift of the angular
coordinate occurs, since the translation multiplies the displacement from the center by a positive
real number. -/
theorem endCoord_endShift (q : Puncture) (L : ℝ) {w : ℂ} (hw : w ≠ q.endCenter) :
    q.endCoord (q.endShift L w) = q.endCoord w + ↑(q.endSign * L) := by
  have h : (w - q.endCenter) / q.endScale ≠ 0 :=
    div_ne_zero (sub_ne_zero.2 hw) q.endScale_ne_zero
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hs : (q.endShift L w - q.endCenter) / q.endScale =
      (Real.exp (-(2 * π * (q.endSign * L))) : ℝ) * ((w - q.endCenter) / q.endScale) := by
    rw [endShift_apply, add_sub_cancel_left, mul_div_assoc]
  rw [endCoord_def, endCoord_def, hs, Complex.log_ofReal_mul (Real.exp_pos _) h, Real.log_exp]
  field_simp
  push_cast
  ring

/-- Translating a point by `±L` along the end `q` adds `L` to its signed longitudinal coordinate
`±s`. -/
theorem endSign_mul_re_endCoord_endShift (q : Puncture) (L : ℝ) {w : ℂ} (hw : w ≠ q.endCenter) :
    q.endSign * (q.endCoord (q.endShift L w)).re = q.endSign * (q.endCoord w).re + L := by
  rw [endCoord_endShift q L hw, Complex.add_re, Complex.ofReal_re, mul_add,
    endSign_mul_endSign_mul]

end TauCeti.ThricePuncturedSphere.Puncture
