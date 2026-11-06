/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate

/-!
# The end coordinates under the exchange of the input punctures

The reflection `w ↦ 1 - w` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}` exchanges the two
finite punctures `0` and `1` and fixes `∞` (`TauCeti.ThricePuncturedSphere.mob01`); it is the only
Möbius transformation doing so. It is the domain symmetry behind the graded commutativity of the
pair-of-pants product. This file records how it acts on the cylindrical end coordinates of
`TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate`.

On the two finite ends it is an exact exchange of the end coordinates, markers included: the end
lifts at `0` and `1` are `z ↦ exp (-2πz) / 2` and `z ↦ 1 - exp (-2πz) / 2`, so
`1 - φ_q(z) = φ_{q'}(z)` for the other finite puncture `q'`
(`Puncture.one_sub_cylindricalEndLift`). Hence the end coordinate of `q'` at `1 - w` is the end
coordinate of `q` at `w` (`Puncture.endCoord_swap_one_sub`), and the angular form changes sign,
because the derivative of `w ↦ 1 - w` is `-1` (`Puncture.endAngularForm_swap_one_sub`).

At `∞` the reflection is not a symmetry of the end coordinate centred at `0`, but the point
reflection `w ↦ -w` is: it rotates the end at `∞` by half a turn. Its end lift
`z ↦ 2 exp (-2πz)` satisfies `-φ_∞(z) = φ_∞(z + i/2)` (`Puncture.neg_cylindricalEndLift_inf`), so
`w ↦ -w` preserves the longitudinal coordinate and shifts the angular coordinate by `1/2` modulo
`1` (`Puncture.re_endCoord_inf_neg`, `Puncture.exists_im_endCoord_inf_neg_eq`). The reflection
`w ↦ 1 - w` is the point reflection about `1/2`, so it rotates by half a turn the end at `∞` whose
coordinate is centred at `1/2`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the commutativity of the pair-of-pants product.
-/

public noncomputable section

open Real

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The exchange of the two finite punctures fixes `∞`. -/
@[simp]
theorem swap_zero_one_inf : Equiv.swap zero one inf = inf :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

/-- The exchange of the two finite punctures preserves the sign of every end. -/
@[simp]
theorem endSign_swap_zero_one (q : Puncture) : (Equiv.swap zero one q).endSign = q.endSign := by
  cases q <;> simp

/-- The exchange of the two finite punctures reflects their centers about `1/2`. -/
theorem endCenter_swap_zero_one {q : Puncture} (hq : q ≠ inf) :
    (Equiv.swap zero one q).endCenter = 1 - q.endCenter := by
  cases q <;> simp_all

/-- The exchange of the two finite punctures negates their scales. -/
theorem endScale_swap_zero_one {q : Puncture} (hq : q ≠ inf) :
    (Equiv.swap zero one q).endScale = -q.endScale := by
  cases q <;> simp_all

/-- **The exchange of the input end lifts.** The reflection `w ↦ 1 - w` carries the end lift of
each finite puncture to the end lift of the other one, including the marker `t = 0`. -/
theorem one_sub_cylindricalEndLift {q : Puncture} (hq : q ≠ inf) (z : ℂ) :
    1 - q.cylindricalEndLift z = (Equiv.swap zero one q).cylindricalEndLift z := by
  rw [cylindricalEndLift_eq, cylindricalEndLift_eq, endCenter_swap_zero_one hq,
    endScale_swap_zero_one hq]
  ring

/-- **The exchange of the input end coordinates.** The end coordinate of the other finite puncture
at `1 - w` is the end coordinate of `q` at `w`. -/
theorem endCoord_swap_one_sub {q : Puncture} (hq : q ≠ inf) (w : ℂ) :
    (Equiv.swap zero one q).endCoord (1 - w) = q.endCoord w := by
  rw [endCoord_def, endCoord_def, endCenter_swap_zero_one hq, endScale_swap_zero_one hq,
    show 1 - w - (1 - q.endCenter) = -(w - q.endCenter) by ring, neg_div_neg_eq]

/-- The angular form of the other finite puncture at `1 - w` is minus the angular form of `q` at
`w`: the reflection `w ↦ 1 - w` has derivative `-1`. -/
theorem endAngularForm_swap_one_sub {q : Puncture} (hq : q ≠ inf) (w : ℂ) :
    (Equiv.swap zero one q).endAngularForm (1 - w) = -q.endAngularForm w := by
  ext v
  rw [endAngularForm_apply, neg_apply, endAngularForm_apply,
    endCenter_swap_zero_one hq, show 1 - w - (1 - q.endCenter) = -(w - q.endCenter) by ring,
    ← Complex.neg_im, mul_neg, neg_neg, ← neg_mul, ← inv_neg, neg_neg]

/-- **The half-turn of the output end.** The point reflection `w ↦ -w` rotates the end at `∞` by
half a turn: it carries the end lift at `z` to the end lift at `z + i/2`. -/
theorem neg_cylindricalEndLift_inf (z : ℂ) :
    -inf.cylindricalEndLift z = inf.cylindricalEndLift (z + Complex.I / 2) := by
  have h : Complex.exp (-(2 * (π : ℂ)) * (Complex.I / 2)) = -1 := by
    rw [show -(2 * (π : ℂ)) * (Complex.I / 2) = -(π * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  simp only [cylindricalEndLift_inf]
  rw [mul_add, Complex.exp_add, h]
  ring

/-- The point reflection `w ↦ -w` preserves the longitudinal coordinate of the end at `∞`. -/
@[simp]
theorem re_endCoord_inf_neg (w : ℂ) : (inf.endCoord (-w)).re = (inf.endCoord w).re := by
  simp [re_endCoord, neg_div]

/-- The point reflection `w ↦ -w` shifts the angular coordinate of the end at `∞` by `1/2`,
modulo `1`. -/
theorem exists_im_endCoord_inf_neg_eq {w : ℂ} (hw : w ≠ 0) :
    ∃ k : ℤ, (inf.endCoord (-w)).im = (inf.endCoord w).im + 1 / 2 + k := by
  have hw' : w / 2 ≠ 0 := div_ne_zero hw two_ne_zero
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Complex.arg_neg_coe_angle hw')
  refine ⟨-k - 1, ?_⟩
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [im_endCoord, endCenter_inf, endScale_inf, sub_zero, neg_div] at hk ⊢
  push_cast
  field_simp
  linarith

/-- The angular form of the end at `∞` changes sign under the point reflection `w ↦ -w`. -/
@[simp]
theorem endAngularForm_inf_neg (w : ℂ) : inf.endAngularForm (-w) = -inf.endAngularForm w := by
  ext v
  simp only [endAngularForm_apply, endCenter_inf, sub_zero, neg_apply,
    mul_neg, neg_neg, inv_neg, neg_mul, Complex.neg_im]

end TauCeti.ThricePuncturedSphere.Puncture
