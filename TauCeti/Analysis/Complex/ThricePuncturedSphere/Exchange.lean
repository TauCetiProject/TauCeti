/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate

/-!
# The exchange of the finite punctures in end coordinates

The holomorphic involution `σ(w) = 1 - w` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`
(`TauCeti.ThricePuncturedSphere.mob01`) exchanges the two finite punctures and fixes `∞`. This file
records how it acts on the cylindrical end coordinates of `S`.

On the two input ends `σ` is exact: it carries the end lift of `0` to the end lift of `1` and back
(`Puncture.one_sub_cylindricalEndLift_zero`, `Puncture.one_sub_cylindricalEndLift_one`), so it
exchanges the end coordinates of `0` and `1` (`Puncture.endCoord_zero_one_sub`,
`Puncture.endCoord_one_one_sub`). Since `dσ = -1`, it exchanges the angular forms up to sign
(`Puncture.endAngularForm_zero_one_sub`, `Puncture.endAngularForm_one_one_sub`).

At `∞` the end lift `φ_∞(z) = 2 exp (-2πz)` is centred at `0`, not at the fixed point `1/2` of
`σ`. The part of `σ` that acts on this end is the half turn `w ↦ -w`, which is a half-period
rotation of the cylinder: `φ_∞(z + i/2) = -φ_∞(z)`
(`Puncture.cylindricalEndLift_inf_add_I_div_two`). It preserves the longitudinal coordinate
(`Puncture.re_endCoord_inf_neg`), shifts the angular coordinate by `1/2` modulo `1`
(`Puncture.exists_endCoord_inf_neg`), and reverses the angular form
(`Puncture.endAngularForm_inf_neg`). The remaining translation by `1` moves the centre of the
output end; it is absorbed by the input-exchange family of Floer perturbation data.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
-/

public section

open Real

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The exchange `w ↦ 1 - w` carries the end lift of `0` to the end lift of `1`. -/
theorem one_sub_cylindricalEndLift_zero (z : ℂ) :
    1 - zero.cylindricalEndLift z = one.cylindricalEndLift z := by
  simp

/-- The exchange `w ↦ 1 - w` carries the end lift of `1` to the end lift of `0`. -/
theorem one_sub_cylindricalEndLift_one (z : ℂ) :
    1 - one.cylindricalEndLift z = zero.cylindricalEndLift z := by
  simp

/-- The half-period rotation of the end at `∞` is the half turn `w ↦ -w` of the plane. -/
theorem cylindricalEndLift_inf_add_I_div_two (z : ℂ) :
    inf.cylindricalEndLift (z + Complex.I / 2) = -inf.cylindricalEndLift z := by
  have h : -(2 * (π : ℂ)) * (z + Complex.I / 2) = -(2 * π) * z + -(π * Complex.I) := by ring
  simp only [cylindricalEndLift_inf, h, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- In end coordinates the exchange `w ↦ 1 - w` turns the end at `1` into the end at `0`. -/
theorem endCoord_zero_one_sub (w : ℂ) : zero.endCoord (1 - w) = one.endCoord w := by
  simp only [endCoord_def, endCenter_zero, endCenter_one, endScale_zero, endScale_one]
  congr 3
  ring

/-- In end coordinates the exchange `w ↦ 1 - w` turns the end at `0` into the end at `1`. -/
theorem endCoord_one_one_sub (w : ℂ) : one.endCoord (1 - w) = zero.endCoord w := by
  simpa using (endCoord_zero_one_sub (1 - w)).symm

/-- The exchange `w ↦ 1 - w` reverses the angular forms of the two finite ends, since its
derivative is `-1`: `σ^* dt_0 = dt_1`. -/
theorem endAngularForm_zero_one_sub (w : ℂ) :
    zero.endAngularForm (1 - w) = -one.endAngularForm w := by
  ext v
  have h : -(2 * (π : ℂ) * (1 - w - zero.endCenter)) = -(-(2 * π * (w - one.endCenter))) := by
    simp only [endCenter_zero, endCenter_one]
    ring
  rw [endAngularForm_apply, h, neg_apply, endAngularForm_apply]
  simp

/-- The exchange `w ↦ 1 - w` reverses the angular forms of the two finite ends, since its
derivative is `-1`: `σ^* dt_1 = dt_0`. -/
theorem endAngularForm_one_one_sub (w : ℂ) :
    one.endAngularForm (1 - w) = -zero.endAngularForm w := by
  rw [← neg_neg (one.endAngularForm (1 - w)), ← endAngularForm_zero_one_sub, sub_sub_cancel]

/-- The half turn `w ↦ -w` reverses the angular form of the end at `∞`. -/
theorem endAngularForm_inf_neg (w : ℂ) : inf.endAngularForm (-w) = -inf.endAngularForm w := by
  ext v
  simp [endAngularForm_apply]

/-- The half turn `w ↦ -w` preserves the longitudinal coordinate of the end at `∞`. -/
@[simp]
theorem re_endCoord_inf_neg (w : ℂ) : (inf.endCoord (-w)).re = (inf.endCoord w).re := by
  simp [re_endCoord, neg_div]

/-- The half turn `w ↦ -w` rotates the end at `∞` by half a period: away from its centre it adds
`1/2` to the angular coordinate, modulo `1`. -/
theorem exists_endCoord_inf_neg {w : ℂ} (hw : w ≠ 0) :
    ∃ k : ℤ, inf.endCoord (-w) = inf.endCoord w + (1 / 2 + k) * Complex.I := by
  have hw' : w ≠ inf.endCenter := by simpa using hw
  obtain ⟨k, hk⟩ := inf.exists_endCoord_cylindricalEndLift (inf.endCoord w + Complex.I / 2)
  refine ⟨k, ?_⟩
  rw [cylindricalEndLift_inf_add_I_div_two, inf.cylindricalEndLift_endCoord hw'] at hk
  rw [hk]
  ring

end TauCeti.ThricePuncturedSphere.Puncture
