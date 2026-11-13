/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import TauCeti.Topology.Instances.AddCircle.UnitInterval

/-!
# Trigonometric functions on the unit interval

The cosine `t ↦ cos (π t)` is strictly decreasing on the unit interval `I`, and the sine
`t ↦ sin (π t)` is positive on its interior. The point `(cos 2πt, sin 2πt)` runs once around the
unit circle as `t` runs over `I`: it reaches every point, it is `(1, 0)` only at the end points,
and it is injective away from the end points.

## Main declarations

* `TauCeti.cos_pi_mul_strictAnti`: `t ↦ cos (π t)` is strictly decreasing on `I`.
* `TauCeti.sin_pi_mul_pos`: `sin (π t) > 0` for `t ∈ I` different from `0` and `1`.
* `TauCeti.exists_cos_sin_two_pi_mul_eq`, `TauCeti.eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one` and
  `TauCeti.eq_or_of_cos_sin_two_pi_mul_eq`: `t ↦ (cos 2πt, sin 2πt)` covers the unit circle, meets
  `(1, 0)` only at the end points of `I`, and identifies only the two end points.
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

/-- `t ↦ cos (π t)` is strictly decreasing on the unit interval. -/
theorem cos_pi_mul_strictAnti : StrictAnti (fun t : I => cos (π * t)) := by
  intro a b hab
  refine strictAntiOn_cos ?_ ?_ (mul_lt_mul_of_pos_left (Subtype.coe_lt_coe.2 hab) pi_pos)
  · exact ⟨by positivity [a.2.1], mul_le_of_le_one_right pi_pos.le a.2.2⟩
  · exact ⟨by positivity [b.2.1], mul_le_of_le_one_right pi_pos.le b.2.2⟩

/-- `sin (π t)` is positive on the open unit interval. -/
theorem sin_pi_mul_pos {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) : 0 < sin (π * t) := by
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
  exact sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])

/-- Every point `(a, b)` of the unit circle is `(cos 2πt, sin 2πt)` for some `t` in the unit
interval. -/
theorem exists_cos_sin_two_pi_mul_eq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : I, cos (2 * π * t) = a ∧ sin (2 * π * t) = b := by
  let z : ℂ := ⟨a, b⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
    nlinarith
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  obtain ⟨t, ht⟩ := AddCircle.surjective_ofUnitInterval (p := 2 * π) (z.arg : Real.Angle)
  rw [AddCircle.ofUnitInterval_apply] at ht
  -- `Real.Angle` is by definition `AddCircle (2 * π)`, with the same quotient map from `ℝ`.
  have ht' : ((2 * π * t : ℝ) : Real.Angle) = z.arg := by rw [mul_comm]; exact ht
  refine ⟨t, ?_, ?_⟩
  · rw [← Real.Angle.cos_coe, ht', Real.Angle.cos_coe, Complex.cos_arg hz0, hz, div_one]
  · rw [← Real.Angle.sin_coe, ht', Real.Angle.sin_coe, Complex.sin_arg, hz, div_one]

/-- On the unit interval, `cos 2πt = 1` only at the end points. -/
theorem eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one {t : I} (h : cos (2 * π * t) = 1) :
    t = 0 ∨ t = 1 := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  rw [← Real.cos_zero, Real.Angle.cos_eq_iff_coe_eq_or_eq_neg, Real.Angle.coe_zero, neg_zero,
    or_self] at h
  have h' : AddCircle.ofUnitInterval (2 * π) t = AddCircle.ofUnitInterval (2 * π) 0 := by
    rw [AddCircle.ofUnitInterval_zero, AddCircle.ofUnitInterval_apply, mul_comm (t : ℝ)]
    -- `Real.Angle` is by definition `AddCircle (2 * π)`, with the same quotient map from `ℝ`.
    exact h
  obtain h | ⟨h, -⟩ | ⟨h, -⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 h'
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

/-- On the unit interval, `cos 2πt` and `sin 2πt` determine `t`, except that they agree at the two
end points. -/
theorem eq_or_of_cos_sin_two_pi_mul_eq {s t : I} (hc : cos (2 * π * s) = cos (2 * π * t))
    (hs : sin (2 * π * s) = sin (2 * π * t)) : s = t ∨ s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  refine (AddCircle.ofUnitInterval_eq_ofUnitInterval_iff (p := 2 * π)).1 ?_
  rw [AddCircle.ofUnitInterval_apply, AddCircle.ofUnitInterval_apply, mul_comm (s : ℝ),
    mul_comm (t : ℝ)]
  -- `Real.Angle` is by definition `AddCircle (2 * π)`, with the same quotient map from `ℝ`.
  exact Real.Angle.cos_sin_inj hc hs

end TauCeti
