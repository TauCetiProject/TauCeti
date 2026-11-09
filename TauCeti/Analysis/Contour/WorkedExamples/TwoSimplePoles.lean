/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.Circle.PrincipalPart
public import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# A circle integral with two simple poles

This file works out the residue theorem for a circle and two simple poles.  For two
distinct points `s₁` and `s₂`, the function

`z ↦ A / (z - s₁) + B / (z - s₂)`

has residues `A` and `B` at the respective poles.  When both poles lie inside a circle, its
contour integral is therefore `2πi (A + B)`.  The calculation is stated directly for arbitrary
centres, radii, pole positions, and coefficients, so it also covers a vanishing coefficient
without pretending that the corresponding point remains a pole.

The integral calculation integrates each principal part with the single-principal-part API in
`TauCeti.Analysis.Contour.Curve.Circle.PrincipalPart`; the residue calculations use the simple-pole
API in `TauCeti.Analysis.Contour.Residue.SimplePole`.
-/

public section

noncomputable section

open Metric

namespace TauCeti.Contour

/-- The rational function with prescribed principal parts `A / (z - s₁)` and
`B / (z - s₂)`. -/
def twoPrincipalParts (A B s₁ s₂ : ℂ) (z : ℂ) : ℂ :=
  A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹

/-- The value of `twoPrincipalParts` at a point. -/
@[simp]
theorem twoPrincipalParts_apply (A B s₁ s₂ z : ℂ) :
    twoPrincipalParts A B s₁ s₂ z = A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹ :=
  twoPrincipalParts.eq_1 A B s₁ s₂ z

/-- The function-level defining equation for `twoPrincipalParts`. -/
theorem twoPrincipalParts_eq (A B s₁ s₂ : ℂ) :
    twoPrincipalParts A B s₁ s₂ = fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹ :=
  funext fun z => twoPrincipalParts_apply A B s₁ s₂ z

/-- When both principal parts are designated at the same point, they combine into one. -/
theorem twoPrincipalParts_self (A B s : ℂ) :
    twoPrincipalParts A B s s = fun z => (A + B) * (z - s)⁻¹ :=
  funext fun z => by rw [twoPrincipalParts_apply, add_mul]

/-- The function `twoPrincipalParts` is meromorphic everywhere. -/
theorem meromorphicAt_twoPrincipalParts (A B s₁ s₂ z : ℂ) :
    MeromorphicAt (twoPrincipalParts A B s₁ s₂) z := by
  rw [twoPrincipalParts_eq]
  fun_prop

/-- At the first designated point, the residue of `twoPrincipalParts` is the first coefficient if
the other principal part vanishes or is designated at a distinct point. -/
@[simp]
theorem residue_twoPrincipalParts_left {A B s₁ s₂ : ℂ} (h : B = 0 ∨ s₁ ≠ s₂) :
    residue (twoPrincipalParts A B s₁ s₂) s₁ = A := by
  rw [twoPrincipalParts_eq, ← Pi.add_def, residue_add (by fun_prop) (by fun_prop),
    residue_const_mul_sub_inv, residue_eq_zero_of_analyticAt (analyticAt_const_mul_sub_inv h),
    add_zero]

/-- At the second designated point, the residue of `twoPrincipalParts` is the second coefficient if
the other principal part vanishes or is designated at a distinct point. -/
@[simp]
theorem residue_twoPrincipalParts_right {A B s₁ s₂ : ℂ} (h : A = 0 ∨ s₁ ≠ s₂) :
    residue (twoPrincipalParts A B s₁ s₂) s₂ = B := by
  rw [twoPrincipalParts_eq, ← Pi.add_def, residue_add (by fun_prop) (by fun_prop),
    residue_const_mul_sub_inv,
    residue_eq_zero_of_analyticAt (analyticAt_const_mul_sub_inv (h.imp_right Ne.symm)), zero_add]

/-- `twoPrincipalParts` is analytic at `z` if and only if each nonzero principal part is designated
away from `z`, or the two principal parts are designated at the same point and cancel. -/
theorem analyticAt_twoPrincipalParts_iff {A B s₁ s₂ z : ℂ} :
    AnalyticAt ℂ (twoPrincipalParts A B s₁ s₂) z ↔
      ((A = 0 ∨ z ≠ s₁) ∧ (B = 0 ∨ z ≠ s₂)) ∨ (s₁ = s₂ ∧ A + B = 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases eq_or_ne s₁ s₂ with rfl | hs
    · refine or_iff_not_imp_right.2 fun hAB => ?_
      have hz : z ≠ s₁ := by
        rintro rfl
        rw [twoPrincipalParts_self] at h
        exact hAB ⟨rfl, by simpa [residue_const_mul_sub_inv] using residue_eq_zero_of_analyticAt h⟩
      exact ⟨Or.inr hz, Or.inr hz⟩
    · refine Or.inl ⟨or_iff_not_imp_right.2 fun hz => ?_, or_iff_not_imp_right.2 fun hz => ?_⟩ <;>
        rw [not_not] at hz <;> subst hz
      · simpa [hs] using residue_eq_zero_of_analyticAt h
      · simpa [hs] using residue_eq_zero_of_analyticAt h
  rintro (⟨h₁, h₂⟩ | ⟨rfl, hAB⟩)
  · rw [twoPrincipalParts_eq]
    exact (analyticAt_const_mul_sub_inv h₁).add (analyticAt_const_mul_sub_inv h₂)
  · simpa [twoPrincipalParts_self, hAB] using analyticAt_const

/-- **Two-pole circle integral.** If the designated point of each nonzero principal part lies
strictly inside the circle `C(c, R)`, then the integral of `A / (z - s₁) + B / (z - s₂)` around
that circle is `2πi (A + B)`.  Together with `residue_twoPrincipalParts_left` and
`residue_twoPrincipalParts_right`, this is the classical residue theorem for two simple poles. -/
theorem circleIntegral_twoPrincipalParts {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs₁ : A = 0 ∨ s₁ ∈ ball c R) (hs₂ : B = 0 ∨ s₂ ∈ ball c R) :
    circleIntegral (twoPrincipalParts A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I * (A + B) := by
  have hsphere {s : ℂ} (hs : s ∈ ball c R) : R = 0 ∨ s ∉ sphere c |R| := by
    rw [abs_of_pos (pos_of_mem_ball hs)]
    exact Or.inr (sphere_disjoint_ball.notMem_of_mem_right hs)
  rw [twoPrincipalParts_eq, circleIntegral.integral_add
    (circleIntegrable_const_mul_sub_inv (hs₁.imp_right hsphere))
    (circleIntegrable_const_mul_sub_inv (hs₂.imp_right hsphere)),
    circleIntegral_const_mul_sub_inv hs₁, circleIntegral_const_mul_sub_inv hs₂, mul_add]

/-- The two-pole calculation in residue-theorem form: for distinct designated points, with the
point of each nonzero principal part inside the circle, the integral is `2πi` times the sum of the
two residues. -/
theorem circleIntegral_twoPrincipalParts_eq_residue_sum {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs : s₁ ≠ s₂) (hs₁ : A = 0 ∨ s₁ ∈ ball c R) (hs₂ : B = 0 ∨ s₂ ∈ ball c R) :
    circleIntegral (twoPrincipalParts A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I *
        (residue (twoPrincipalParts A B s₁ s₂) s₁ +
          residue (twoPrincipalParts A B s₁ s₂) s₂) := by
  rw [circleIntegral_twoPrincipalParts hs₁ hs₂, residue_twoPrincipalParts_left (Or.inr hs),
    residue_twoPrincipalParts_right (Or.inr hs)]

end TauCeti.Contour

end
