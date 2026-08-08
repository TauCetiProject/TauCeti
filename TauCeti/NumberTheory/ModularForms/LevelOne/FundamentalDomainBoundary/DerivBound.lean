/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# A uniform derivative bound for the boundary contour

The derivative of the boundary contour is bounded off the three corner parameters: each
piece has a constant derivative or a scaled unit tangent, so one constant bounds them all,
uniformly in the parameter.

This is the growth input of the on-curve principal values at a fixed excision radius: on
the complement of an `ε`-ball around a point of the contour, the winding integrand
`(γ t - s)⁻¹ • deriv γ t` is bounded by `ε⁻¹` times this bound, so each excised integrand
is bounded and hence integrable. The bound degrades as `ε` shrinks, so it is not a
dominator for the excision limit itself: that limit rests on the symmetric cancellation at
the crossing, not on this estimate.

## Main declarations

* `TauCeti.ModularForm.exists_norm_deriv_fdBoundary_le`: a bound on `‖deriv (fdBoundary H)‖`
  valid off the corner parameters.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/OnCurvePV/Basic.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

/-- **A uniform bound on the contour's derivative off the corners.** At every parameter
other than the three corner parameters, `‖deriv (fdBoundary H) t‖` is bounded by
`‖ρ + 1 - (1/2 + H·i)‖ + π/6 + ‖-1/2 + H·i - ρ‖ + 1`: off the corners the derivative is one
of the four piecewise values — the two vertical chords, the arc's `π/6`-scaled unit tangent,
and the ceiling's `1` — and each is bounded by one summand.

The corners are excluded rather than handled: the contour is not differentiable there, and
a three-point set is null, so the consumers — which bound excised integrands at a fixed
excision radius — need nothing at those parameters. The bound is an existential over a positive
constant, the form those consumers use. -/
theorem exists_norm_deriv_fdBoundary_le (H : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∉ fdBoundaryCorners, ‖deriv (fdBoundary H) t‖ ≤ M := by
  refine ⟨‖(ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)‖ + Real.pi / 6 +
    ‖-1 / 2 + H * Complex.I - (ρ : ℂ)‖ + 1, by positivity, fun t ht ↦ ?_⟩
  rw [mem_fdBoundaryCorners] at ht
  push Not at ht
  obtain ⟨h1, h3, h4⟩ := ht
  have hpi : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have hn1 : (0 : ℝ) ≤ ‖(ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)‖ := norm_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖-1 / 2 + H * Complex.I - (ρ : ℂ)‖ := norm_nonneg _
  rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
  · rw [deriv_fdBoundary_of_lt_one hlt1]
    nlinarith [hn1, hn2, hpi]
  rcases lt_or_gt_of_ne h3 with hlt3 | hgt3
  · rw [deriv_fdBoundary_of_mem_Ioo_one_three ⟨hgt1, hlt3⟩, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hpi, norm_mul, norm_circleMap_zero, abs_one, one_mul, norm_I, mul_one]
    linarith
  rcases lt_or_gt_of_ne h4 with hlt4 | hgt4
  · rw [deriv_fdBoundary_of_mem_Ioo_three_four ⟨hgt3, hlt4⟩]
    nlinarith [hn1, hn2, hpi]
  · rw [deriv_fdBoundary_of_gt_four hgt4, norm_one]
    linarith

end ModularForm

end TauCeti

end
