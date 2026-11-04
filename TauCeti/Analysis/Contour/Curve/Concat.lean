/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Contour integrals along reversed and concatenated curves

The contour-integration layer works with raw curves `γ : ℝ → ℂ` on a parameter interval
`[[a, b]]` and with the raw contour integral `∫ t in a..b, deriv γ t • f (γ t)`. This file computes
that integral along the two operations on curves that a path-independence argument needs: running a
curve backwards, and following one curve by another. That these operations preserve piecewise `C¹`
regularity is `TauCeti.IsPiecewiseC1On.comp_const_sub` and `TauCeti.IsPiecewiseC1On.if_le`.

* The contour integral of the **reversal** `t ↦ γ (c - t)` over `a..b` is the contour integral of
  `γ` over `c - a..c - b`. Taking `c` to be the sum of the endpoints of a second interval lets the
  reversed curve start where another curve ends.
* The contour integral only sees a curve on the open interior of its parameter interval, so along
  the **concatenation** `t ↦ if t ≤ b then γ t else δ t` of a curve `γ` on `[a, b]` and a curve
  `δ` on `[b, c]` it splits as the sum of the contour integrals of `γ` and `δ`.

## Main results

* `TauCeti.Contour.intervalIntegral_deriv_smul_comp_const_sub` — the contour integral of the
  reversed curve.
* `TauCeti.Contour.intervalIntegral_deriv_smul_congr` — the contour integral depends on the curve
  only through its values on the open parameter interval.
* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_add_of_eqOn` — the contour integral along a
  concatenation is the sum of the contour integrals along its pieces.
-/

public section

namespace TauCeti.Contour

open Set MeasureTheory

section Integral

variable {γ δ : ℝ → ℂ} {a b c : ℝ}

/-- **The contour integral along a reversed curve.** The contour integral of `t ↦ γ (c - t)` over
`a..b` is the contour integral of `γ` over `c - a..c - b`. In particular, for `c = a + b` the
transformed endpoints are `b` and `a`, in reverse order, so it is
`∫ t in b..a, deriv γ t • f (γ t)`, the negative of the contour integral of `γ` over `a..b`. -/
theorem intervalIntegral_deriv_smul_comp_const_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (γ : ℝ → ℂ) (f : ℂ → E) (a b c : ℝ) :
    ∫ t in a..b, deriv (fun t => γ (c - t)) t • f (γ (c - t)) =
      ∫ t in c - a..c - b, deriv γ t • f (γ t) := by
  simp only [deriv_comp_const_sub, neg_smul, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => deriv γ t • f (γ t)) c,
    intervalIntegral.integral_symm (c - b) (c - a)]

/-- **The contour integral sees only the open parameter interval.** If two curves agree on the
open interval between `a` and `b`, their contour integrals over `a..b` agree, even though the
integrand involves the derivative of the curve. -/
theorem intervalIntegral_deriv_smul_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (h : EqOn γ δ (uIoo a b)) :
    ∫ t in a..b, deriv γ t • f (γ t) = ∫ t in a..b, deriv δ t • f (δ t) :=
  intervalIntegral.integral_congr_uIoo ((h.deriv isOpen_Ioo).comp_left₂ h.comp_left)

/-- **The contour integral along a concatenation.** If `η` agrees with `γ` on the open interval
between `a` and `b` and with `δ` on the open interval between `b` and `c`, and the contour
integrands of `γ` and `δ` are integrable there, then the contour integral of `η` over `a..c` is the
sum of those of `γ` over `a..b` and of `δ` over `b..c`. This applies in particular to the
concatenation `t ↦ if t ≤ b then γ t else δ t` when `a ≤ b ≤ c`. -/
theorem intervalIntegral_deriv_smul_eq_add_of_eqOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {η : ℝ → ℂ} (hγ : EqOn η γ (uIoo a b))
    (hδ : EqOn η δ (uIoo b c))
    (hγi : IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume a b)
    (hδi : IntervalIntegrable (fun t => deriv δ t • f (δ t)) volume b c) :
    ∫ t in a..c, deriv η t • f (η t) =
      (∫ t in a..b, deriv γ t • f (γ t)) + ∫ t in b..c, deriv δ t • f (δ t) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (f := fun t => deriv η t • f (η t))
      (hγi.congr_uIoo ((hγ.deriv isOpen_Ioo).comp_left₂ hγ.comp_left).symm)
      (hδi.congr_uIoo ((hδ.deriv isOpen_Ioo).comp_left₂ hδ.comp_left).symm),
    intervalIntegral_deriv_smul_congr hγ, intervalIntegral_deriv_smul_congr hδ]

end Integral

end TauCeti.Contour
