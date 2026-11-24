/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Rectangle.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Argument.Variation

/-!
# The argument principle on a rectangle as a variation of the argument

A function `f` continuous and nowhere zero on the frontier of the rectangle `Rectangle z w` has a
continuous argument `θ` on `[0, 4]` along the boundary curve `Complex.rectBoundary z w`
(`TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp_rectBoundary`); this needs no ordering of
the corners `z` and `w`.

Now let `z` be the lower-left corner (`z.re ≤ w.re` and `z.im ≤ w.im`), so that
`rectBoundary z w` runs counterclockwise, and let `f` be meromorphic on a set containing the
closed rectangle, with its chosen representative analytic and nonzero at every point of the
frontier. Then for every such continuous argument `θ`, its total change around the boundary is
`2π` times the signed divisor count of `f` in the rectangle
(`TauCeti.Contour.sub_eq_two_pi_mul_divisorCount_of_rectBoundary`), and `2π` times the zero
count when `f` has no poles there (`TauCeti.Contour.sub_eq_two_pi_mul_zeroCount_of_rectBoundary`).

This is the form of the argument principle used to count the zeros of the Riemann zeta function
and of other `L`-functions up to a given height: the count is read off from the change of the
argument of the function along the boundary of a rectangle, and that change is then estimated
edge by edge.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §9.3.
* H. Davenport, *Multiplicative Number Theory*, Chapter 15.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ} {θ : ℝ → ℝ}

/-- A function continuous and nowhere zero on the frontier of a rectangle has a continuous
argument along the boundary curve on `[0, 4]`. -/
theorem exists_continuousOn_eq_norm_mul_exp_rectBoundary
    (hf : ContinuousOn f (frontier (Rectangle z w)))
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 4) ∧ ∀ t ∈ Icc (0 : ℝ) 4,
      f (rectBoundary z w t) = ‖f (rectBoundary z w t)‖ * exp (I * θ t) := by
  have hc : ContinuousOn (rectBoundary z w) (Icc 0 4) := by
    simpa [uIcc_of_le] using (isPiecewiseC1On_rectBoundary z w).continuousOn
  exact exists_continuousOn_eq_norm_mul_exp
    (hf.comp hc fun t _ ↦ rectBoundary_mem_frontier t) fun t _ ↦ hne _ (rectBoundary_mem_frontier t)

/-- **The argument principle on a rectangle, as a variation of the argument.** Let `z` be the
lower-left corner of the rectangle `Rectangle z w` (`z.re ≤ w.re`, `z.im ≤ w.im`), so that the
boundary curve `rectBoundary z w` runs counterclockwise. For `f` meromorphic on a set `U`
containing the closed rectangle, analytic and nonzero on its frontier, any
continuous argument `θ` of `f` along the boundary curve on `[0, 4]` changes by `2π` times the signed
divisor count of `f` in the rectangle. -/
theorem sub_eq_two_pi_mul_divisorCount_of_rectBoundary (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0)
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 4,
      f (rectBoundary z w t) = ‖f (rectBoundary z w t)‖ * exp (I * θ t)) :
    θ 4 - θ 0 = 2 * π * divisorCount f U (Rectangle z w) := by
  have hu : uIcc (0 : ℝ) 4 = Icc 0 4 := uIcc_of_le (by norm_num)
  have hint := integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub
    (isPiecewiseC1On_rectBoundary z w) (fun t _ ↦ hreg _ (rectBoundary_mem_frontier t))
    (fun t _ ↦ hne _ (rectBoundary_mem_frontier t)) (hu ▸ hθ) (hu ▸ hlift)
  rw [argumentPrinciple_rectBoundary_divisor hre him hRU hf
    fun x hx ↦ (hreg x hx).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hne x hx),
    rectBoundary_four, rectBoundary_zero, sub_self, ofReal_zero, zero_add] at hint
  -- `hint` now reads `2πi · divisorCount = i (θ 4 - θ 0)`; cancel the factor `i`.
  have h : I * ((θ 4 - θ 0 : ℝ) : ℂ) =
      I * ((2 * π * divisorCount f U (Rectangle z w) : ℝ) : ℂ) := by
    rw [← hint]
    push_cast
    ring
  exact_mod_cast mul_left_cancel₀ I_ne_zero h

/-- **The argument principle on a rectangle without poles, as a variation of the argument.** Let `z`
be the lower-left corner of the rectangle `Rectangle z w` (`z.re ≤ w.re`, `z.im ≤ w.im`), so that
the boundary curve `rectBoundary z w` runs counterclockwise. For `f` meromorphic on a set `U`
containing the closed rectangle, without poles in the rectangle, and analytic and
nonzero on its frontier, any continuous argument `θ` of `f` along the boundary curve on
`[0, 4]` changes by `2π` times the number of zeros of `f` in the rectangle, counted with
multiplicity. -/
theorem sub_eq_two_pi_mul_zeroCount_of_rectBoundary (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hne : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0)
    (hnonneg : ∀ x ∈ Rectangle z w, 0 ≤ MeromorphicOn.divisor f U x)
    (hθ : ContinuousOn θ (Icc 0 4))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 4,
      f (rectBoundary z w t) = ‖f (rectBoundary z w t)‖ * exp (I * θ t)) :
    θ 4 - θ 0 = 2 * π * zeroCount f U (Rectangle z w) := by
  rw [sub_eq_two_pi_mul_divisorCount_of_rectBoundary hre him hRU hf hreg hne hθ hlift,
    divisorCount_eq_zeroCount hnonneg, Int.cast_natCast]

end TauCeti.Contour
