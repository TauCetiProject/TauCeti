/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The argument principle on a rectangle

For a closed rectangle `R = Complex.Rectangle z w` with `z` its lower left corner, contained in an
open set `U`, and a function `f` analytic and nonvanishing on `U` off a finite set `S` that avoids
the frontier of `R`, the contour integral of the logarithmic derivative of `f` along the
counterclockwise boundary `Complex.rectBoundary z w` is

`∫ t in 0..4, γ' t • logDeriv f (γ t) = 2πi · ∑_{s ∈ S ∩ R} ord_s f`:

each zero or pole of `f` inside the rectangle is counted once with its order, and those outside
are not counted at all. This is the argument principle for null-homologous curves,
`TauCeti.Contour.argumentPrinciple_nullHomologous`, with the winding numbers of the rectangle
boundary evaluated: `1` at the points of `S` inside the rectangle, which lie in its interior since
`S` avoids the frontier, and `0` at those outside. It is the form in which the argument principle
counts the zeros of an L-function in a rectangle of the critical strip.

The sum over all of `S` would be false: for `U = ℂ`, the square with corners `-1 - I` and `1 + I`,
`f z = z - 2` and `S = {2}`, every other hypothesis holds, the integral is `0`, and the order of
`f` at `2` is `1`.

## Main results

* `TauCeti.Contour.argumentPrinciple_rectBoundary`: the argument principle on a rectangle, with
  caller-supplied orders at the points of `S`.
* `TauCeti.Contour.argumentPrinciple_rectBoundary_of_analyticOnNhd`: the zero-counting form, for
  `f` analytic on `U` and nonvanishing on the frontier of the rectangle.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {z w : ℂ}

/-- The winding number of the rectangle boundary about a point off its frontier is the indicator
of the rectangle. -/
private theorem windingNumber_rectBoundary_eq_ite (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {s : ℂ} (hfr : s ∉ frontier (Rectangle z w)) [Decidable (s ∈ Rectangle z w)] :
    windingNumber (rectBoundary z w) 0 4 s = if s ∈ Rectangle z w then 1 else 0 := by
  split_ifs with hs
  · exact windingNumber_rectBoundary_eq_one (mem_Ioo_reProdIm_of_mem_rectangle hre him hs hfr)
  · exact windingNumber_rectBoundary_eq_zero hs

/-- The rectangle boundary over `[0, 4]` lies in every set containing the closed rectangle. -/
private theorem rectBoundary_mem_of_rectangle_subset (hRU : Rectangle z w ⊆ U) {t : ℝ}
    (ht : t ∈ uIcc (0 : ℝ) 4) : rectBoundary z w t ∈ U :=
  hRU (rectBoundary_mem_rectangle (by rwa [uIcc_of_le (by norm_num)] at ht))

/-- The rectangle boundary over `[0, 4]` lies on the frontier of the rectangle. -/
private theorem rectBoundary_mem_frontier_of_mem_uIcc {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 4) :
    rectBoundary z w t ∈ frontier (Rectangle z w) :=
  rectBoundary_mem_frontier (by rwa [uIcc_of_le (by norm_num)] at ht)

open scoped Classical in
/-- **The argument principle on a rectangle.** Let `z` be the lower left corner of a closed
rectangle `Rectangle z w` contained in an open set `U`, and let `f` be analytic and nonvanishing at
every point of `U` outside a finite set `S` that avoids the frontier of the rectangle, meromorphic
at the points of `S` in `U`, with integer orders `ord` there. Then the contour integral of
`logDeriv f` along the counterclockwise boundary is `2πi` times the sum of the orders at the points
of `S` in the rectangle.

Nothing is asked of `f` or `ord` at points of `S` outside `U`, which lie outside the rectangle and
do not contribute. -/
theorem argumentPrinciple_rectBoundary {ord : ℂ → ℤ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U)
    (hoff : ∀ x ∈ U, x ∉ S → AnalyticAt ℂ f x ∧ f x ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, (ord s : ℂ) := by
  rw [argumentPrinciple_nullHomologous hU hoff hmero hord (isPiecewiseC1On_rectBoundary z w)
    (fun _ ↦ rectBoundary_mem_of_rectangle_subset hRU) (by simp)
    (fun _ ht hS' ↦ hS _ hS' (rectBoundary_mem_frontier_of_mem_uIcc ht))
    (isNullHomologous_rectBoundary hRU), Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  rw [windingNumber_rectBoundary_eq_ite hre him (hS s hs)]
  split_ifs <;> simp

open scoped Classical in
/-- **Counting zeros in a rectangle.** Let `z` be the lower left corner of a closed rectangle
`Rectangle z w` contained in an open set `U`, and let `f` be analytic on `U`, with its zeros in `U`
contained in a finite set `S`, and nonvanishing on the frontier of the rectangle. Then the contour
integral of `logDeriv f` along the counterclockwise boundary is `2πi` times the number of zeros of
`f` in the rectangle, counted with multiplicity. -/
theorem argumentPrinciple_rectBoundary_of_analyticOnNhd (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hzeros : ∀ x ∈ U, f x = 0 → x ∈ S) (hfr : ∀ x ∈ frontier (Rectangle z w), f x ≠ 0) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, (analyticOrderNatAt f s : ℂ) := by
  rw [argumentPrinciple_nullHomologous_of_analyticOnNhd hU hf hzeros
    (isPiecewiseC1On_rectBoundary z w) (fun _ ↦ rectBoundary_mem_of_rectangle_subset hRU)
    (by simp) (fun _ ht ↦ hfr _ (rectBoundary_mem_frontier_of_mem_uIcc ht))
    (isNullHomologous_rectBoundary hRU), Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun s _ ↦ ?_)
  by_cases hs : s ∈ frontier (Rectangle z w)
  · -- On the frontier `f` does not vanish, so the order is `0` and both sides vanish.
    have h0 : analyticOrderNatAt f s = 0 := by
      rw [analyticOrderNatAt, (hf s (hRU ((isClosed_rectangle z w).frontier_subset hs)))
        |>.analyticOrderAt_eq_zero.2 (hfr s hs), ENat.toNat_zero]
    simp [h0]
  · rw [windingNumber_rectBoundary_eq_ite hre him hs]
    split_ifs <;> simp

end TauCeti.Contour
