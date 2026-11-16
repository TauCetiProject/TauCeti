/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Rectangle.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import TauCeti.Analysis.Contour.Argument.Divisor
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The divisor form of the argument principle on a rectangle

`TauCeti.Contour.argumentPrinciple_rectBoundary_divisor` evaluates the integral of `f'/f`
around a closed rectangle as `2πi` times its signed divisor count. Meromorphy on an open
neighbourhood and order zero on the frontier suffice to construct the finite exceptional
set internally; no global finiteness or connectedness of the neighbourhood is required.

The chosen representative must be analytic on the frontier of the rectangle.
This condition matters on the contour: changing an isolated value of a meromorphic function
does not change its divisor, but can destroy the pointwise regularity needed by the contour
integral. The theorem therefore applies directly to analytic functions and to meromorphic
functions whose removable singularities on the contour are filled in. Isolated representative
defects away from the contour are allowed.

`TauCeti.Contour.argumentPrinciple_rectBoundary_zeroCount` gives the corresponding natural
zero count when the rectangle contains no negative divisor values.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}

/-- The integral of the logarithmic derivative around a rectangle is `2πi` times its signed
divisor count. The representative is required to be analytic on the frontier;
order zero alone would not guarantee pointwise regularity on the contour.

The rectangle may be degenerate, and the open meromorphic domain need not be connected. -/
theorem argumentPrinciple_rectBoundary_divisor (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * (divisorCount f U (Rectangle z w) : ℂ) :=
  argumentPrinciple_nullHomologous_divisor
    (isCompact_uIcc.reProdIm isCompact_uIcc) (convex_rectangle z w).isPreconnected
    hU hRU hf hreg hfr (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ rectBoundary_mem_frontier t) (by simp)
    (isNullHomologous_rectBoundary Subset.rfl)
    (fun x hx ↦ windingNumber_rectBoundary_eq_one (interior_rectangle hre him ▸ hx))

/-- If the divisor has no negative values in the rectangle, the boundary integral counts
zeros with their natural multiplicities, without subtracting any poles. -/
theorem argumentPrinciple_rectBoundary_zeroCount (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (Rectangle z w), AnalyticAt ℂ f x)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0)
    (hnonneg : ∀ x ∈ Rectangle z w, 0 ≤ MeromorphicOn.divisor f U x) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * (zeroCount f U (Rectangle z w) : ℂ) := by
  rw [argumentPrinciple_rectBoundary_divisor hre him hU hRU hf hreg hfr,
    divisorCount_eq_zeroCount hnonneg, Int.cast_natCast]

end TauCeti.Contour
