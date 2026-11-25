/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Rectangle.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Argument.Divisor
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The divisor form of the argument principle on a rectangle

`TauCeti.Contour.argumentPrinciple_rectBoundary_divisor` evaluates the integral of `f'/f`
around a closed rectangle as `2πi` times its signed divisor count. Meromorphy on any
set containing the rectangle and order zero on its frontier suffice; neither openness
of that set nor analyticity of the chosen representative on the frontier is required.

The proof delegates to `TauCeti.Contour.argumentPrinciple_nullHomologous_divisor`, which fills
isolated representative defects on a compact neighbourhood of the rectangle and compares divisors
only on the rectangle, keeping the original ambient domain in the count.

`TauCeti.Contour.argumentPrinciple_rectBoundary_zeroCount` gives the corresponding natural
zero count when the rectangle contains no negative divisor values.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}

/-- The integral of the logarithmic derivative around a rectangle is `2πi` times its signed
divisor count. The ambient meromorphic set need not be open or connected; isolated changes
of representative values on the frontier are allowed. The rectangle may be degenerate. -/
theorem argumentPrinciple_rectBoundary_divisor (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * (divisorCount f U (Rectangle z w) : ℂ) :=
  argumentPrinciple_nullHomologous_divisor
    (isCompact_uIcc.reProdIm isCompact_uIcc) (convex_rectangle z w).isPreconnected
    hRU hf hfr (isPiecewiseC1On_rectBoundary z w).absolutelyContinuousOnInterval
    (fun t _ ↦ rectBoundary_mem_frontier t) (by simp)
    (isNullHomologous_rectBoundary Subset.rfl)
    (fun x hx ↦ windingNumber_rectBoundary_eq_one (interior_rectangle hre him ▸ hx))

/-- If the divisor has no negative values in the rectangle, the boundary integral counts
zeros with their natural multiplicities, without subtracting any poles. -/
theorem argumentPrinciple_rectBoundary_zeroCount (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0)
    (hnonneg : ∀ x ∈ Rectangle z w, 0 ≤ MeromorphicOn.divisor f U x) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * (zeroCount f U (Rectangle z w) : ℂ) := by
  rw [argumentPrinciple_rectBoundary_divisor hre him hRU hf hfr,
    divisorCount_eq_zeroCount hnonneg, Int.cast_natCast]

end TauCeti.Contour
