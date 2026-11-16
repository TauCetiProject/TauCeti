/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.TruncatedSector.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import TauCeti.Analysis.Contour.Argument.Divisor
import TauCeti.Analysis.Contour.Winding.Number.TruncatedSector

/-!
# The divisor and zero-counting forms of the argument principle on a truncated sector

`TauCeti.Contour.argumentPrinciple_truncatedSectorBoundary_divisor` evaluates the contour integral
of `logDeriv f` around `Complex.truncatedSectorBoundary z₀ r R θ₁ θ₂` (for `0 ≤ r ≤ R` and
`0 ≤ θ₂ - θ₁ < 2π`) as `2πi` times the signed divisor count `TauCeti.divisorCount` on
`Complex.closedTruncatedSector z₀ r R θ₁ θ₂`. Meromorphy on an open neighbourhood and order zero
(together with analyticity of the chosen representative) on the frontier suffice to construct the
finite exceptional set internally; the ambient open set `U` need not be connected or bounded, and
the truncated sector may be degenerate (`r = R` or `θ₁ = θ₂`) or a full sector (`r = 0`).

`TauCeti.Contour.argumentPrinciple_truncatedSectorBoundary_zeroCount` specializes to the natural
zero count `TauCeti.zeroCount` when no negative divisor values occur in the truncated sector, and
`TauCeti.Contour.argumentPrinciple_truncatedSectorBoundary_finsum_analyticOrderNatAt` specializes
further to a function analytic on a neighbourhood of the closed truncated sector and nonvanishing on
its frontier, expressing the integral directly in terms of
`∑ᶠ z ∈ openTruncatedSector z₀ r R θ₁ θ₂, analyticOrderNatAt f z` without requiring an ambient open
set or finiteness witness from the caller.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {r R θ₁ θ₂ : ℝ}

/-- **Divisor form of the argument principle on a truncated sector.** For `0 ≤ r ≤ R` and
`0 ≤ θ₂ - θ₁ < 2π`, if `f` is meromorphic on an open neighbourhood `U` of
`closedTruncatedSector z₀ r R θ₁ θ₂`, analytic on its frontier, and of meromorphic order `0` on its
frontier, then the contour integral of `logDeriv f` around `truncatedSectorBoundary z₀ r R θ₁ θ₂`
is `2πi` times `divisorCount f U (closedTruncatedSector z₀ r R θ₁ θ₂)`. -/
theorem argumentPrinciple_truncatedSectorBoundary_divisor
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    (hU : IsOpen U) (hSU : closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), AnalyticAt ℂ f x)
    (hfr : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), meromorphicOrderAt f x = 0) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          logDeriv f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      2 * π * I * (divisorCount f U (closedTruncatedSector z₀ r R θ₁ θ₂) : ℂ) :=
  argumentPrinciple_nullHomologous_divisor
    (isCompact_closedTruncatedSector z₀ r R θ₁ θ₂)
    (isPreconnected_closedTruncatedSector z₀ r R θ₁ θ₂)
    hU hSU hf hreg hfr (isPiecewiseC1On_truncatedSectorBoundary z₀ r R θ₁ θ₂)
    (fun t _ ↦ truncatedSectorBoundary_mem_frontier hr hrR hθ hspan t) (by simp)
    (isNullHomologous_truncatedSectorBoundary hrR hθ Subset.rfl)
    (fun x hx ↦ windingNumber_truncatedSectorBoundary_eq_one hr hspan
      (interior_closedTruncatedSector hr hrR hθ hspan ▸ hx))

/-- **Zero-counting form of the argument principle on a truncated sector.** If the divisor of `f`
has no negative values in `closedTruncatedSector z₀ r R θ₁ θ₂`, the boundary integral counts zeros
with their natural multiplicities `zeroCount f U (closedTruncatedSector z₀ r R θ₁ θ₂)`. -/
theorem argumentPrinciple_truncatedSectorBoundary_zeroCount
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    (hU : IsOpen U) (hSU : closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), AnalyticAt ℂ f x)
    (hfr : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), meromorphicOrderAt f x = 0)
    (hnonneg : ∀ x ∈ closedTruncatedSector z₀ r R θ₁ θ₂, 0 ≤ MeromorphicOn.divisor f U x) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          logDeriv f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      2 * π * I * (zeroCount f U (closedTruncatedSector z₀ r R θ₁ θ₂) : ℂ) := by
  rw [argumentPrinciple_truncatedSectorBoundary_divisor hr hrR hθ hspan hU hSU hf hreg hfr,
    divisorCount_eq_zeroCount hnonneg, Int.cast_natCast]

/-- **Holomorphic zero-counting form of the argument principle on a truncated sector.** If `f` is
analytic on a neighbourhood of `closedTruncatedSector z₀ r R θ₁ θ₂` (with `0 ≤ r ≤ R` and
`0 ≤ θ₂ - θ₁ < 2π`) and does not vanish on its frontier, then the contour integral of `logDeriv f`
around `truncatedSectorBoundary z₀ r R θ₁ θ₂` is `2πi` times
`∑ᶠ z ∈ openTruncatedSector z₀ r R θ₁ θ₂, analyticOrderNatAt f z`. No ambient open set or finite
zero-set witness is needed from the caller. -/
theorem argumentPrinciple_truncatedSectorBoundary_finsum_analyticOrderNatAt
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    (hf : AnalyticOnNhd ℂ f (closedTruncatedSector z₀ r R θ₁ θ₂))
    (hfr : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), f x ≠ 0) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          logDeriv f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      2 * π * I *
        ((∑ᶠ z ∈ openTruncatedSector z₀ r R θ₁ θ₂, analyticOrderNatAt f z : ℕ) : ℂ) := by
  let U : Set ℂ := {x | AnalyticAt ℂ f x}
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hfU : AnalyticOnNhd ℂ f U := fun _ hx ↦ hx
  have hfr_sub := (isClosed_closedTruncatedSector z₀ r R θ₁ θ₂).frontier_subset
  have hfr_ord (x : ℂ) (hx : x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂)) :
      meromorphicOrderAt f x = 0 := by
    have hfx : AnalyticAt ℂ f x := hf x (hfr_sub hx)
    rw [hfx.meromorphicOrderAt_eq, hfx.analyticOrderAt_eq_zero.2 (hfr x hx)]
    rfl
  rw [argumentPrinciple_truncatedSectorBoundary_zeroCount hr hrR hθ hspan hU hf hfU.meromorphicOn
    (fun x hx ↦ hf x (hfr_sub hx)) hfr_ord
    (fun x _ ↦ MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU x)]
  congr 2
  rw [← zeroCount_interior (fun x hx ↦ (hf x (hfr_sub hx)).divisor_apply_eq_zero (hfr x hx)),
    interior_closedTruncatedSector hr hrR hθ hspan, zeroCount_def]
  refine finsum_mem_congr rfl fun z hz ↦ ?_
  have hzK := openTruncatedSector_subset_closedTruncatedSector z₀ r R θ₁ θ₂ hz
  rw [hfU.meromorphicOn.divisor_eq_analyticOrderNatAt (hf z hzK) (hf z hzK), Int.toNat_natCast]

end TauCeti.Contour
