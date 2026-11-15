/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Curve.TruncatedSector
import TauCeti.Analysis.Contour.Winding.Number.TruncatedSector

/-!
# The argument principle on a truncated sector

For a closed truncated sector `K = Complex.closedTruncatedSector z₀ r R θ₁ θ₂` with `0 ≤ r ≤ R` and
`0 ≤ θ₂ - θ₁ < 2π`, contained in an open set `U`, and a function `f` analytic and nonvanishing on
`U` off a finite set `S` that avoids `frontier K`, the contour integral of the logarithmic
derivative of `f` along the counterclockwise boundary
`γ = Complex.truncatedSectorBoundary z₀ r R θ₁ θ₂` is

`∫ t in 0..4, γ' t • logDeriv f (γ t) = 2πi · ∑_{s ∈ S ∩ K} ord_s f`:

each zero or pole of `f` inside `K` is counted once with its order, and those outside `K` are not
counted at all. Both genuinely truncated sectors (`0 < r`) and full sectors (`r = 0`) are covered.

This specializes the homological argument principle
`TauCeti.Contour.argumentPrinciple_nullHomologous` using the winding numbers of
`truncatedSectorBoundary` from `TauCeti.Analysis.Contour.Winding.Number.TruncatedSector`: `1` at
points of `S` in `K` (which lie in `openTruncatedSector z₀ r R θ₁ θ₂` because `S` avoids
`frontier K`) and `0` at points outside `K`. Combined with
`Complex.integral_truncatedSectorBoundary`, the contour integral splits into two radial integrals
over `r..R` and two circular-arc integrals over `θ₁..θ₂`.

## Main results

* `TauCeti.Contour.argumentPrinciple_truncatedSectorBoundary`: the argument principle on a
  truncated sector, with caller-supplied integer orders at the points of `S`.
* `TauCeti.Contour.argumentPrinciple_truncatedSectorBoundary_of_analyticOnNhd`: the holomorphic
  zero-counting form, for `f` analytic on `U` and nonvanishing on the frontier of the truncated
  sector.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {z₀ : ℂ} {r R θ₁ θ₂ : ℝ}

/-- The winding number of `truncatedSectorBoundary` about a point off the frontier of the closed
truncated sector is the indicator of `closedTruncatedSector z₀ r R θ₁ θ₂`. -/
private theorem windingNumber_truncatedSectorBoundary_eq_ite
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    {s : ℂ} (hfr : s ∉ frontier (closedTruncatedSector z₀ r R θ₁ θ₂))
    [Decidable (s ∈ closedTruncatedSector z₀ r R θ₁ θ₂)] :
    windingNumber (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 s =
      if s ∈ closedTruncatedSector z₀ r R θ₁ θ₂ then 1 else 0 := by
  split_ifs with hs
  · exact windingNumber_truncatedSectorBoundary_eq_one hr hspan
      (mem_openTruncatedSector_of_mem_closedTruncatedSector hr hrR hθ hspan hs hfr)
  · exact windingNumber_truncatedSectorBoundary_eq_zero hrR hθ hs

open scoped Classical in
/-- **The argument principle on a truncated sector.** Let `closedTruncatedSector z₀ r R θ₁ θ₂`
(with `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`) be contained in an open set `U`, and let `f` be analytic
and nonvanishing at every point of `U` outside a finite set `S` that avoids the frontier of the
truncated sector, meromorphic at the points of `S` in `U`, with integer orders `ord` there. Then
the contour integral of `logDeriv f` along `truncatedSectorBoundary z₀ r R θ₁ θ₂` is `2πi` times
the sum of `ord` over the points of `S` in the truncated sector.

Nothing is asked of `f` or `ord` at points of `S` outside `U`, which lie outside the truncated
sector and do not contribute. -/
theorem argumentPrinciple_truncatedSectorBoundary {ord : ℂ → ℤ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    (hU : IsOpen U) (hSU : closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ U)
    (hoff : ∀ x ∈ U, x ∉ S → AnalyticAt ℂ f x ∧ f x ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hS : ∀ s ∈ S, s ∉ frontier (closedTruncatedSector z₀ r R θ₁ θ₂)) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          logDeriv f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      2 * π * I * ∑ s ∈ S with s ∈ closedTruncatedSector z₀ r R θ₁ θ₂, (ord s : ℂ) := by
  rw [argumentPrinciple_nullHomologous hU hoff hmero hord
    (isPiecewiseC1On_truncatedSectorBoundary z₀ r R θ₁ θ₂)
    (fun t _ ↦ hSU (truncatedSectorBoundary_mem_closedTruncatedSector hrR hθ t))
    (by simp)
    (fun _ _ hS' ↦ hS _ hS' (truncatedSectorBoundary_mem_frontier hr hrR hθ hspan _))
    (isNullHomologous_truncatedSectorBoundary hrR hθ hSU), Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  rw [windingNumber_truncatedSectorBoundary_eq_ite hr hrR hθ hspan (hS s hs)]
  split_ifs <;> simp

open scoped Classical in
/-- **Counting zeros in a truncated sector.** Let `closedTruncatedSector z₀ r R θ₁ θ₂` (with
`0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`) be contained in an open set `U`, and let `f` be analytic on
`U`, with its zeros in `U` contained in a finite set `S`, and nonvanishing on the frontier of the
truncated sector. Then the contour integral of `logDeriv f` along
`truncatedSectorBoundary z₀ r R θ₁ θ₂` is `2πi` times the number of zeros of `f` in the truncated
sector, counted with multiplicity. -/
theorem argumentPrinciple_truncatedSectorBoundary_of_analyticOnNhd
    (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * π)
    (hU : IsOpen U) (hSU : closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hzeros : ∀ x ∈ U, f x = 0 → x ∈ S)
    (hfr : ∀ x ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂), f x ≠ 0) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          logDeriv f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      2 * π * I *
        ∑ s ∈ S with s ∈ closedTruncatedSector z₀ r R θ₁ θ₂, (analyticOrderNatAt f s : ℂ) := by
  rw [argumentPrinciple_nullHomologous_of_analyticOnNhd hU hf hzeros
    (isPiecewiseC1On_truncatedSectorBoundary z₀ r R θ₁ θ₂)
    (fun t _ ↦ hSU (truncatedSectorBoundary_mem_closedTruncatedSector hrR hθ t))
    (by simp)
    (fun _ _ ↦ hfr _ (truncatedSectorBoundary_mem_frontier hr hrR hθ hspan _))
    (isNullHomologous_truncatedSectorBoundary hrR hθ hSU), Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun s _ ↦ ?_)
  by_cases hs : s ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂)
  · have h0 : analyticOrderNatAt f s = 0 := by
      rw [analyticOrderNatAt,
        (hf s (hSU ((isClosed_closedTruncatedSector z₀ r R θ₁ θ₂).frontier_subset hs)))
          |>.analyticOrderAt_eq_zero.2 (hfr s hs),
        ENat.toNat_zero]
    simp [h0]
  · rw [windingNumber_truncatedSectorBoundary_eq_ite hr hrR hθ hspan hs]
    split_ifs <;> simp

end TauCeti.Contour
