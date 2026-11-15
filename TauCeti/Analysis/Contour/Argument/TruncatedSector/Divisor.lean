/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.TruncatedSector.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Convex

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

open Set Complex Metric
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
      2 * π * I * (divisorCount f U (closedTruncatedSector z₀ r R θ₁ θ₂) : ℂ) := by
  classical
  set K := closedTruncatedSector z₀ r R θ₁ θ₂
  have hcompact : IsCompact K := isCompact_closedTruncatedSector z₀ r R θ₁ θ₂
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_cthickening_subset_open hU hSU
  let V := thickening δ K
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have hVU : V ⊆ U := (thickening_subset_cthickening δ K).trans hδU
  have hfV : MeromorphicOn f V := hf.mono_set hVU
  have hV_preconn : IsPreconnected V := by
    refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
    obtain ⟨a, ha, hxa⟩ := mem_thickening_iff.1 hx
    obtain ⟨b, hb, hyb⟩ := mem_thickening_iff.1 hy
    refine ⟨ball a δ ∪ K ∪ ball b δ, ?_, Or.inl (Or.inl (mem_ball.2 hxa)),
      Or.inr (mem_ball.2 hyb), ?_⟩
    · exact union_subset (union_subset (ball_subset_thickening ha δ) hKV)
        (ball_subset_thickening hb δ)
    · exact (((convex_ball a δ).isPreconnected).union a (mem_ball_self hδ) ha
        (isPreconnected_closedTruncatedSector z₀ r R θ₁ θ₂)).union b (Or.inr hb)
          (mem_ball_self hδ) (convex_ball b δ).isPreconnected
  have hzfr : circleMap z₀ r θ₁ ∈ frontier K := by
    simpa using truncatedSectorBoundary_mem_frontier hr hrR hθ hspan 0
  have hzV : circleMap z₀ r θ₁ ∈ V :=
    hKV (circleMap_mem_closedTruncatedSector (left_mem_Icc.2 hrR) (left_mem_Icc.2 hθ))
  have htop (x : ℂ) (hx : x ∈ V) : meromorphicOrderAt f x ≠ ⊤ :=
    hfV.meromorphicOrderAt_ne_top_of_isPreconnected hV_preconn hzV hx (by simp [hfr _ hzfr])
  have hfinite : (Function.support (MeromorphicOn.divisor f V)).Finite :=
    (hf.mono_set hδU).divisor_support_finite_of_subset hcompact.cthickening
      (thickening_subset_cthickening δ K)
  have hdefects := hcompact.cthickening.finite_sdiff_of_mem_codiscreteWithin
    (hf.mono_set hδU).analyticAt_mem_codiscreteWithin
  let S := hfinite.toFinset ∪ hdefects.toFinset
  have hoff (x : ℂ) (hx : x ∈ V) (hxS : x ∉ S) : AnalyticAt ℂ f x ∧ f x ≠ 0 := by
    have hxoff := Finset.notMem_union.mp hxS
    have hd : MeromorphicOn.divisor f V x = 0 := by simpa using hxoff.1
    have ho : meromorphicOrderAt f x = 0 := by
      rw [hfV.divisor_apply hx, WithTop.untop₀_eq_zero] at hd
      exact hd.resolve_right (htop x hx)
    have ha : AnalyticAt ℂ f x := by
      by_contra ha
      exact hxoff.2 (hdefects.mem_toFinset.mpr
        ⟨thickening_subset_cthickening δ K hx, ha⟩)
    exact ⟨ha, ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp ho⟩
  have hSfr (x : ℂ) (hx : x ∈ S) : x ∉ frontier K := by
    intro hxfr
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxV := (MeromorphicOn.divisor f V).supportWithinDomain (by simpa using hx)
      have hd : MeromorphicOn.divisor f V x ≠ 0 := by simpa using hx
      exact hd (by simp [hfV.divisor_apply hxV, hfr x hxfr])
    · exact (hdefects.mem_toFinset.mp hx).2 (hreg x hxfr)
  have hcount : divisorCount f U K = ∑ x ∈ S with x ∈ K, MeromorphicOn.divisor f U x := by
    rw [divisorCount_def]
    apply finsum_mem_eq_sum_of_subset
    · intro x hx
      refine Finset.mem_filter.mpr ⟨?_, hx.1⟩
      apply Finset.mem_union_left
      simpa only [Finite.mem_toFinset, Function.mem_support,
        hf.divisor_apply (hSU hx.1), hfV.divisor_apply (hKV hx.1)] using hx.2
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  rw [argumentPrinciple_truncatedSectorBoundary (ord := MeromorphicOn.divisor f V) hr hrR hθ hspan
    isOpen_thickening hKV hoff (fun x _ hx ↦ hfV x hx)
    (fun x _ hx ↦ by
      rw [hfV.divisor_apply hx, WithTop.coe_untop₀_of_ne_top (htop x hx)]) hSfr]
  congr 1
  rw [hcount, Int.cast_sum]
  exact Finset.sum_congr rfl fun x hx ↦ by
    rw [hfV.divisor_apply (hKV (Finset.mem_filter.mp hx).2),
      hf.divisor_apply (hSU (Finset.mem_filter.mp hx).2)]

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
