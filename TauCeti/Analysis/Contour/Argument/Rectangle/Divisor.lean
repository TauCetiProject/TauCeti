/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Rectangle.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Meromorphic.NormalForm

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

open Set Complex Metric
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
      2 * π * I * (divisorCount f U (Rectangle z w) : ℂ) := by
  classical
  -- Apply the pointwise rectangle principle using Mathlib's local finiteness of
  -- meromorphic divisors and nonanalytic points.
  -- Work on a relatively compact convex neighbourhood rather than the possibly
  -- disconnected, unbounded domain `U`.
  have hcompact : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_cthickening_subset_open hU hRU
  let V := thickening δ (Rectangle z w)
  have hRV : Rectangle z w ⊆ V := self_subset_thickening hδ _
  have hVU : V ⊆ U := (thickening_subset_cthickening δ _).trans hδU
  have hfV : MeromorphicOn f V := hf.mono_set hVU
  have hzfr : z ∈ frontier (Rectangle z w) := by simp [frontier_rectangle, mem_reProdIm]
  have hzV : z ∈ V := hRV (by simp [Rectangle, mem_reProdIm])
  have htop (x : ℂ) (hx : x ∈ V) : meromorphicOrderAt f x ≠ ⊤ :=
    hfV.meromorphicOrderAt_ne_top_of_isPreconnected
      ((convex_rectangle z w).thickening δ).isPreconnected hzV hx (by simp [hfr z hzfr])
  have hfinite : (Function.support (MeromorphicOn.divisor f V)).Finite :=
    (hf.mono_set hδU).divisor_support_finite_of_subset hcompact.cthickening
      (thickening_subset_cthickening δ _)
  have hdefects := hcompact.cthickening.finite_sdiff_of_mem_codiscreteWithin
    (hf.mono_set hδU).analyticAt_mem_codiscreteWithin
  let S := hfinite.toFinset ∪ hdefects.toFinset
  -- Include nonanalytic representative values as well as the divisor support.
  -- Removable defects have order zero and do not change the count.
  have hoff (x : ℂ) (hx : x ∈ V) (hxS : x ∉ S) : AnalyticAt ℂ f x ∧ f x ≠ 0 := by
    have hxoff := Finset.notMem_union.mp hxS
    have hd : MeromorphicOn.divisor f V x = 0 := by simpa using hxoff.1
    have ho : meromorphicOrderAt f x = 0 := by
      rw [hfV.divisor_apply hx, WithTop.untop₀_eq_zero] at hd
      exact hd.resolve_right (htop x hx)
    have ha : AnalyticAt ℂ f x := by
      by_contra ha
      exact hxoff.2 (hdefects.mem_toFinset.mpr
        ⟨thickening_subset_cthickening δ _ hx, ha⟩)
    exact ⟨ha, ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp ho⟩
  have hSfr (x : ℂ) (hx : x ∈ S) : x ∉ frontier (Rectangle z w) := by
    intro hxfr
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxV := (MeromorphicOn.divisor f V).supportWithinDomain
        (by simpa using hx)
      have hd : MeromorphicOn.divisor f V x ≠ 0 := by simpa using hx
      exact hd (by simp [hfV.divisor_apply hxV, hfr x hxfr])
    · exact (hdefects.mem_toFinset.mp hx).2 (hreg x hxfr)
  -- Express the count using exactly the finite set passed to the pointwise
  -- argument principle; the two divisors agree on the rectangle.
  have hcount : divisorCount f U (Rectangle z w) =
      ∑ x ∈ S with x ∈ Rectangle z w, MeromorphicOn.divisor f U x := by
    rw [divisorCount_def]
    apply finsum_mem_eq_sum_of_subset
    · intro x hx
      refine Finset.mem_filter.mpr ⟨?_, hx.1⟩
      apply Finset.mem_union_left
      simpa only [Finite.mem_toFinset, Function.mem_support,
        hf.divisor_apply (hRU hx.1), hfV.divisor_apply (hRV hx.1)] using hx.2
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  rw [argumentPrinciple_rectBoundary (ord := MeromorphicOn.divisor f V) hre him
    isOpen_thickening hRV hoff (fun x _ hx ↦ hfV x hx)
    (fun x _ hx ↦ by
      rw [hfV.divisor_apply hx, WithTop.coe_untop₀_of_ne_top (htop x hx)]) hSfr]
  congr 1
  rw [hcount, Int.cast_sum]
  exact Finset.sum_congr rfl fun x hx ↦ by
    rw [hfV.divisor_apply (hRV (Finset.mem_filter.mp hx).2),
      hf.divisor_apply (hRU (Finset.mem_filter.mp hx).2)]

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
