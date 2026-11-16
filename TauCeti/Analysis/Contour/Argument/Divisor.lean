/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Argument.Principle
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Normed.Module.Connected

/-!
# The argument principle against the divisor

`TauCeti.Contour.argumentPrinciple` and `TauCeti.Contour.argumentPrinciple_nullHomologous` ask the
caller for the data of the counting problem: a finite set `S` collecting the nonzero-order points,
an order function `ord`, and proofs that the two agree and that `S` is exhaustive. Mathlib's
`MeromorphicOn.divisor` already packages that data — `MeromorphicOn.divisor_apply` evaluates it to
`(meromorphicOrderAt f z).untop₀`, and local compactness supplies finiteness of the divisor support
and of isolated representative defects. This file restates both the circle and null-homologous
argument principles against the divisor API, so callers that already speak `divisor` or
`TauCeti.divisorCount` need not rebuild the finset and the order function by hand.

Requiring `meromorphicOrderAt f z = 0` on the boundary does double duty:

* It confines the nonzero-order points to the interior, so a divisor taken over the open disc (or
  counted on the compact region `K`) accounts for every such point.
* It rules out order `⊤`. This matters because `(⊤ : WithTop ℤ).untop₀ = 0`, so at a point where `f`
  vanishes identically the divisor reads `0` while the order does not, and the exhaustiveness
  obligation would fail. Because `closedBall c R` is convex (hence preconnected, with nonempty
  sphere for `0 ≤ R`) and a thickening of a preconnected compact set `K` is preconnected (with
  nonempty frontier visited by `γ`), `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`
  propagates the finite order at a boundary point to the whole region.

For a general piecewise-`C¹` boundary curve (`argumentPrinciple_nullHomologous_divisor`), the chosen
representative must also be analytic on `frontier K`: changing an isolated value of a meromorphic
function does not change its divisor, but can destroy the pointwise regularity needed by the contour
integral. Isolated representative defects away from `frontier K` are allowed and absorbed into the
internal finite exceptional set `S`.

## Main results

* `TauCeti.Contour.argumentPrinciple_divisor` —
  `∮_{C(c,R)} logDeriv f = 2πi · ∑ᶠ z, divisor f (ball c R) z`, the circle argument principle with
  the counting data taken from `MeromorphicOn.divisor`.
* `TauCeti.Contour.argumentPrinciple_nullHomologous_divisor` —
  `∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · divisorCount f U K` for a closed piecewise-`C¹`
  curve `γ` on `frontier K` that is null-homologous in a compact preconnected set `K ⊆ U` and winds
  once around every point of `interior K`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Metric Set
open scoped Interval

namespace TauCeti.Contour

/-- **The argument principle, against the divisor.** For `f` meromorphic on the closed disc
`C(c, R)` with no zero or pole on the bounding circle, the contour integral of the logarithmic
derivative is `2πi` times the sum of `MeromorphicOn.divisor` over the open disc.

This is `TauCeti.Contour.argumentPrinciple` with the finite set and the order function supplied by
Mathlib's divisor API rather than by the caller. -/
theorem argumentPrinciple_divisor {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : MeromorphicOn f (closedBall c R))
    (hsphere : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0) :
    circleIntegral (logDeriv f) c R
      = 2 * (Real.pi : ℂ) * Complex.I *
        (∑ᶠ z, ((MeromorphicOn.divisor f (ball c R) z : ℤ) : ℂ)) := by
  have hfb : MeromorphicOn f (ball c R) := hf.mono_set ball_subset_closedBall
  set S := (MeromorphicOn.divisor_ball_support_finite hf).toFinset
  rw [finsum_eq_finsetSum_of_support_subset _ (s := S) fun z hz => by simpa [S] using hz]
  have hxs : c + (R : ℂ) ∈ sphere c R := by simp [abs_of_nonneg hR]
  have htop : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ := fun z hz =>
    hf.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (sphere_subset_closedBall hxs) hz (by simp [hsphere _ hxs])
  refine argumentPrinciple hR S _ hf (fun z hz => ?_) (fun z hz hord => ?_) fun z hz => ?_
  · exact (MeromorphicOn.divisor f (ball c R)).supportWithinDomain (by simpa [S] using hz)
  · have hzball : z ∈ ball c R := by
      rw [← closedBall_sdiff_sphere]; exact ⟨hz, fun h => hord (hsphere z h)⟩
    simpa [S, hfb, hzball, WithTop.untop₀_eq_zero, htop z hz] using hord
  · have hzball := (MeromorphicOn.divisor f (ball c R)).supportWithinDomain (by simpa [S] using hz)
    rw [MeromorphicOn.divisor_apply hfb hzball,
      WithTop.coe_untop₀_of_ne_top (htop z (ball_subset_closedBall hzball))]

/-- **The argument principle against the divisor on a compact preconnected region.** Let `K` be a
compact preconnected set contained in an open set `U`, let `f` be meromorphic on `U`, analytic on
`frontier K`, and of meromorphic order `0` on `frontier K`, and let `γ` be a closed piecewise-`C¹`
curve on `[[a, b]]` tracing points of `frontier K`, null-homologous in `K`, and winding once around
every point of `interior K`. Then the contour integral of `logDeriv f` along `γ` is `2πi` times
`divisorCount f U K`.

No global connectedness or boundedness of `U` is required, and isolated representative defects of
`f` away from `frontier K` are allowed. -/
theorem argumentPrinciple_nullHomologous_divisor {f : ℂ → ℂ} {U K : Set ℂ}
    (hK : IsCompact K) (hK_conn : IsPreconnected K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hf : MeromorphicOn f U)
    (hreg : ∀ x ∈ frontier K, AnalyticAt ℂ f x)
    (hfr : ∀ x ∈ frontier K, meromorphicOrderAt f x = 0)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγfr : ∀ t ∈ uIcc a b, γ t ∈ frontier K) (hclosed : γ a = γ b)
    (hnull : IsNullHomologous γ a b K)
    (hwind : ∀ x ∈ interior K, windingNumber γ a b x = 1) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t) =
      2 * (Real.pi : ℂ) * Complex.I * (divisorCount f U K : ℂ) := by
  classical
  -- Work on a relatively compact preconnected open thickening of `K` inside `U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let V := thickening δ K
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have hVU : V ⊆ U := (thickening_subset_cthickening δ K).trans hδU
  have hfV : MeromorphicOn f V := hf.mono_set hVU
  have hafr : γ a ∈ frontier K := hγfr a left_mem_uIcc
  have htop (x : ℂ) (hx : x ∈ V) : meromorphicOrderAt f x ≠ ⊤ :=
    hfV.meromorphicOrderAt_ne_top_of_isPreconnected (hK_conn.thickening δ)
      (hKV (hK.isClosed.frontier_subset hafr)) hx (by simp [hfr (γ a) hafr])
  -- Collect both divisor support and isolated representative defects in a single finite set `S`.
  have hfinite : (Function.support (MeromorphicOn.divisor f V)).Finite :=
    (hf.mono_set hδU).divisor_support_finite_of_subset hK.cthickening
      (thickening_subset_cthickening δ K)
  have hdefects := hK.cthickening.finite_sdiff_of_mem_codiscreteWithin
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
      exact hxoff.2 (hdefects.mem_toFinset.mpr ⟨thickening_subset_cthickening δ K hx, ha⟩)
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
        hf.divisor_apply (hKU hx.1), hfV.divisor_apply (hKV hx.1)] using hx.2
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  rw [argumentPrinciple_nullHomologous (S := S) (U := V) (ord := MeromorphicOn.divisor f U)
    isOpen_thickening hoff (fun s _ hsV ↦ hfV s hsV)
    (fun s _ hsV ↦ by
      rw [hf.divisor_apply (hVU hsV), WithTop.coe_untop₀_of_ne_top (htop s hsV)])
    hγ (fun t ht ↦ hKV (hK.isClosed.frontier_subset (hγfr t ht))) hclosed
    (fun t ht hmem ↦ hSfr _ hmem (hγfr t ht))
    (isNullHomologous_iff.2 fun w hw ↦ isNullHomologous_iff.1 hnull w fun hwK ↦ hw (hKV hwK))]
  congr 1
  rw [hcount, Int.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  split_ifs with hsK
  · have hsint : s ∈ interior K := by
      rw [← self_sdiff_frontier]
      exact ⟨hsK, hSfr s hs⟩
    rw [hwind s hsint, one_mul]
  · rw [isNullHomologous_iff.1 hnull s hsK, zero_mul]

end TauCeti.Contour
