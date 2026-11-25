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
import TauCeti.Analysis.Calculus.Deriv.CountableLevels
import TauCeti.Analysis.Normed.Module.Connected

/-!
# The argument principle against the divisor

`TauCeti.Contour.argumentPrinciple` and `TauCeti.Contour.argumentPrinciple_nullHomologous` ask the
caller for the data of the counting problem: a finite set `S` collecting the nonzero-order points,
an order function `ord`, and proofs that the two agree and that `S` is exhaustive. Mathlib's
`MeromorphicOn.divisor` already packages that data — `MeromorphicOn.divisor_apply` evaluates it to
`(meromorphicOrderAt f z).untop₀`, and local compactness supplies finiteness of the divisor support.
This file restates both the circle and null-homologous argument principles against the divisor API,
so callers that already speak `divisor` or `TauCeti.divisorCount` need not rebuild the finset and
the order function by hand.

Requiring `meromorphicOrderAt f z = 0` on the boundary does double duty:

* It confines the nonzero-order points to the interior, so a divisor taken over the open disc (or
  counted on the compact region `K`) accounts for every such point.
* It rules out order `⊤`. This matters because `(⊤ : WithTop ℤ).untop₀ = 0`, so at a point where `f`
  vanishes identically the divisor reads `0` while the order does not, and the exhaustiveness
  obligation would fail. Because `closedBall c R` is convex (hence preconnected, with nonempty
  sphere for `0 ≤ R`) and a thickening of a preconnected compact set `K` is preconnected (with
  nonempty frontier visited by `γ`), `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`
  propagates the finite order at a boundary point to the whole region.

For `argumentPrinciple_nullHomologous_divisor`, neither openness of the ambient set `U` nor
analyticity of the chosen representative on `frontier K` is required: passing to `toMeromorphicNFOn`
on a compact thickening of `K` fills isolated representative defects, and the original logarithmic
derivative agrees with the normal form's logarithmic derivative codiscretely on `frontier K`. On
the finite set of discrepancies, `Set.Countable.ae_deriv_eq_zero_on_preimage` ensures that
`deriv γ` vanishes almost everywhere, so the derivative-weighted boundary integrals agree without
any regularity or non-degeneracy assumptions on `γ` beyond absolute continuity.

## Main results

* `TauCeti.Contour.argumentPrinciple_divisor` —
  `∮_{C(c,R)} logDeriv f = 2πi · ∑ᶠ z, divisor f (ball c R) z`, the circle argument principle with
  the counting data taken from `MeromorphicOn.divisor`.
* `TauCeti.Contour.argumentPrinciple_nullHomologous_divisor` —
  `∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · divisorCount f U K` for a closed absolutely
  continuous curve `γ` on `frontier K` that is null-homologous in a compact preconnected set
  `K ⊆ U` and winds once around every point of `interior K`.

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

open scoped Classical in
/-- Finite exceptional data for a meromorphic normal form on a preconnected neighbourhood of a
closed set `K`, together with the finite-sum expression for its divisor count on `K`. -/
private theorem normalForm_exceptional_data {F : ℂ → ℂ} {K V : Set ℂ} {p : ℂ}
    (hK : IsClosed K) (hKV : K ⊆ V) (hV : IsPreconnected V) (hNF : MeromorphicNFOn F V)
    (hfinite : (Function.support (MeromorphicOn.divisor F V)).Finite)
    (hpfr : p ∈ frontier K) (hfr : ∀ x ∈ frontier K, meromorphicOrderAt F x = 0) :
    ∃ S : Finset ℂ,
      (∀ x ∈ V, x ∉ S → AnalyticAt ℂ F x ∧ F x ≠ 0) ∧
      (∀ s ∈ S, s ∈ V → meromorphicOrderAt F s =
        (MeromorphicOn.divisor F V s : WithTop ℤ)) ∧
      (∀ s ∈ S, s ∉ frontier K) ∧
      divisorCount F V K = ∑ s ∈ S with s ∈ K, MeromorphicOn.divisor F V s := by
  classical
  have hfV : MeromorphicOn F V := hNF.meromorphicOn
  have hpV : p ∈ V := hKV (hK.frontier_subset hpfr)
  have htop (x : ℂ) (hx : x ∈ V) : meromorphicOrderAt F x ≠ ⊤ :=
    hfV.meromorphicOrderAt_ne_top_of_isPreconnected hV hpV hx (by simp [hfr p hpfr])
  let S := hfinite.toFinset
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro x hx hxS
    have hd : MeromorphicOn.divisor F V x = 0 := by
      simpa [S, Function.mem_support] using hxS
    have ho : meromorphicOrderAt F x = 0 := by
      rw [hfV.divisor_apply hx, WithTop.untop₀_eq_zero] at hd
      exact hd.resolve_right (htop x hx)
    exact ⟨(hNF hx).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by simp [ho]),
      (hNF hx).meromorphicOrderAt_eq_zero_iff.mp ho⟩
  · intro x _ hx
    rw [hfV.divisor_apply hx, WithTop.coe_untop₀_of_ne_top (htop x hx)]
  · intro x hx hxfr
    have hd : MeromorphicOn.divisor F V x ≠ 0 := by simpa [S, Function.mem_support] using hx
    exact hd (by
      rw [hfV.divisor_apply (hKV (hK.frontier_subset hxfr))]
      simp [hfr x hxfr])
  · rw [divisorCount_def]
    apply finsum_mem_eq_sum_of_subset
    · intro x hx
      exact Finset.mem_filter.mpr ⟨by simpa [S, Function.mem_support] using hx.2, hx.1⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2

/-- **The argument principle against the divisor on a compact preconnected region.** Let `K` be a
compact preconnected set contained in a set `U`, let `f` be meromorphic on `U` with meromorphic
order `0` on `frontier K`, and let `γ` be a closed absolutely continuous curve on `[[a, b]]`
tracing points of `frontier K`, null-homologous in `K`, and winding once around every point of
`interior K`. Then the contour integral of `logDeriv f` along `γ` is `2πi` times
`divisorCount f U K`.

The ambient meromorphic set `U` need not be open, connected, or bounded, and isolated changes of
representative values on or off `frontier K` are allowed. -/
theorem argumentPrinciple_nullHomologous_divisor {f : ℂ → ℂ} {U K : Set ℂ}
    (hK : IsCompact K) (hK_conn : IsPreconnected K)
    (hKU : K ⊆ U) (hf : MeromorphicOn f U)
    (hfr : ∀ x ∈ frontier K, meromorphicOrderAt f x = 0)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγfr : ∀ t ∈ uIcc a b, γ t ∈ frontier K) (hclosed : γ a = γ b)
    (hnull : IsNullHomologous γ a b K)
    (hwind : ∀ x ∈ interior K, windingNumber γ a b x = 1) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t) =
      2 * (Real.pi : ℂ) * Complex.I * (divisorCount f U K : ℂ) := by
  classical
  have hopen : IsOpen {x : ℂ | MeromorphicAt f x} := isOpen_iff_mem_nhds.mpr fun x hx ↦
    (eventually_nhdsWithin_iff.mp <|
      hx.eventually_analyticAt.mono fun _ ↦ AnalyticAt.meromorphicAt).mono fun y hy ↦
        (eq_or_ne y x).elim (· ▸ hx) hy
  obtain ⟨δ, hδ, hδM⟩ := hK.exists_cthickening_subset_open hopen (fun x hx ↦ hf x (hKU hx))
  let W := cthickening δ K
  let V := thickening δ K
  let F := toMeromorphicNFOn f W
  have hfW : MeromorphicOn f W := fun _ hx ↦ hδM hx
  have hNF : MeromorphicNFOn F W := meromorphicNFOn_toMeromorphicNFOn f W
  have hVW : V ⊆ W := thickening_subset_cthickening δ K
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have horder (x : ℂ) (hx : x ∈ K) : meromorphicOrderAt F x = meromorphicOrderAt f x :=
    meromorphicOrderAt_toMeromorphicNFOn hfW (hVW (hKV hx))
  have hNFV : MeromorphicNFOn F V := fun _ hx ↦ hNF (hVW hx)
  obtain ⟨S, hoff, hord, hSfr, hcount⟩ := normalForm_exceptional_data hK.isClosed hKV
    (hK_conn.thickening δ) hNFV
    (hNF.meromorphicOn.divisor_support_finite_of_subset hK.cthickening hVW)
    (hγfr a left_mem_uIcc)
    (fun x hx ↦ (horder x (hK.isClosed.frontier_subset hx)).trans (hfr x hx))
  have hlog := (logDeriv_congr_codiscreteWithin isOpen_thickening <|
    (toMeromorphicNFOn_eqOn_codiscrete hfW).filter_mono
      (Filter.codiscreteWithin_mono hVW)).filter_mono
    (Filter.codiscreteWithin_mono (hK.isClosed.frontier_subset.trans hKV))
  have hbad := ((hK.of_isClosed_subset isClosed_frontier
    hK.isClosed.frontier_subset).finite_sdiff_of_mem_codiscreteWithin hlog).countable
  have hint : (∫ t in a..b, deriv γ t • logDeriv f (γ t)) =
      ∫ t in a..b, deriv γ t • logDeriv F (γ t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hbad.ae_deriv_eq_zero_on_preimage γ MeasureTheory.volume] with t ht hmem
    by_cases h : logDeriv f (γ t) = logDeriv F (γ t)
    · rw [h]
    · simp [ht ⟨hγfr t (uIoc_subset_uIcc hmem), h⟩]
  rw [hint, argumentPrinciple_nullHomologous (S := S) (U := V) (ord := MeromorphicOn.divisor F V)
    isOpen_thickening hoff (fun s _ hsV ↦ hNFV.meromorphicOn s hsV) hord hγ
    (fun t ht ↦ hKV (hK.isClosed.frontier_subset (hγfr t ht))) hclosed
    (fun t ht hmem ↦ hSfr _ hmem (hγfr t ht))
    (isNullHomologous_iff.2 fun w hw ↦ isNullHomologous_iff.1 hnull w fun hwK ↦ hw (hKV hwK))]
  congr 1
  trans (divisorCount F V K : ℂ)
  · rw [hcount, Int.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    split_ifs with hsK
    · rw [hwind s (self_sdiff_frontier (s := K) ▸ ⟨hsK, hSfr s hs⟩), one_mul]
    · rw [isNullHomologous_iff.1 hnull s hsK, zero_mul]
  · congr 1
    rw [divisorCount_def, divisorCount_def]
    exact finsum_congr fun x ↦ finsum_congr fun hx ↦ by
      rw [hNFV.meromorphicOn.divisor_apply (hKV hx), hf.divisor_apply (hKU hx), horder x hx]

end TauCeti.Contour
