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
around a closed rectangle as `2πi` times its signed divisor count. Meromorphy on any
set containing the rectangle and order zero on its frontier suffice; neither openness
of that set nor analyticity of the chosen representative on the frontier is required.

The proof fills isolated representative defects on a compact neighbourhood of the rectangle.
The original logarithmic derivative agrees with that of the normal form codiscretely on the
frontier, so their derivative-weighted boundary integrals agree even when the rectangle has
collapsed edges. Divisors are compared only on the rectangle, keeping the original ambient
domain in the count.

`TauCeti.Contour.argumentPrinciple_rectBoundary_zeroCount` gives the corresponding natural
zero count when the rectangle contains no negative divisor values.
-/

public section

open Set Complex Metric
open scoped Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}

open scoped Classical in
/-- Finite exceptional data for the canonical representative, including the exact
finite-sum interpretation of its divisor count. -/
private theorem rectangle_normalForm_exceptional_data {F : ℂ → ℂ} {V : Set ℂ}
    (hRV : Rectangle z w ⊆ V) (hV : IsPreconnected V) (hNF : MeromorphicNFOn F V)
    (hfinite : (Function.support (MeromorphicOn.divisor F V)).Finite)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt F x = 0) :
    ∃ S : Finset ℂ,
      (∀ x ∈ V, x ∉ S → AnalyticAt ℂ F x ∧ F x ≠ 0) ∧
      (∀ s ∈ S, s ∈ V → meromorphicOrderAt F s =
        (MeromorphicOn.divisor F V s : WithTop ℤ)) ∧
      (∀ s ∈ S, s ∉ frontier (Rectangle z w)) ∧
      divisorCount F V (Rectangle z w) =
        ∑ s ∈ S with s ∈ Rectangle z w, MeromorphicOn.divisor F V s := by
  classical
  have hfV : MeromorphicOn F V := hNF.meromorphicOn
  have hzfr : z ∈ frontier (Rectangle z w) := by simp [frontier_rectangle, mem_reProdIm]
  have hzV : z ∈ V := hRV (by simp [Rectangle, mem_reProdIm])
  have htop (x : ℂ) (hx : x ∈ V) : meromorphicOrderAt F x ≠ ⊤ :=
    hfV.meromorphicOrderAt_ne_top_of_isPreconnected hV hzV hx (by simp [hfr z hzfr])
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
    exact hd (by rw [hfV.divisor_apply (hRV ((isClosed_rectangle z w).frontier_subset hxfr))]
                 simp [hfr x hxfr])
  · rw [divisorCount_def]
    apply finsum_mem_eq_sum_of_subset
    · intro x hx
      exact Finset.mem_filter.mpr ⟨by simpa [S, Function.mem_support] using hx.2, hx.1⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2

/-- The integral of the logarithmic derivative around a rectangle is `2πi` times its signed
divisor count. The ambient meromorphic set need not be open or connected; isolated changes
of representative values on the frontier are allowed. The rectangle may be degenerate. -/
theorem argumentPrinciple_rectBoundary_divisor (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hRU : Rectangle z w ⊆ U) (hf : MeromorphicOn f U)
    (hfr : ∀ x ∈ frontier (Rectangle z w), meromorphicOrderAt f x = 0) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • logDeriv f (rectBoundary z w t) =
      2 * π * I * (divisorCount f U (Rectangle z w) : ℂ) := by
  classical
  have hopen : IsOpen {x : ℂ | MeromorphicAt f x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hnear := eventually_nhdsWithin_iff.mp
      (hx.eventually_analyticAt.mono fun _ hy ↦ hy.meromorphicAt)
    filter_upwards [hnear] with y hy
    by_cases h : y = x
    · simpa only [mem_ofPred_eq, h] using hx
    · exact hy h
  have hcompact : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨δ, hδ, hδM⟩ := hcompact.exists_cthickening_subset_open hopen (fun x hx ↦ hf x (hRU hx))
  let W := cthickening δ (Rectangle z w)
  let V := thickening δ (Rectangle z w)
  let F := toMeromorphicNFOn f W
  have hfW : MeromorphicOn f W := fun x hx ↦ hδM hx
  have hNF : MeromorphicNFOn F W := meromorphicNFOn_toMeromorphicNFOn f W
  have hVW : V ⊆ W := thickening_subset_cthickening δ _
  have hRV : Rectangle z w ⊆ V := self_subset_thickening hδ _
  have horder (x : ℂ) (hx : x ∈ Rectangle z w) :
      meromorphicOrderAt F x = meromorphicOrderAt f x :=
    meromorphicOrderAt_toMeromorphicNFOn hfW (hVW (hRV hx))
  have hNFV : MeromorphicNFOn F V := fun _ hx ↦ hNF (hVW hx)
  obtain ⟨S, hoff, hord, hSfr, hcount⟩ := rectangle_normalForm_exceptional_data hRV
    ((convex_rectangle z w).thickening δ).isPreconnected hNFV
    (hNF.meromorphicOn.divisor_support_finite_of_subset hcompact.cthickening hVW)
    (fun x hx ↦ (horder x ((isClosed_rectangle z w).frontier_subset hx)).trans (hfr x hx))
  have heq : f =ᶠ[Filter.codiscreteWithin V] F :=
    (toMeromorphicNFOn_eqOn_codiscrete hfW).filter_mono (Filter.codiscreteWithin_mono hVW)
  have hlog := (logDeriv_congr_codiscreteWithin isOpen_thickening heq).filter_mono
    (Filter.codiscreteWithin_mono ((isClosed_rectangle z w).frontier_subset.trans hRV))
  rw [integral_rectBoundary_congr_codiscreteWithin hlog,
    argumentPrinciple_rectBoundary hre him isOpen_thickening hRV hoff
      (fun x _ hx ↦ hNF.meromorphicOn x (hVW hx)) hord hSfr, ← Int.cast_sum, ← hcount]
  congr 2
  rw [divisorCount_def, divisorCount_def]
  exact finsum_congr fun x ↦ finsum_congr fun hx ↦ by
    rw [hNFV.meromorphicOn.divisor_apply (hRV hx), hf.divisor_apply (hRU hx), horder x hx]

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
