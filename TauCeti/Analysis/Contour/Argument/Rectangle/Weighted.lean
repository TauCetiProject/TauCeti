/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Rectangle
public import Mathlib.Analysis.Analytic.Order
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# Weighted argument principle on rectangles

Integrating an analytic weight times a logarithmic derivative on a rectangle gives the weighted
sum of the enclosed zeros, counted with multiplicity. In particular one can shift a truncated
vertical line while keeping the two horizontal integrals explicit.

This is the rectangle counterpart of `TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`.
-/

public section

open Complex Set
open scoped Real Interval

namespace TauCeti.Contour

/-- For an analytic function `f` with no boundary zeros, the right edge integral of `f′/f`
against an analytic weight `g` is the left edge integral plus the horizontal connectors and
`2π` times the weighted sum of the interior zeros with multiplicity. The edge integrals on
vertical lines are parameterized by the real ordinate. -/
theorem intervalIntegral_vertical_logDeriv_mul_eq {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Icc a b ×ℂ Icc u v))
    (hg : AnalyticOnNhd ℂ g (Icc a b ×ℂ Icc u v))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc u v, f z = 0 → z ∈ Ioo a b ×ℂ Ioo u v) :
    (∫ y : ℝ in u..v, logDeriv f (b + y * I) * g (b + y * I)) =
      (∫ y : ℝ in u..v, logDeriv f (a + y * I) * g (a + y * I)) +
      ((∫ x : ℝ in a..b, logDeriv f (x + v * I) * g (x + v * I)) -
       (∫ x : ℝ in a..b, logDeriv f (x + u * I) * g (x + u * I))) / I +
      2 * π * ∑ᶠ z ∈ {z ∈ Icc a b ×ℂ Icc u v | f z = 0},
        (analyticOrderNatAt f z : ℂ) * g z := by
  classical
  let K := Icc a b ×ℂ Icc u v
  let Z := {z ∈ K | f z = 0}
  have hK : IsPreconnected K := by
    have h := (convex_rectangle (a + u * I) (b + v * I)).isPreconnected
    simpa [K, Rectangle, add_re, add_im, mul_re, mul_im, uIcc_of_le, hab, huv] using h
  have hc : (a : ℂ) + u * I ∈ K := by
    simp [K, mem_reProdIm, add_re, add_im, mul_re, mul_im, hab, huv]
  have hne : f (a + u * I) ≠ 0 := by
    intro hz
    simpa [mem_reProdIm, add_re, mul_re] using hzeros _ hc hz
  have hfin : Z.Finite :=
    hf.finite_setOf_mem_and_eq_zero_of_isCompact hK hc hne (isCompact_Icc.reProdIm isCompact_Icc)
      Subset.rfl
  have hP : ∀ z ∈ hfin.toFinset, z ∈ Ioo a b ×ℂ Ioo u v := fun z hz ↦
    hzeros z (hfin.mem_toFinset.mp hz).1 (hfin.mem_toFinset.mp hz).2
  have ha : AnalyticOnNhd ℂ (fun z ↦ logDeriv f z * g z) (K \ hfin.toFinset) := fun z hz ↦
    ((hf z hz.1).logDeriv (fun he ↦ hz.2 (hfin.mem_toFinset.mpr ⟨hz.1, he⟩))).fun_mul (hg z hz.1)
  have hs := intervalIntegral_vertical_eq_uShaped_add_two_pi_mul_sum_residue hab huv hP
    ha.continuousOn (ha.differentiableOn.mono (sdiff_subset_sdiff_left fun z hz ↦
      ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)) (fun z hz ↦
        ((hf z (hfin.mem_toFinset.mp hz).1).meromorphicAt.logDeriv).mul
          (hg z (hfin.mem_toFinset.mp hz).1).meromorphicAt)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine hs.trans ?_
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  have hzk := (hfin.mem_toFinset.mp hz).1
  have hc₀ : analyticOrderAt f (a + u * I) = 0 := (hf _ hc).analyticOrderAt_eq_zero.mpr hne
  have hord := hf.analyticOrderAt_ne_top_of_isPreconnected hK hc hzk (by simp [hc₀])
  exact residue_logDeriv_mul_eq_meromorphicOrderAt (hf z hzk).meromorphicAt
    (by rw [(hf z hzk).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hord]; simp)
    (hg z hzk)

end TauCeti.Contour
