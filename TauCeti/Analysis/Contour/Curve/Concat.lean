/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Reversal and concatenation of piecewise `C¹` curves

The contour-integration layer works with raw curves `γ : ℝ → ℂ` on a parameter interval
`[[a, b]]` (`Contour.IsPiecewiseC1On`) and with the raw contour integral
`∫ t in a..b, deriv γ t • f (γ t)`. This file supplies the two operations on such curves that a
path-independence argument needs: running a curve backwards, and following one curve by another.

* The **reversal** `t ↦ γ (c - t)` of a curve on `[[a, b]]` is a curve on `[[c - a, c - b]]`; its
  contour integral over `a..b` is the contour integral of `γ` over `c - a..c - b`. Taking `c` to be
  the sum of the endpoints of a second interval lets the reversed curve start where another curve
  ends.
* The **concatenation** `t ↦ if t ≤ b then γ t else δ t` of a curve `γ` on `[a, b]` and a curve `δ`
  on `[b, c]` that agree at `b` is piecewise `C¹` on `[a, c]`. The contour integral only sees a
  curve on the open interior of its parameter interval, so it splits as the sum of the contour
  integrals of `γ` and `δ`.

## Main results

* `TauCeti.Contour.IsPiecewiseC1On.comp_const_sub` — reversal preserves piecewise `C¹` regularity.
* `TauCeti.Contour.intervalIntegral_deriv_smul_comp_const_sub` — the contour integral of the
  reversed curve.
* `TauCeti.Contour.IsPiecewiseC1On.if_le` — concatenation preserves piecewise `C¹` regularity.
* `TauCeti.Contour.eqOn_deriv_smul_comp_of_eqOn` — the contour integrand depends on the curve on
  an open parameter interval only through its values there.
* `TauCeti.Contour.intervalIntegral_deriv_smul_congr` — the contour integral depends on the curve
  only through its values on the open parameter interval.
* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_add_of_eqOn` — the contour integral along a
  concatenation is the sum of the contour integrals along its pieces.
-/

public section

namespace TauCeti.Contour

open Set MeasureTheory

variable {γ δ : ℝ → ℂ} {a b c : ℝ}

/-- **Reversal of a piecewise-`C¹` curve.** If `γ` is piecewise `C¹` on `[[a, b]]`, then the
reversed curve `t ↦ γ (c - t)` is piecewise `C¹` on `[[c - a, c - b]]`, with the reflected
breakpoints. -/
theorem IsPiecewiseC1On.comp_const_sub (h : IsPiecewiseC1On γ a b) (c : ℝ) :
    IsPiecewiseC1On (fun t => γ (c - t)) (c - a) (c - b) := by
  obtain ⟨p, hp, hC1⟩ := h.exists_breakpoints
  have hmem : ∀ {t : ℝ}, t ∈ uIcc (c - a) (c - b) → c - t ∈ uIcc a b := fun ht => by
    rwa [← preimage_const_sub_uIcc] at ht
  refine IsPiecewiseC1On.of_breakpoints
    (h.continuousOn.comp (continuous_sub_left c).continuousOn fun _ ht => hmem ht)
    (p.image (c - ·)) ?_ fun d e hde hdisj => ?_
  · intro x hx
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' := hp hy
    rw [min_sub_sub_left, max_sub_sub_left]
    exact ⟨by linarith [hy'.2], by linarith [hy'.1]⟩
  · have hsub : Icc (c - e) (c - d) ⊆ uIcc a b := fun s hs => by
      have hs' : c - s ∈ Icc d e := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simpa using hmem (hde hs')
    have hdisj' : Disjoint (↑p : Set ℝ) (Ioo (c - e) (c - d)) := by
      rw [Set.disjoint_left] at hdisj ⊢
      intro x hxp hx
      exact hdisj (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hxp))
        ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact (hC1 _ _ hsub hdisj').comp (contDiff_const.sub contDiff_id).contDiffOn
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- **The contour integral along a reversed curve.** The contour integral of `t ↦ γ (c - t)` over
`a..b` is the contour integral of `γ` over `c - a..c - b`. In particular, for `c = a + b` the
transformed endpoints are `b` and `a`, in reverse order, so it is
`∫ t in b..a, deriv γ t • f (γ t)`, the negative of the contour integral of `γ` over `a..b`. -/
theorem intervalIntegral_deriv_smul_comp_const_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (γ : ℝ → ℂ) (f : ℂ → E) (a b c : ℝ) :
    ∫ t in a..b, deriv (fun t => γ (c - t)) t • f (γ (c - t)) =
      ∫ t in c - a..c - b, deriv γ t • f (γ t) := by
  simp only [deriv_comp_const_sub, neg_smul, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => deriv γ t • f (γ t)) c,
    intervalIntegral.integral_symm (c - b) (c - a)]

/-- **Concatenation of piecewise-`C¹` curves.** If `γ` is piecewise `C¹` on `[a, b]`, `δ` is
piecewise `C¹` on `[b, c]`, and the two agree at `b`, then the curve following `γ` up to time `b`
and `δ` afterwards is piecewise `C¹` on `[a, c]`. -/
theorem IsPiecewiseC1On.if_le (h₁ : IsPiecewiseC1On γ a b) (h₂ : IsPiecewiseC1On δ b c)
    (hab : a ≤ b) (hbc : b ≤ c) (hb : γ b = δ b) :
    IsPiecewiseC1On (fun t => if t ≤ b then γ t else δ t) a c := by
  classical
  obtain ⟨p₁, -, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, -, hC₂⟩ := h₂.exists_breakpoints
  have hac : a ≤ c := hab.trans hbc
  have hη₁ : EqOn (fun t => if t ≤ b then γ t else δ t) γ (Icc a b) := fun t ht =>
    ite_eq_left ht.2
  have hη₂ : EqOn (fun t => if t ≤ b then γ t else δ t) δ (Icc b c) := fun t ht => by
    rcases ht.1.eq_or_lt with rfl | hlt
    · simp [hb]
    · exact ite_eq_right (not_le.2 hlt)
  refine IsPiecewiseC1On.of_breakpoints ?_ ((p₁ ∪ p₂ ∪ {b}).filter (· ∈ Ioo a c)) ?_
    fun d e hde hdisj => ?_
  · rw [uIcc_of_le hac, ← Icc_union_Icc_eq_Icc hab hbc]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact (uIcc_of_le hab ▸ h₁.continuousOn).congr hη₁
    · exact (uIcc_of_le hbc ▸ h₂.continuousOn).congr hη₂
  · intro x hx
    rw [min_eq_left hac, max_eq_right hac]
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  · rw [uIcc_of_le hac] at hde
    have hIoo : Ioo d e ⊆ Ioo a c := fun x hx =>
      ⟨(hde ⟨le_rfl, (hx.1.trans hx.2).le⟩).1.trans_lt hx.1,
        hx.2.trans_le (hde ⟨(hx.1.trans hx.2).le, le_rfl⟩).2⟩
    have hnot : ∀ x ∈ p₁ ∪ p₂ ∪ {b}, x ∉ Ioo d e := fun x hx hxde =>
      Set.disjoint_left.1 hdisj (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hx, hIoo hxde⟩)) hxde
    have hside : e ≤ b ∨ b ≤ d := by
      by_contra hcon
      push Not at hcon
      exact hnot b (by simp) ⟨hcon.2, hcon.1⟩
    rcases hside with heb | hbd
    · have hsub : Icc d e ⊆ Icc a b := fun t ht => ⟨(hde ht).1, ht.2.trans heb⟩
      refine (hC₁ d e (uIcc_of_le hab ▸ hsub) (Set.disjoint_left.2 fun x hx hxde =>
        hnot x (by simp [Finset.mem_coe.1 hx]) hxde)).congr fun t ht => hη₁ (hsub ht)
    · have hsub : Icc d e ⊆ Icc b c := fun t ht => ⟨hbd.trans ht.1, (hde ht).2⟩
      refine (hC₂ d e (uIcc_of_le hbc ▸ hsub) (Set.disjoint_left.2 fun x hx hxde =>
        hnot x (by simp [Finset.mem_coe.1 hx]) hxde)).congr fun t ht => hη₂ (hsub ht)

/-- **The contour integrand sees only the open parameter interval.** Two curves that agree on the
open interval between `a` and `b` have contour integrands that agree there too, an open set being a
neighbourhood of each of its points. -/
theorem eqOn_deriv_smul_comp_of_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (h : EqOn γ δ (uIoo a b)) :
    EqOn (fun t => deriv γ t • f (γ t)) (fun t => deriv δ t • f (δ t)) (uIoo a b) := fun t ht => by
  simp only [h ht, h.deriv isOpen_Ioo ht]

/-- **The contour integral sees only the open parameter interval.** If two curves agree on the
open interval between `a` and `b`, their contour integrals over `a..b` agree, even though the
integrand involves the derivative of the curve. -/
theorem intervalIntegral_deriv_smul_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (h : EqOn γ δ (uIoo a b)) :
    ∫ t in a..b, deriv γ t • f (γ t) = ∫ t in a..b, deriv δ t • f (δ t) :=
  intervalIntegral.integral_congr_uIoo (eqOn_deriv_smul_comp_of_eqOn h)

/-- **The contour integral along a concatenation.** If `η` agrees with `γ` on the open interval
between `a` and `b` and with `δ` on the open interval between `b` and `c`, and the contour
integrands of `γ` and `δ` are integrable there, then the contour integral of `η` over `a..c` is the
sum of those of `γ` over `a..b` and of `δ` over `b..c`. This applies in particular to the
concatenation `t ↦ if t ≤ b then γ t else δ t` when `a ≤ b ≤ c`. -/
theorem intervalIntegral_deriv_smul_eq_add_of_eqOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {η : ℝ → ℂ} (hγ : EqOn η γ (uIoo a b))
    (hδ : EqOn η δ (uIoo b c))
    (hγi : IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume a b)
    (hδi : IntervalIntegrable (fun t => deriv δ t • f (δ t)) volume b c) :
    ∫ t in a..c, deriv η t • f (η t) =
      (∫ t in a..b, deriv γ t • f (γ t)) + ∫ t in b..c, deriv δ t • f (δ t) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hγi.congr_uIoo (eqOn_deriv_smul_comp_of_eqOn hγ).symm)
      (hδi.congr_uIoo (eqOn_deriv_smul_comp_of_eqOn hδ).symm),
    intervalIntegral_deriv_smul_congr hγ, intervalIntegral_deriv_smul_congr hδ]

end TauCeti.Contour
