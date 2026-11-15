/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.TruncatedSector
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.Conformal.ArgumentPrinciple
import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.Contour.Winding.Number.Translate

/-!
# Winding numbers of the boundary of a truncated sector

This file evaluates the generalized winding number `TauCeti.Contour.windingNumber` of the closed
truncated-sector boundary `Complex.truncatedSectorBoundary z₀ r R θ₁ θ₂` on `[0, 4]`:

* about a point outside the closed truncated sector `Complex.closedTruncatedSector z₀ r R θ₁ θ₂`
  (with `r ≤ R` and `θ₁ ≤ θ₂`) it is `0`
  (`TauCeti.Contour.windingNumber_truncatedSectorBoundary_eq_zero`);
* consequently, the boundary is null-homologous in every set containing the closed truncated sector
  (`TauCeti.Contour.isNullHomologous_truncatedSectorBoundary`);
* about a point of the open truncated sector `Complex.openTruncatedSector z₀ r R θ₁ θ₂` (with
  `0 ≤ r` and `θ₂ - θ₁ < 2π`) it is `1`
  (`TauCeti.Contour.windingNumber_truncatedSectorBoundary_eq_one`). Both genuinely truncated sectors
  (`0 < r`) and full sectors (`r = 0`) are covered.

The exterior value is obtained by contracting `(R, θ₂)` to `(r, θ₁)` inside `Icc r R ×ˢ Icc θ₁ θ₂`
via `TauCeti.Contour.windingNumber_eq_of_continuousOn_uncurry`. For the interior value at
`p = circleMap z₀ ρ₀ φ₀` with `r < ρ₀ < R` and `θ₁ < φ₀ < θ₂`, one first pushes the inner radius up
to `r' = (r + ρ₀) / 2 > 0` without crossing `p`, then deforms the linear radial parametrization to
the exponential parametrization `t ↦ z₀ + exp (rectBoundary u₁ v₁ t)` along the frontier of the
truncated sector, and finally evaluates the resulting image winding number by the geometric argument
principle (`TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd`) on a horizontal strip of
height less than `2π`, where `w ↦ z₀ + exp w - p` has a single simple zero at `log ρ₀ + φ₀ * I`
enclosed once by `rectBoundary u₁ v₁`.
-/

public section

open Set Complex

namespace TauCeti.Contour

variable {z₀ p : ℂ} {r R θ₁ θ₂ : ℝ}

/-- When both radii and both angles coincide, `truncatedSectorBoundary` is constant. -/
private theorem truncatedSectorBoundary_same (z₀ : ℂ) (r θ t : ℝ) :
    truncatedSectorBoundary z₀ r r θ θ t = circleMap z₀ r θ := by
  obtain ⟨ρ, hρ, φ, hφ, heq⟩ :=
    mem_closedTruncatedSector.1 (truncatedSectorBoundary_mem_closedTruncatedSector le_rfl le_rfl t)
  simp only [Icc_self, mem_singleton_iff] at hρ hφ
  subst ρ φ
  exact heq.symm

/-- **The winding number of `truncatedSectorBoundary` vanishes outside the closed truncated
sector.** Neither `0 ≤ r` nor `θ₂ - θ₁ < 2π` is needed here: the curve contracts inside
`closedTruncatedSector z₀ r R θ₁ θ₂` to the constant curve at `circleMap z₀ r θ₁`. -/
theorem windingNumber_truncatedSectorBoundary_eq_zero (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂)
    (hp : p ∉ closedTruncatedSector z₀ r R θ₁ θ₂) :
    windingNumber (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 p = 0 := by
  have hhom := windingNumber_eq_of_continuousOn_uncurry
    (S := Icc r R ×ˢ Icc θ₁ θ₂)
    (H := fun q : ℝ × ℝ ↦ truncatedSectorBoundary z₀ r q.1 θ₁ q.2)
    (a := 0) (b := 4) (w := p) (p := (R, θ₂)) (q := (r, θ₁))
    (isPreconnected_Icc.prod isPreconnected_Icc)
    (continuous_uncurry_truncatedSectorBoundary.comp
      (f := fun x : (ℝ × ℝ) × ℝ ↦ ((z₀, r, x.1.1, θ₁, x.1.2), x.2)) (by fun_prop)).continuousOn
    (fun q _ ↦ isPiecewiseC1On_truncatedSectorBoundary z₀ r q.1 θ₁ q.2)
    (fun q _ ↦ by simp)
    (fun q hq t _ htp ↦ hp (closedTruncatedSector_mono le_rfl hq.1.2 le_rfl hq.2.2
      (htp ▸ truncatedSectorBoundary_mem_closedTruncatedSector hq.1.1 hq.2.1 t)))
    ⟨right_mem_Icc.2 hrR, right_mem_Icc.2 hθ⟩
    ⟨left_mem_Icc.2 hrR, left_mem_Icc.2 hθ⟩
  have hconst : truncatedSectorBoundary z₀ r r θ₁ θ₁ = fun _ ↦ circleMap z₀ r θ₁ :=
    funext (truncatedSectorBoundary_same z₀ r θ₁)
  rw [hhom, hconst]
  exact windingNumber_const _ _ _ _

/-- **The boundary of a truncated sector is null-homologous in every set containing the closed
truncated sector.** -/
theorem isNullHomologous_truncatedSectorBoundary (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) {U : Set ℂ}
    (hU : closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ U) :
    IsNullHomologous (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 U :=
  isNullHomologous_iff.2 fun _ hw ↦
    windingNumber_truncatedSectorBoundary_eq_zero hrR hθ fun hwS ↦ hw (hU hwS)

/-- Deforming the linear radial parametrization of `truncatedSectorBoundary` (with `0 < r < R`) to
the exponential parametrization `t ↦ z₀ + exp (rectBoundary u₁ v₁ t)` preserves the winding number
about any point `p` off the frontier of `closedTruncatedSector z₀ r R θ₁ θ₂`. -/
private theorem windingNumber_truncatedSectorBoundary_eq_exp_rectBoundary
    (hr : 0 < r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * Real.pi)
    (hp : p ∉ frontier (closedTruncatedSector z₀ r R θ₁ θ₂)) :
    windingNumber (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 p =
      windingNumber
        (fun t ↦ z₀ + exp (rectBoundary ((Real.log r : ℂ) + θ₁ * I) ((Real.log R : ℂ) + θ₂ * I) t))
        0 4 p := by
  have hR_pos : 0 < R := hr.trans_le hrR
  have hlog_le : Real.log r ≤ Real.log R := Real.log_le_log hr hrR
  set u₀ : ℂ := (r : ℂ) + θ₁ * I
  set v₀ : ℂ := (R : ℂ) + θ₂ * I
  set u₁ : ℂ := (Real.log r : ℂ) + θ₁ * I
  set v₁ : ℂ := (Real.log R : ℂ) + θ₂ * I
  let H : ℝ → ℝ → ℂ := fun s t ↦
    circleMap z₀ ((1 - s) * (rectBoundary u₀ v₀ t).re + s * Real.exp (rectBoundary u₁ v₁ t).re)
      (rectBoundary u₀ v₀ t).im
  have h4 : uIcc (0 : ℝ) 4 = Icc 0 4 := uIcc_of_le (by norm_num)
  have hpair : IsPiecewiseC1On (fun t ↦ (rectBoundary u₀ v₀ t, rectBoundary u₁ v₁ t)) 0 4 := by
    have h₁ := (ContinuousLinearMap.inl ℝ ℂ ℂ).contDiff.contDiffOn.comp_isPiecewiseC1On
      (isPiecewiseC1On_rectBoundary u₀ v₀) (mapsTo_univ _ _)
    have h₂ := (ContinuousLinearMap.inr ℝ ℂ ℂ).contDiff.contDiffOn.comp_isPiecewiseC1On
      (isPiecewiseC1On_rectBoundary u₁ v₁) (mapsTo_univ _ _)
    exact (h₁.add h₂).congr fun t _ ↦ by simp
  have hpw (s : ℝ) : IsPiecewiseC1On (H s) 0 4 := by
    let Φ : ℂ × ℂ → ℂ := fun q ↦ circleMap z₀ ((1 - s) * q.1.re + s * Real.exp q.2.re) q.1.im
    have hrad : ContDiff ℝ 1 (fun q : ℂ × ℂ ↦ (1 - s) * q.1.re + s * Real.exp q.2.re) :=
      (contDiff_const.mul (reCLM.contDiff.comp (ContinuousLinearMap.fst ℝ ℂ ℂ).contDiff)).add
        (contDiff_const.mul
          (Real.contDiff_exp.comp (reCLM.contDiff.comp (ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff)))
    have hexp : ContDiff ℝ 1 (fun q : ℂ × ℂ ↦ exp ((q.1.im : ℂ) * I)) :=
      ((contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
        ((ofRealCLM.contDiff.comp
          (imCLM.contDiff.comp (ContinuousLinearMap.fst ℝ ℂ ℂ).contDiff)).mul contDiff_const)
    have hΦ : ContDiff ℝ 1 Φ :=
      contDiff_const.add ((ofRealCLM.contDiff.comp hrad).mul hexp)
    exact hΦ.contDiffOn.comp_isPiecewiseC1On hpair (mapsTo_univ _ _)
  have hcont : Continuous (Function.uncurry H) := by
    have hc₀ : Continuous (fun x : ℝ × ℝ ↦ rectBoundary u₀ v₀ x.2) :=
      (continuous_rectBoundary u₀ v₀).comp continuous_snd
    have hc₁ : Continuous (fun x : ℝ × ℝ ↦ rectBoundary u₁ v₁ x.2) :=
      (continuous_rectBoundary u₁ v₁).comp continuous_snd
    let Ψ : ℝ × ℂ × ℂ → ℂ := fun y ↦
      circleMap z₀ ((1 - y.1) * y.2.1.re + y.1 * Real.exp y.2.2.re) y.2.1.im
    have hΨ : Continuous Ψ := by unfold Ψ circleMap; fun_prop
    exact hΨ.comp (continuous_fst.prodMk (hc₀.prodMk hc₁))
  have hmem_fr {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 4) :
      H s t ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂) := by
    rw [frontier_closedTruncatedSector hr.le hrR hθ hspan]
    have hre₀ : (rectBoundary u₀ v₀ t).re ∈ Icc r R := by
      have hm := rectBoundary_mem_rectangle (z := u₀) (w := v₀) t
      rw [mem_rectangle_iff (by simpa [u₀, v₀] using hrR) (by simpa [u₀, v₀] using hθ)] at hm
      simpa [u₀, v₀] using hm.1
    have hexp₁ : Real.exp (rectBoundary u₁ v₁ t).re ∈ Icc r R := by
      have hm := rectBoundary_mem_rectangle (z := u₁) (w := v₁) t
      rw [mem_rectangle_iff (by simpa [u₁, v₁] using hlog_le) (by simpa [u₁, v₁] using hθ)] at hm
      have hre₁ : (rectBoundary u₁ v₁ t).re ∈ Icc (Real.log r) (Real.log R) := by
        simpa [u₁, v₁] using hm.1
      exact ⟨Real.exp_log hr ▸ Real.exp_le_exp.2 hre₁.1,
        Real.exp_log hR_pos ▸ Real.exp_le_exp.2 hre₁.2⟩
    have hconv : (1 - s) * (rectBoundary u₀ v₀ t).re + s * Real.exp (rectBoundary u₁ v₁ t).re ∈
        Icc r R :=
      ⟨by nlinarith [hs.1, hs.2, hre₀.1, hexp₁.1], by nlinarith [hs.1, hs.2, hre₀.2, hexp₁.2]⟩
    refine ⟨(_, _), ?_, rfl⟩
    rcases le_total t 1 with h1 | h1
    · have him : (rectBoundary u₀ v₀ t).im = θ₁ := by
        rw [rectBoundary_of_mem_Icc_zero_one ⟨ht.1, h1⟩]; simp [u₀]
      exact Or.inl ⟨hconv, by simp [him]⟩
    rcases le_total t 2 with h2 | h2
    · have hr₀ : (rectBoundary u₀ v₀ t).re = R := by
        rw [rectBoundary_of_mem_Icc_one_two ⟨h1, h2⟩]; simp [v₀]
      have hr₁ : Real.exp (rectBoundary u₁ v₁ t).re = R := by
        rw [rectBoundary_of_mem_Icc_one_two ⟨h1, h2⟩]
        simp [v₁, Real.exp_log hR_pos]
      have him : (rectBoundary u₀ v₀ t).im ∈ Icc θ₁ θ₂ := by
        have hm := rectBoundary_mem_rectangle (z := u₀) (w := v₀) t
        rw [mem_rectangle_iff (by simpa [u₀, v₀] using hrR) (by simpa [u₀, v₀] using hθ)] at hm
        simpa [u₀, v₀] using hm.2
      exact Or.inr ⟨by rw [hr₀, hr₁]; ring_nf; simp, him⟩
    rcases le_total t 3 with h3 | h3
    · have him : (rectBoundary u₀ v₀ t).im = θ₂ := by
        rw [rectBoundary_of_mem_Icc_two_three ⟨h2, h3⟩]; simp [v₀]
      exact Or.inl ⟨hconv, by simp [him]⟩
    · have hr₀ : (rectBoundary u₀ v₀ t).re = r := by
        rw [rectBoundary_of_mem_Icc_three_four ⟨h3, ht.2⟩]; simp [u₀]
      have hr₁ : Real.exp (rectBoundary u₁ v₁ t).re = r := by
        rw [rectBoundary_of_mem_Icc_three_four ⟨h3, ht.2⟩]
        simp [u₁, Real.exp_log hr]
      have him : (rectBoundary u₀ v₀ t).im ∈ Icc θ₁ θ₂ := by
        have hm := rectBoundary_mem_rectangle (z := u₀) (w := v₀) t
        rw [mem_rectangle_iff (by simpa [u₀, v₀] using hrR) (by simpa [u₀, v₀] using hθ)] at hm
        simpa [u₀, v₀] using hm.2
      exact Or.inr ⟨by rw [hr₀, hr₁]; ring_nf; simp, him⟩
  have hhom := windingNumber_eq_of_continuousOn_uncurry
    (S := Icc (0 : ℝ) 1) (H := H) (a := 0) (b := 4) (w := p)
    isPreconnected_Icc hcont.continuousOn (fun s _ ↦ hpw s) (fun s _ ↦ by simp [H])
    (fun s hs t ht hEq ↦ hp (hEq ▸ hmem_fr hs (h4 ▸ ht)))
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have hH0 : H 0 = truncatedSectorBoundary z₀ r R θ₁ θ₂ := by
    funext t
    simp [H, truncatedSectorBoundary_def, u₀, v₀]
  rw [hH0] at hhom
  rw [hhom]
  refine windingNumber_congr_curve fun t _ ↦ ?_
  have him : (rectBoundary u₀ v₀ t).im = (rectBoundary u₁ v₁ t).im :=
    im_rectBoundary_eq_of_im_eq (by simp [u₀, u₁]) (by simp [v₀, v₁]) t
  simp only [H, sub_self, zero_mul, one_mul, zero_add, him, circleMap, ofReal_exp, ← exp_add,
    re_add_im]

/-- **The boundary of a truncated sector winds once around every point of the open truncated
sector.** Both genuinely truncated sectors (`0 < r`) and full sectors (`r = 0`) are covered; the
hypothesis `p ∈ openTruncatedSector z₀ r R θ₁ θ₂` forces `r < R` and `θ₁ < θ₂`, so the boundary is
traversed counterclockwise. -/
theorem windingNumber_truncatedSectorBoundary_eq_one (hr : 0 ≤ r) (hspan : θ₂ - θ₁ < 2 * Real.pi)
    (hp : p ∈ openTruncatedSector z₀ r R θ₁ θ₂) :
    windingNumber (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 p = 1 := by
  obtain ⟨ρ₀, ⟨hrρ₀, hρ₀R⟩, φ₀, ⟨hθ₁φ₀, hφ₀θ₂⟩, hp_eq⟩ := mem_openTruncatedSector.1 hp
  have hθ : θ₁ ≤ θ₂ := (hθ₁φ₀.trans hφ₀θ₂).le
  -- Step 1: increase the inner radius to `r' = (r + ρ₀) / 2 > 0` without crossing `p`.
  set r' : ℝ := (r + ρ₀) / 2 with hr'_def
  have hr'_pos : 0 < r' := by linarith [hr'_def]
  have hrr' : r ≤ r' := by linarith [hr'_def]
  have hr'ρ₀ : r' < ρ₀ := by linarith [hr'_def]
  have hr'R : r' ≤ R := (hr'ρ₀.trans hρ₀R).le
  have hp_not_fr (s : ℝ) (hs : s ∈ Icc r r') :
      p ∉ frontier (closedTruncatedSector z₀ s R θ₁ θ₂) := by
    have hp_open : p ∈ openTruncatedSector z₀ s R θ₁ θ₂ :=
      mem_openTruncatedSector.2 ⟨ρ₀, ⟨hs.2.trans_lt hr'ρ₀, hρ₀R⟩, φ₀, ⟨hθ₁φ₀, hφ₀θ₂⟩, hp_eq⟩
    rw [← interior_closedTruncatedSector (hr.trans hs.1) (hs.2.trans hr'R) hθ hspan] at hp_open
    exact disjoint_left.1 disjoint_interior_frontier hp_open
  have hstep1 : windingNumber (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 p =
      windingNumber (truncatedSectorBoundary z₀ r' R θ₁ θ₂) 0 4 p :=
    windingNumber_eq_of_continuousOn_uncurry
      (S := Icc r r') (H := fun s : ℝ ↦ truncatedSectorBoundary z₀ s R θ₁ θ₂)
      (a := 0) (b := 4) (w := p)
      isPreconnected_Icc
      (continuous_uncurry_truncatedSectorBoundary.comp
        (f := fun x : ℝ × ℝ ↦ ((z₀, x.1, R, θ₁, θ₂), x.2)) (by fun_prop)).continuousOn
      (fun s _ ↦ isPiecewiseC1On_truncatedSectorBoundary z₀ s R θ₁ θ₂)
      (fun s _ ↦ by simp)
      (fun s hs t _ hEq ↦ hp_not_fr s hs
        (hEq ▸ truncatedSectorBoundary_mem_frontier (hr.trans hs.1) (hs.2.trans hr'R) hθ hspan t))
      (left_mem_Icc.2 hrr') (right_mem_Icc.2 hrr')
  -- Step 2: deform to `z₀ + exp (rectBoundary u₁ v₁ t)` on the log-polar rectangle.
  rw [hstep1, windingNumber_truncatedSectorBoundary_eq_exp_rectBoundary hr'_pos hr'R hθ hspan
    (hp_not_fr r' (right_mem_Icc.2 hrr'))]
  -- Step 3: apply the geometric argument principle to `g w = z₀ + exp w - p` on a strip of height
  -- strictly less than `2π`.
  set u₁ : ℂ := (Real.log r' : ℂ) + θ₁ * I
  set v₁ : ℂ := (Real.log R : ℂ) + θ₂ * I
  set w₁ : ℝ → ℂ := rectBoundary u₁ v₁
  set g : ℂ → ℂ := fun w ↦ z₀ + exp w - p
  have htrans : windingNumber (fun t ↦ z₀ + exp (w₁ t)) 0 4 p =
      windingNumber (g ∘ w₁) 0 4 0 := by
    have h := windingNumber_translate (γ := g ∘ w₁) (a := 0) (b := 4) (z₀ := 0) p
    rw [zero_add] at h
    rw [← h]
    exact windingNumber_congr_curve fun t _ ↦ by simp [g]
  rw [htrans]
  have hρ₀_pos : 0 < ρ₀ := hr'_pos.trans hr'ρ₀
  set δ : ℝ := (2 * Real.pi - (θ₂ - θ₁)) / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  let U : Set ℂ := {w : ℂ | w.im ∈ Ioo (θ₁ - δ) (θ₂ + δ)}
  set s₀ : ℂ := (Real.log ρ₀ : ℂ) + φ₀ * I
  have hU_open : IsOpen U := isOpen_Ioo.preimage continuous_im
  have hlog_le : Real.log r' ≤ Real.log R := Real.log_le_log hr'_pos hr'R
  have hRU : Rectangle u₁ v₁ ⊆ U := by
    intro w hw
    rw [mem_rectangle_iff (by simpa [u₁, v₁] using hlog_le) (by simpa [u₁, v₁] using hθ)] at hw
    have him : w.im ∈ Icc θ₁ θ₂ := by simpa [u₁, v₁] using hw.2
    exact mem_ofPred.2 ⟨by linarith [him.1], by linarith [him.2]⟩
  have hg_anal : AnalyticOnNhd ℂ g U := fun w _ ↦
    (analyticAt_const.add analyticAt_cexp).sub analyticAt_const
  have hg_zeros : ∀ w ∈ U, g w = 0 → w ∈ ({s₀} : Finset ℂ) := by
    intro w hw hgw
    obtain ⟨hw₁, hw₂⟩ := mem_ofPred.1 hw
    have hexp_eq : circleMap z₀ (Real.exp w.re) w.im = circleMap z₀ ρ₀ φ₀ := by
      calc
        circleMap z₀ (Real.exp w.re) w.im = z₀ + exp w := by
          simp [circleMap, ofReal_exp, ← exp_add, re_add_im]
        _ = p := sub_eq_zero.1 hgw
        _ = circleMap z₀ ρ₀ φ₀ := hp_eq.symm
    have ⟨hre_eq, him_eq⟩ := eq_and_eq_of_circleMap_eq (Real.exp_pos w.re) hρ₀_pos.le
      (abs_lt.2 ⟨by linarith [hδ_def], by linarith [hδ_def]⟩) hexp_eq
    have hlog_eq : w.re = Real.log ρ₀ := by
      simpa using congrArg Real.log hre_eq
    refine Finset.mem_singleton.2 (Complex.ext ?_ ?_)
    · simp [s₀, hlog_eq]
    · simp [s₀, him_eq]
  have hs₀_open : s₀ ∈ Ioo u₁.re v₁.re ×ℂ Ioo u₁.im v₁.im := by
    refine ⟨?_, ?_⟩
    · simpa [s₀, u₁, v₁] using ⟨Real.log_lt_log hr'_pos hr'ρ₀, Real.log_lt_log hρ₀_pos hρ₀R⟩
    · simpa [s₀, u₁, v₁] using ⟨hθ₁φ₀, hφ₀θ₂⟩
  have hs₀_not_fr : s₀ ∉ frontier (Rectangle u₁ v₁) := by
    have hs₀_int := hs₀_open
    rw [← interior_rectangle (by simpa [u₁, v₁] using hlog_le)
      (by simpa [u₁, v₁] using hθ)] at hs₀_int
    exact disjoint_left.1 disjoint_interior_frontier hs₀_int
  have hw₁_off : ∀ t ∈ uIcc (0 : ℝ) 4, g (w₁ t) ≠ 0 := by
    intro t _ hgt
    have heq : w₁ t = s₀ := Finset.mem_singleton.1
      (hg_zeros (w₁ t) (hRU (rectBoundary_mem_rectangle t)) hgt)
    exact hs₀_not_fr (heq ▸ rectBoundary_mem_frontier t)
  rw [TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd hU_open hg_anal hg_zeros
    (isPiecewiseC1On_rectBoundary u₁ v₁) (fun t _ ↦ hRU (rectBoundary_mem_rectangle t))
    (by simp) hw₁_off (isNullHomologous_rectBoundary hRU),
    Finset.sum_singleton, windingNumber_rectBoundary_eq_one hs₀_open, one_mul]
  have hg_s₀ : g s₀ = 0 := by
    have hexp_s₀ : z₀ + exp s₀ = circleMap z₀ ρ₀ φ₀ := by
      simp [s₀, circleMap, exp_add, ← ofReal_exp, Real.exp_log hρ₀_pos]
    simp [g, hexp_s₀, hp_eq]
  have hderiv_s₀ : deriv g s₀ ≠ 0 := by
    have hd : HasDerivAt g (0 + exp s₀ - 0) s₀ :=
      ((hasDerivAt_const s₀ z₀).add (Complex.hasDerivAt_exp s₀)).sub (hasDerivAt_const s₀ p)
    rw [hd.deriv, zero_add, sub_zero]
    exact Complex.exp_ne_zero s₀
  have hord1 : analyticOrderAt g s₀ = 1 :=
    ((analyticAt_const.add analyticAt_cexp).sub analyticAt_const)
      |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hg_s₀ hderiv_s₀
  simp [analyticOrderNatAt, hord1]

end TauCeti.Contour
