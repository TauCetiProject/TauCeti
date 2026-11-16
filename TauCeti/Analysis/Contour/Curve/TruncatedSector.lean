/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.TruncatedSector
public import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Curve.Circle.Basic
import TauCeti.Analysis.Contour.Curve.Concat
import TauCeti.Analysis.Contour.Curve.Integrability
import TauCeti.Analysis.Contour.Curve.Reparam
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The boundary of a truncated sector as a closed piecewise-`C¹` curve

For a centre `z₀ : ℂ`, radii `r, R : ℝ` and angles `θ₁, θ₂ : ℝ`, this file parametrizes the
boundary of `Complex.closedTruncatedSector z₀ r R θ₁ θ₂` as a closed `4`-periodic piecewise-`C¹`
curve `Complex.truncatedSectorBoundary z₀ r R θ₁ θ₂` on `[0, 4]`. It is obtained by pushing the
parameter-rectangle boundary `Complex.rectBoundary (r + θ₁ * I) (R + θ₂ * I)` forward along the
smooth polar map `w ↦ circleMap z₀ w.re w.im`:

* on `[0, 1]` it runs radially from `circleMap z₀ r θ₁` to `circleMap z₀ R θ₁` along angle `θ₁`;
* on `[1, 2]` it runs along the outer circular arc of radius `R` from `θ₁` to `θ₂`;
* on `[2, 3]` it runs radially back from `circleMap z₀ R θ₂` to `circleMap z₀ r θ₂` along angle
  `θ₂`;
* on `[3, 4]` it runs along the inner circular arc of radius `r` from `θ₂` back to `θ₁` (collapsing
  to the constant vertex `z₀` when `r = 0`).

When `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, the orientation is counterclockwise and the trace over
`[0, 4]` is `frontier (closedTruncatedSector z₀ r R θ₁ θ₂)`. For any continuous integrand on the
trace, the contour integral along `[0, 4]` decomposes into the difference of the two radial ray
integrals over `r..R` plus the difference of the two circular-arc integrals over `θ₁..θ₂`.

## Main definitions

* `Complex.truncatedSectorBoundary z₀ r R θ₁ θ₂`: the closed `4`-periodic boundary curve on
  `[0, 4]`.

## Main results

* `Complex.truncatedSectorBoundary_of_mem_Icc_zero_one` and its three companions: explicit formulas
  on the four unit cells `[0, 1]`, `[1, 2]`, `[2, 3]`, `[3, 4]`.
* `Complex.isPiecewiseC1On_truncatedSectorBoundary`: piecewise-`C¹` regularity on `[0, 4]`.
* `Complex.continuous_uncurry_truncatedSectorBoundary`: joint continuity in the sector parameters
  and the curve parameter.
* `Complex.image_truncatedSectorBoundary`: for `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, the trace over
  `[0, 4]` is `frontier (closedTruncatedSector z₀ r R θ₁ θ₂)`.
* `Complex.integral_truncatedSectorBoundary`: contour-integral decomposition into two radial
  integrals and two circular-arc integrals.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Complex

/-- The boundary of `closedTruncatedSector z₀ r R θ₁ θ₂` as a closed `4`-periodic curve on
`[0, 4]`, defined as the polar image of `rectBoundary (r + θ₁ * I) (R + θ₂ * I)`. For
`0 ≤ r ≤ R` and `θ₁ ≤ θ₂` it traverses the outgoing ray at `θ₁`, the outer arc at `R`, the incoming
ray at `θ₂`, and the inner arc at `r` in counterclockwise order. -/
def truncatedSectorBoundary (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) (t : ℝ) : ℂ :=
  let w := rectBoundary ((r : ℂ) + θ₁ * I) ((R : ℂ) + θ₂ * I) t
  circleMap z₀ w.re w.im

/-- `Complex.truncatedSectorBoundary` unfolded to its polar-rectangle definition. -/
theorem truncatedSectorBoundary_def (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) (t : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t =
      circleMap z₀ (rectBoundary ((r : ℂ) + θ₁ * I) ((R : ℂ) + θ₂ * I) t).re
        (rectBoundary ((r : ℂ) + θ₁ * I) ((R : ℂ) + θ₂ * I) t).im := (rfl)

variable {z₀ : ℂ} {r R θ₁ θ₂ : ℝ}

/-- At `t = 0` the truncated-sector boundary starts at `circleMap z₀ r θ₁`. -/
@[simp]
theorem truncatedSectorBoundary_zero (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ 0 = circleMap z₀ r θ₁ := by
  simp [truncatedSectorBoundary]

/-- At `t = 1` the truncated-sector boundary reaches `circleMap z₀ R θ₁`. -/
@[simp]
theorem truncatedSectorBoundary_one (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ 1 = circleMap z₀ R θ₁ := by
  simp [truncatedSectorBoundary]

/-- At `t = 2` the truncated-sector boundary reaches `circleMap z₀ R θ₂`. -/
@[simp]
theorem truncatedSectorBoundary_two (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ 2 = circleMap z₀ R θ₂ := by
  simp [truncatedSectorBoundary]

/-- At `t = 3` the truncated-sector boundary reaches `circleMap z₀ r θ₂`. -/
@[simp]
theorem truncatedSectorBoundary_three (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ 3 = circleMap z₀ r θ₂ := by
  simp [truncatedSectorBoundary]

/-- The truncated-sector boundary has period `4`. -/
theorem periodic_truncatedSectorBoundary (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    Function.Periodic (truncatedSectorBoundary z₀ r R θ₁ θ₂) 4 := fun t ↦ by
  simp only [truncatedSectorBoundary_def, periodic_rectBoundary _ _ t]

/-- The truncated-sector boundary is closed: at `t = 4` it returns to `circleMap z₀ r θ₁`. -/
@[simp]
theorem truncatedSectorBoundary_four (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ 4 = circleMap z₀ r θ₁ := by
  simpa using periodic_truncatedSectorBoundary z₀ r R θ₁ θ₂ 0

/-- On `[0, 1]` the truncated-sector boundary runs radially from `r` to `R` along angle `θ₁`. -/
theorem truncatedSectorBoundary_of_mem_Icc_zero_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t = circleMap z₀ (r + t * (R - r)) θ₁ := by
  rw [truncatedSectorBoundary_def, rectBoundary_of_mem_Icc_zero_one ht]
  simp

/-- On `[1, 2]` the truncated-sector boundary runs along the outer circular arc of radius `R` from
`θ₁` to `θ₂`. -/
theorem truncatedSectorBoundary_of_mem_Icc_one_two {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t = circleMap z₀ R (θ₁ + (t - 1) * (θ₂ - θ₁)) := by
  rw [truncatedSectorBoundary_def, rectBoundary_of_mem_Icc_one_two ht]
  simp

/-- On `[2, 3]` the truncated-sector boundary runs radially from `R` to `r` along angle `θ₂`. -/
theorem truncatedSectorBoundary_of_mem_Icc_two_three {t : ℝ} (ht : t ∈ Icc (2 : ℝ) 3) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t = circleMap z₀ (R + (t - 2) * (r - R)) θ₂ := by
  rw [truncatedSectorBoundary_def, rectBoundary_of_mem_Icc_two_three ht]
  simp

/-- On `[3, 4]` the truncated-sector boundary runs along the inner circular arc of radius `r` from
`θ₂` back to `θ₁`. -/
theorem truncatedSectorBoundary_of_mem_Icc_three_four {t : ℝ} (ht : t ∈ Icc (3 : ℝ) 4) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t = circleMap z₀ r (θ₂ + (t - 3) * (θ₁ - θ₂)) := by
  rw [truncatedSectorBoundary_def, rectBoundary_of_mem_Icc_three_four ht]
  simp

/-! ### Piecewise-`C¹` regularity and joint parameter continuity -/

/-- The truncated-sector boundary is piecewise `C¹` on `[0, 4]`. -/
theorem isPiecewiseC1On_truncatedSectorBoundary (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    TauCeti.IsPiecewiseC1On (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 :=
  ((TauCeti.contDiff_uncurry_circleMap z₀ (n := 1)).comp
    (reCLM.contDiff.prodMk imCLM.contDiff)).contDiffOn.comp_isPiecewiseC1On
    (isPiecewiseC1On_rectBoundary _ _) (mapsTo_univ _ _)

/-- `truncatedSectorBoundary` is jointly continuous in `(z₀, r, R, θ₁, θ₂)` and `t : ℝ`. -/
theorem continuous_uncurry_truncatedSectorBoundary :
    Continuous
      (fun p : (ℂ × ℝ × ℝ × ℝ × ℝ) × ℝ ↦
        truncatedSectorBoundary p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) := by
  have hrect : Continuous
      (fun p : (ℂ × ℝ × ℝ × ℝ × ℝ) × ℝ ↦
        rectBoundary ((p.1.2.1 : ℂ) + p.1.2.2.2.1 * I) ((p.1.2.2.1 : ℂ) + p.1.2.2.2.2 * I) p.2) :=
    continuous_uncurry_rectBoundary.comp
      (f := fun p : (ℂ × ℝ × ℝ × ℝ × ℝ) × ℝ ↦
        ((((p.1.2.1 : ℂ) + p.1.2.2.2.1 * I), ((p.1.2.2.1 : ℂ) + p.1.2.2.2.2 * I)), p.2))
      (by fun_prop)
  have hpolar : Continuous (fun q : ℂ × ℂ ↦ circleMap q.1 q.2.re q.2.im) := by
    unfold circleMap
    fun_prop
  exact hpolar.comp ((continuous_fst.comp continuous_fst).prodMk hrect)

/-- The truncated-sector boundary `truncatedSectorBoundary z₀ r R θ₁ θ₂` is continuous on `ℝ`. -/
theorem continuous_truncatedSectorBoundary (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    Continuous (truncatedSectorBoundary z₀ r R θ₁ θ₂) :=
  continuous_uncurry_truncatedSectorBoundary.comp
    (f := fun t : ℝ ↦ ((z₀, r, R, θ₁, θ₂), t)) (by fun_prop)

/-! ### Trace and membership in the frontier and closed truncated sector -/

/-- The trace of `truncatedSectorBoundary z₀ r R θ₁ θ₂` over `[0, 4]` is the polar image of the
four edges of the parameter rectangle `[[r, R]] × [[θ₁, θ₂]]`, without any ordering or
non-wrapping assumption on the parameters. -/
theorem image_truncatedSectorBoundary_eq_union (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ '' Icc 0 4 =
      Function.uncurry (circleMap z₀) '' (([[r, R]] ×ˢ {θ₁, θ₂}) ∪ ({r, R} ×ˢ [[θ₁, θ₂]])) := by
  have hcomp : truncatedSectorBoundary z₀ r R θ₁ θ₂ '' Icc 0 4 =
      (fun w : ℂ ↦ circleMap z₀ w.re w.im) ''
        (rectBoundary ((r : ℂ) + θ₁ * I) ((R : ℂ) + θ₂ * I) '' Icc 0 4) :=
    (image_image (fun w : ℂ ↦ circleMap z₀ w.re w.im)
      (rectBoundary ((r : ℂ) + θ₁ * I) ((R : ℂ) + θ₂ * I)) (Icc 0 4)).symm
  rw [hcomp, image_rectBoundary, frontier_rectangle]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  ext p
  simp only [mem_image, Prod.exists, Function.uncurry_apply_pair]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.re, w.im, ?_, rfl⟩
    simpa [mem_reProdIm] using hw
  · rintro ⟨ρ, φ, hρφ, rfl⟩
    refine ⟨(ρ : ℂ) + φ * I, ?_, by simp⟩
    simpa [mem_reProdIm] using hρφ

/-- For `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, the trace of `truncatedSectorBoundary` over `[0, 4]`
is the frontier of `closedTruncatedSector z₀ r R θ₁ θ₂`. -/
theorem image_truncatedSectorBoundary (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂)
    (hspan : θ₂ - θ₁ < 2 * Real.pi) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ '' Icc 0 4 =
      frontier (closedTruncatedSector z₀ r R θ₁ θ₂) := by
  rw [image_truncatedSectorBoundary_eq_union, frontier_closedTruncatedSector hr hrR hθ hspan,
    uIcc_of_le hrR, uIcc_of_le hθ]

/-- For `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, every value of `truncatedSectorBoundary` lies on the
frontier of `closedTruncatedSector z₀ r R θ₁ θ₂`. -/
theorem truncatedSectorBoundary_mem_frontier (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂)
    (hspan : θ₂ - θ₁ < 2 * Real.pi) (t : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t ∈ frontier (closedTruncatedSector z₀ r R θ₁ θ₂) := by
  obtain ⟨s, hs, hts⟩ := (periodic_truncatedSectorBoundary z₀ r R θ₁ θ₂).exists_mem_Ico₀
    (by norm_num) t
  rw [hts, ← image_truncatedSectorBoundary hr hrR hθ hspan]
  exact mem_image_of_mem _ (Ico_subset_Icc_self hs)

/-- Whenever `r ≤ R` and `θ₁ ≤ θ₂`, every value of `truncatedSectorBoundary` lies in
`closedTruncatedSector z₀ r R θ₁ θ₂` (even if `r < 0` or `θ₂ - θ₁ ≥ 2π`). -/
theorem truncatedSectorBoundary_mem_closedTruncatedSector (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) (t : ℝ) :
    truncatedSectorBoundary z₀ r R θ₁ θ₂ t ∈ closedTruncatedSector z₀ r R θ₁ θ₂ := by
  have hw := rectBoundary_mem_rectangle (z := (r : ℂ) + θ₁ * I) (w := (R : ℂ) + θ₂ * I) t
  rw [mem_rectangle_iff (by simpa using hrR) (by simpa using hθ)] at hw
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hw
  exact circleMap_mem_closedTruncatedSector hw.1 hw.2

/-! ### Decomposition of the contour integral into ray and arc integrals -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The contour integral along `truncatedSectorBoundary`** of a function continuous on its trace
over `[0, 4]` is the signed sum of its two radial integrals over `r..R` (at angles `θ₁` and `θ₂`)
and its two circular-arc integrals over `θ₁..θ₂` (at radii `R` and `r`). No ordering or positivity
assumption on `r, R, θ₁, θ₂` is required. -/
theorem integral_truncatedSectorBoundary {f : ℂ → E}
    (hf : ContinuousOn f (truncatedSectorBoundary z₀ r R θ₁ θ₂ '' Icc 0 4)) :
    ∫ t in (0 : ℝ)..4,
        deriv (truncatedSectorBoundary z₀ r R θ₁ θ₂) t •
          f (truncatedSectorBoundary z₀ r R θ₁ θ₂ t) =
      (exp (θ₁ * I) • ∫ ρ : ℝ in r..R, f (circleMap z₀ ρ θ₁)) -
        (exp (θ₂ * I) • ∫ ρ : ℝ in r..R, f (circleMap z₀ ρ θ₂)) +
        (∫ θ : ℝ in θ₁..θ₂, deriv (circleMap z₀ R) θ • f (circleMap z₀ R θ)) -
        (∫ θ : ℝ in θ₁..θ₂, deriv (circleMap z₀ r) θ • f (circleMap z₀ r θ)) := by
  set γ := truncatedSectorBoundary z₀ r R θ₁ θ₂
  have hi : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume 0 4 :=
    (isPiecewiseC1On_truncatedSectorBoundary z₀ r R θ₁ θ₂).intervalIntegrable_deriv_smul_comp
      (by rwa [uIcc_of_le (by norm_num)])
  have hi_sub {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) :
      IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b :=
    hi.mono_set (by rw [uIcc_of_le hab, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc ha hb)
  have hleg {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 4) (hab : a ≤ b)
      {η : ℝ → ℂ} {φ : ℝ → ℝ} {c : ℝ}
      (heq : EqOn γ (η ∘ φ) (Icc a b))
      (hφ : ∀ t ∈ uIcc a b, HasDerivAt φ c t)
      (hη : ∀ u, DifferentiableAt ℝ η u)
      (hη' : Continuous (deriv η)) :
      ∫ t in a..b, deriv γ t • f (γ t) = ∫ u in φ a..φ b, deriv η u • f (η u) := by
    rw [TauCeti.Contour.intervalIntegral_deriv_smul_congr
      (heq.mono (uIoo_of_le hab ▸ Ioo_subset_Icc_self))]
    refine TauCeti.Contour.integral_deriv_smul_comp_reparam hφ continuousOn_const
      (fun u _ ↦ hη u) hη'.continuousOn (hf.mono ?_)
    rw [← image_comp, uIcc_of_le hab, ← heq.image_eq]
    exact image_mono (Icc_subset_Icc ha hb)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3)
      (hi_sub (by norm_num) (by norm_num) (by norm_num))
      (hi_sub (by norm_num) (by norm_num) (by norm_num)),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 2)
      (hi_sub (by norm_num) (by norm_num) (by norm_num))
      (hi_sub (by norm_num) (by norm_num) (by norm_num)),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      (hi_sub (by norm_num) (by norm_num) (by norm_num))
      (hi_sub (by norm_num) (by norm_num) (by norm_num))]
  have e₀ : ∫ t in (0 : ℝ)..1, deriv γ t • f (γ t) =
      exp (θ₁ * I) • ∫ ρ : ℝ in r..R, f (circleMap z₀ ρ θ₁) := by
    rw [hleg (by norm_num) (by norm_num) (by norm_num)
      (η := fun ρ ↦ circleMap z₀ ρ θ₁) (φ := fun t ↦ r + t * (R - r)) (c := R - r)
      (fun t ht ↦ truncatedSectorBoundary_of_mem_Icc_zero_one ht)
      (fun t _ ↦ by simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (R - r)).const_add r)
      (fun ρ ↦ (TauCeti.hasDerivAt_circleMap_radius z₀ θ₁ ρ).differentiableAt)
      (continuous_const.congr fun ρ ↦ (TauCeti.deriv_circleMap_radius z₀ θ₁ ρ).symm)]
    simp [TauCeti.deriv_circleMap_radius, intervalIntegral.integral_smul]
  have e₁ : ∫ t in (1 : ℝ)..2, deriv γ t • f (γ t) =
      ∫ θ : ℝ in θ₁..θ₂, deriv (circleMap z₀ R) θ • f (circleMap z₀ R θ) := by
    rw [hleg (by norm_num) (by norm_num) (by norm_num)
      (η := circleMap z₀ R) (φ := fun t ↦ θ₁ + (t - 1) * (θ₂ - θ₁)) (c := θ₂ - θ₁)
      (fun t ht ↦ truncatedSectorBoundary_of_mem_Icc_one_two ht)
      (fun t _ ↦ by
        simpa only [one_mul] using (((hasDerivAt_id' t).sub_const 1).mul_const _).const_add θ₁)
      (fun θ ↦ (hasDerivAt_circleMap z₀ R θ).differentiableAt)
      (continuous_deriv_circleMap z₀ R)]
    norm_num
  have e₂ : ∫ t in (2 : ℝ)..3, deriv γ t • f (γ t) =
      exp (θ₂ * I) • ∫ ρ : ℝ in R..r, f (circleMap z₀ ρ θ₂) := by
    rw [hleg (by norm_num) (by norm_num) (by norm_num)
      (η := fun ρ ↦ circleMap z₀ ρ θ₂) (φ := fun t ↦ R + (t - 2) * (r - R)) (c := r - R)
      (fun t ht ↦ truncatedSectorBoundary_of_mem_Icc_two_three ht)
      (fun t _ ↦ by
        simpa only [one_mul] using (((hasDerivAt_id' t).sub_const 2).mul_const _).const_add R)
      (fun ρ ↦ (TauCeti.hasDerivAt_circleMap_radius z₀ θ₂ ρ).differentiableAt)
      (continuous_const.congr fun ρ ↦ (TauCeti.deriv_circleMap_radius z₀ θ₂ ρ).symm)]
    have h2 : R + (2 - 2) * (r - R) = R := by ring
    have h3 : R + (3 - 2) * (r - R) = r := by ring
    rw [h2, h3]
    simp [TauCeti.deriv_circleMap_radius, intervalIntegral.integral_smul]
  have e₃ : ∫ t in (3 : ℝ)..4, deriv γ t • f (γ t) =
      ∫ θ : ℝ in θ₂..θ₁, deriv (circleMap z₀ r) θ • f (circleMap z₀ r θ) := by
    rw [hleg (by norm_num) (by norm_num) (by norm_num)
      (η := circleMap z₀ r) (φ := fun t ↦ θ₂ + (t - 3) * (θ₁ - θ₂)) (c := θ₁ - θ₂)
      (fun t ht ↦ truncatedSectorBoundary_of_mem_Icc_three_four ht)
      (fun t _ ↦ by
        simpa only [one_mul] using (((hasDerivAt_id' t).sub_const 3).mul_const _).const_add θ₂)
      (fun θ ↦ (hasDerivAt_circleMap z₀ r θ).differentiableAt)
      (continuous_deriv_circleMap z₀ r)]
    have h3 : θ₂ + (3 - 3) * (θ₁ - θ₂) = θ₂ := by ring
    have h4 : θ₂ + (4 - 3) * (θ₁ - θ₂) = θ₁ := by ring
    rw [h3, h4]
  rw [e₀, e₁, e₂, e₃, intervalIntegral.integral_symm r R, intervalIntegral.integral_symm θ₁ θ₂,
    smul_neg]
  abel

end Integral

end Complex

end
