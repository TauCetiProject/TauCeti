/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.TruncatedSector
public import TauCeti.Analysis.Contour.Curve.Rectangle
import Mathlib.MeasureTheory.Integral.CircleIntegral

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

private theorem contDiff_polarOfComplex (z₀ : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun w : ℂ ↦ circleMap z₀ w.re w.im) := by
  have hexp : ContDiff ℝ n (fun w : ℂ ↦ exp ((w.im : ℂ) * I)) :=
    ((contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
      ((ofRealCLM.contDiff.comp imCLM.contDiff).mul contDiff_const)
  exact contDiff_const.add ((ofRealCLM.contDiff.comp reCLM.contDiff).mul hexp)

/-- The truncated-sector boundary is piecewise `C¹` on `[0, 4]`. -/
theorem isPiecewiseC1On_truncatedSectorBoundary (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    TauCeti.IsPiecewiseC1On (truncatedSectorBoundary z₀ r R θ₁ θ₂) 0 4 :=
  (contDiff_polarOfComplex z₀ (n := 1)).contDiffOn.comp_isPiecewiseC1On
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

/-- Along an open cell `(a, b)` where a curve `γ` agrees with a `C¹` curve `η` on `[a, b]`
(`a ≤ b`), the contour integrand `deriv γ t • f (γ t)` is interval-integrable and has the same
integral as `deriv η t • f (η t)`. -/
private theorem intervalIntegrable_and_integral_eq_of_eqOn_Icc {γ η : ℝ → ℂ} {f : ℂ → E} {a b : ℝ}
    (hab : a ≤ b) (hγ : EqOn γ η (Icc a b)) (hη : ContDiff ℝ 1 η)
    (hf : ContinuousOn f (η '' Icc a b)) :
    IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b ∧
      ∫ t in a..b, deriv γ t • f (γ t) = ∫ t in a..b, deriv η t • f (η t) := by
  have heq_Ioo : EqOn (fun t ↦ deriv γ t • f (γ t)) (fun t ↦ deriv η t • f (η t)) (Ioo a b) := by
    intro t ht
    dsimp only
    have hev : γ =ᶠ[nhds t] η :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) fun u hu ↦ hγ hu
    rw [hev.deriv_eq, hγ (Ioo_subset_Icc_self ht)]
  have heq_uIoo : EqOn (fun t ↦ deriv γ t • f (γ t)) (fun t ↦ deriv η t • f (η t)) (uIoo a b) := by
    rwa [uIoo_of_le hab]
  have hcont : ContinuousOn (fun t ↦ deriv η t • f (η t)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hη.continuous_deriv le_rfl).continuousOn.smul
      (hf.comp hη.continuous.continuousOn (mapsTo_image η _))
  exact ⟨(intervalIntegrable_congr_uIoo heq_uIoo).2 hcont.intervalIntegrable,
    intervalIntegral.integral_congr_uIoo heq_uIoo⟩

/-- Radial segment change of variables on `[k, k + 1]`: for
`η t = circleMap z₀ (a + (t - k) * (b - a)) θ`, the contour integral over `k..k + 1` is
`exp (θ * I) • ∫ ρ in a..b, f (circleMap z₀ ρ θ)`. -/
private theorem integral_radial_leg (f : ℂ → E) (z₀ : ℂ) (a b θ k : ℝ) :
    ∫ t in k..(k + 1),
        deriv (fun u : ℝ ↦ circleMap z₀ (a + (u - k) * (b - a)) θ) t •
          f (circleMap z₀ (a + (t - k) * (b - a)) θ) =
      exp (θ * I) • ∫ ρ : ℝ in a..b, f (circleMap z₀ ρ θ) := by
  have hderiv (t : ℝ) :
      deriv (fun u : ℝ ↦ circleMap z₀ (a + (u - k) * (b - a)) θ) t =
        ((b - a : ℝ) : ℂ) * exp (θ * I) := by
    have hd1 : HasDerivAt (fun u : ℝ ↦ a + (u - k) * (b - a)) (0 + 1 * (b - a)) t :=
      (hasDerivAt_const t a).add (((hasDerivAt_id t).sub_const k).mul_const (b - a))
    rw [zero_add, one_mul] at hd1
    have hd2 : HasDerivAt (fun u : ℝ ↦ ((a + (u - k) * (b - a) : ℝ) : ℂ)) ((b - a : ℝ) : ℂ) t :=
      hd1.ofReal_comp
    have hd3 : HasDerivAt (fun u : ℝ ↦ z₀ + ((a + (u - k) * (b - a) : ℝ) : ℂ) * exp (θ * I))
        (0 + ((b - a : ℝ) : ℂ) * exp (θ * I)) t :=
      (hasDerivAt_const t z₀).add (hd2.mul_const (exp (θ * I)))
    rw [zero_add] at hd3
    exact hd3.deriv
  have h1 :
      ∫ t in k..(k + 1),
          deriv (fun u : ℝ ↦ circleMap z₀ (a + (u - k) * (b - a)) θ) t •
            f (circleMap z₀ (a + (t - k) * (b - a)) θ) =
        exp (θ * I) • ((b - a) • ∫ s in (0 : ℝ)..1, f (circleMap z₀ (a + s * (b - a)) θ)) := by
    have hshift := intervalIntegral.integral_comp_sub_right
      (fun s : ℝ ↦ (((b - a : ℝ) : ℂ) * exp (θ * I)) • f (circleMap z₀ (a + s * (b - a)) θ)) k
        (a := k) (b := k + 1)
    rw [sub_self, add_sub_cancel_left] at hshift
    calc
      _ = ∫ t in k..(k + 1),
            (((b - a : ℝ) : ℂ) * exp (θ * I)) • f (circleMap z₀ (a + (t - k) * (b - a)) θ) :=
        intervalIntegral.integral_congr fun t _ ↦ by rw [hderiv]
      _ = ∫ s in (0 : ℝ)..1,
            (exp (θ * I) • (b - a) • f (circleMap z₀ (a + s * (b - a)) θ)) := by
        rw [hshift]
        exact intervalIntegral.integral_congr fun s _ ↦ by
          rw [mul_comm ((b - a : ℝ) : ℂ), mul_smul, coe_smul]
      _ = exp (θ * I) • ((b - a) • ∫ s in (0 : ℝ)..1, f (circleMap z₀ (a + s * (b - a)) θ)) := by
        rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  rw [h1]
  congr 1
  have hcov := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun ρ : ℝ ↦ f (circleMap z₀ ρ θ)) (b - a) a
  rw [mul_zero, zero_add, mul_one, sub_add_cancel] at hcov
  rw [← hcov]
  exact congrArg _ (intervalIntegral.integral_congr fun s _ ↦ by ring_nf)

/-- Circular arc change of variables on `[k, k + 1]`: for
`η t = circleMap z₀ ρ (α + (t - k) * (β - α))`, the contour integral over `k..k + 1` is
`∫ θ in α..β, deriv (circleMap z₀ ρ) θ • f (circleMap z₀ ρ θ)`. -/
private theorem integral_arc_leg (f : ℂ → E) (z₀ : ℂ) (ρ α β k : ℝ) :
    ∫ t in k..(k + 1),
        deriv (fun u : ℝ ↦ circleMap z₀ ρ (α + (u - k) * (β - α))) t •
          f (circleMap z₀ ρ (α + (t - k) * (β - α))) =
      ∫ θ : ℝ in α..β, deriv (circleMap z₀ ρ) θ • f (circleMap z₀ ρ θ) := by
  have hderiv (t : ℝ) :
      deriv (fun u : ℝ ↦ circleMap z₀ ρ (α + (u - k) * (β - α))) t =
        (β - α) • deriv (circleMap z₀ ρ) (α + (t - k) * (β - α)) := by
    have hd1 : HasDerivAt (fun u : ℝ ↦ α + (u - k) * (β - α)) (0 + 1 * (β - α)) t :=
      (hasDerivAt_const t α).add (((hasDerivAt_id t).sub_const k).mul_const (β - α))
    rw [zero_add, one_mul] at hd1
    have hd2 := ((hasDerivAt_circleMap z₀ ρ (α + (t - k) * (β - α))).scomp t hd1).deriv
    rw [deriv_circleMap]
    exact hd2
  have hshift := intervalIntegral.integral_comp_sub_right
    (fun s : ℝ ↦ (β - α) •
      (deriv (circleMap z₀ ρ) (α + s * (β - α)) • f (circleMap z₀ ρ (α + s * (β - α))))) k
      (a := k) (b := k + 1)
  rw [sub_self, add_sub_cancel_left] at hshift
  have hcov := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun θ : ℝ ↦ deriv (circleMap z₀ ρ) θ • f (circleMap z₀ ρ θ)) (β - α) α
  rw [mul_zero, zero_add, mul_one, sub_add_cancel] at hcov
  calc
    _ = ∫ t in k..(k + 1), (β - α) •
          (deriv (circleMap z₀ ρ) (α + (t - k) * (β - α)) •
            f (circleMap z₀ ρ (α + (t - k) * (β - α)))) :=
      intervalIntegral.integral_congr fun t _ ↦ by rw [hderiv, smul_assoc]
    _ = (β - α) • ∫ s in (0 : ℝ)..1,
          deriv (circleMap z₀ ρ) (α + s * (β - α)) • f (circleMap z₀ ρ (α + s * (β - α))) := by
      rw [hshift, intervalIntegral.integral_smul]
    _ = ∫ θ : ℝ in α..β, deriv (circleMap z₀ ρ) θ • f (circleMap z₀ ρ θ) := by
      rw [← hcov]
      exact congrArg _ (intervalIntegral.integral_congr fun s _ ↦ by ring_nf)

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
  let η₀ : ℝ → ℂ := fun u ↦ circleMap z₀ (r + (u - 0) * (R - r)) θ₁
  let η₁ : ℝ → ℂ := fun u ↦ circleMap z₀ R (θ₁ + (u - 1) * (θ₂ - θ₁))
  let η₂ : ℝ → ℂ := fun u ↦ circleMap z₀ (R + (u - 2) * (r - R)) θ₂
  let η₃ : ℝ → ℂ := fun u ↦ circleMap z₀ r (θ₂ + (u - 3) * (θ₁ - θ₂))
  have hrad (a b θ k : ℝ) : ContDiff ℝ 1 (fun u : ℝ ↦ circleMap z₀ (a + (u - k) * (b - a)) θ) :=
    contDiff_const.add
      ((ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ 1 fun u : ℝ ↦ a + (u - k) * (b - a))).mul
        contDiff_const)
  have harc (ρ α β k : ℝ) : ContDiff ℝ 1 (fun u : ℝ ↦ circleMap z₀ ρ (α + (u - k) * (β - α))) :=
    (contDiff_circleMap z₀ ρ).comp (by fun_prop)
  have hγ₀ : EqOn γ η₀ (Icc 0 1) := fun t ht ↦ by
    simpa [γ, η₀] using truncatedSectorBoundary_of_mem_Icc_zero_one ht
  have hγ₁ : EqOn γ η₁ (Icc 1 2) := fun t ht ↦
    truncatedSectorBoundary_of_mem_Icc_one_two ht
  have hγ₂ : EqOn γ η₂ (Icc 2 3) := fun t ht ↦
    truncatedSectorBoundary_of_mem_Icc_two_three ht
  have hγ₃ : EqOn γ η₃ (Icc 3 4) := fun t ht ↦
    truncatedSectorBoundary_of_mem_Icc_three_four ht
  have hsub₀ : η₀ '' Icc 0 1 ⊆ γ '' Icc 0 4 :=
    hγ₀.symm.image_eq.trans_subset (image_mono (Icc_subset_Icc_right (by norm_num)))
  have hsub₁ : η₁ '' Icc 1 2 ⊆ γ '' Icc 0 4 :=
    hγ₁.symm.image_eq.trans_subset (image_mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  have hsub₂ : η₂ '' Icc 2 3 ⊆ γ '' Icc 0 4 :=
    hγ₂.symm.image_eq.trans_subset (image_mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  have hsub₃ : η₃ '' Icc 3 4 ⊆ γ '' Icc 0 4 :=
    hγ₃.symm.image_eq.trans_subset (image_mono (Icc_subset_Icc_left (by norm_num)))
  obtain ⟨hi₀, heq₀⟩ := intervalIntegrable_and_integral_eq_of_eqOn_Icc (by norm_num) hγ₀
    (hrad r R θ₁ 0) (hf.mono hsub₀)
  obtain ⟨hi₁, heq₁⟩ := intervalIntegrable_and_integral_eq_of_eqOn_Icc (by norm_num) hγ₁
    (harc R θ₁ θ₂ 1) (hf.mono hsub₁)
  obtain ⟨hi₂, heq₂⟩ := intervalIntegrable_and_integral_eq_of_eqOn_Icc (by norm_num) hγ₂
    (hrad R r θ₂ 2) (hf.mono hsub₂)
  obtain ⟨hi₃, heq₃⟩ := intervalIntegrable_and_integral_eq_of_eqOn_Icc (by norm_num) hγ₃
    (harc r θ₂ θ₁ 3) (hf.mono hsub₃)
  have hi₀₁ := hi₀.trans hi₁
  have hi₀₂ := hi₀₁.trans hi₂
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₀₂ hi₃,
    ← intervalIntegral.integral_add_adjacent_intervals hi₀₁ hi₂,
    ← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁,
    heq₀, heq₁, heq₂, heq₃]
  have e₀ : ∫ t in (0 : ℝ)..1, deriv η₀ t • f (η₀ t) =
      exp (θ₁ * I) • ∫ ρ : ℝ in r..R, f (circleMap z₀ ρ θ₁) := by
    simpa only [zero_add] using integral_radial_leg f z₀ r R θ₁ 0
  have e₁ : ∫ t in (1 : ℝ)..2, deriv η₁ t • f (η₁ t) =
      ∫ θ : ℝ in θ₁..θ₂, deriv (circleMap z₀ R) θ • f (circleMap z₀ R θ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num]
    exact integral_arc_leg f z₀ R θ₁ θ₂ 1
  have e₂ : ∫ t in (2 : ℝ)..3, deriv η₂ t • f (η₂ t) =
      exp (θ₂ * I) • ∫ ρ : ℝ in R..r, f (circleMap z₀ ρ θ₂) := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num]
    exact integral_radial_leg f z₀ R r θ₂ 2
  have e₃ : ∫ t in (3 : ℝ)..4, deriv η₃ t • f (η₃ t) =
      ∫ θ : ℝ in θ₂..θ₁, deriv (circleMap z₀ r) θ • f (circleMap z₀ r θ) := by
    rw [show (4 : ℝ) = 3 + 1 by norm_num]
    exact integral_arc_leg f z₀ r θ₂ θ₁ 3
  rw [e₀, e₁, e₂, e₃, intervalIntegral.integral_symm r R, intervalIntegral.integral_symm θ₁ θ₂,
    smul_neg]
  abel

end Integral

end Complex

end
