/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Scalar Cayley transform and its real inverse coordinate

The fractional-linear formulas `(z - i) / (z + i)` and `i (1 + w) / (1 - w)` are inverse away
from their poles. The first formula sends real inputs to the unit circle and the second is real
on that circle.

On the real axis, `TauCeti.continuousAt_sub_I_div_add_I` gives continuity and
`TauCeti.norm_sub_I_div_norm_add_I_ofReal` gives unit norm. The real inverse
`Complex.inverseCayleyCoord` is continuous away from `1` and is
`-w.im / (1 - w.re)` on the circle.

These scalar lemmas come from the Tau Ceti modules `Analysis.Complex.UpperHalfPlane.Cayley`
and `Analysis.Complex.Pick.Nevanlinna`, by the Tau Ceti contributors, Jon Crall,
Claude Opus 5 and OpenAI gpt-6.1-sol. The real inverse coordinate API is adapted from Kitware DKPS
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`
(Jon Crall and Claude Opus 5, copyright (c) 2026 Kitware, Inc., Apache-2.0).
The Cayley transform is treated in Ahlfors, *Complex Analysis*, 3rd ed., Ch. 3 §3.
-/

public section

open Complex

namespace TauCeti

/-- The denominator of the Cayley transform does not vanish on the closed upper half-plane. -/
theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

/-- The squared distances from `z` to `-i` and to `i` differ by `4 * z.im`. -/
theorem norm_add_I_sq (z : ℂ) : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
  ring

/-- The Cayley transform is continuous at every real point. -/
theorem continuousAt_sub_I_div_add_I (x : ℝ) :
    ContinuousAt (fun z : ℂ => (z - I) / (z + I)) (x : ℂ) :=
  (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const)
    (add_I_ne_zero_of_im_nonneg (by simp))

/-- The Cayley transform of a real point lies on the unit circle. -/
@[simp] theorem norm_sub_I_div_norm_add_I_ofReal (x : ℝ) :
    ‖(x : ℂ) - I‖ / ‖(x : ℂ) + I‖ = 1 := by
  have hx : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  rw [div_eq_one_iff_eq (norm_ne_zero_iff.mpr hx),
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_add_I_sq]
  simp

/-- The real part of a boundary Cayley point. -/
@[simp]
theorem re_sub_I_div_add_I_ofReal (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  rw [div_re]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

/-- The imaginary part of a boundary Cayley point. -/
@[simp]
theorem im_sub_I_div_add_I_ofReal (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).im = -(2 * x) / (x ^ 2 + 1) := by
  rw [div_im]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

/-- The denominator `z + i` of the Cayley transform at `z = i (1 + w) / (1 - w)` is
`2 i / (1 - w)`. -/
theorem I_mul_one_add_div_one_sub_add_I {w : ℂ} (hw : w ≠ 1) :
    I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by
  have : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  field_simp
  ring

/-- The denominator `1 - w` of the inverse Cayley transform at `w = (z - i) / (z + i)` is
`2 i / (z + i)`. -/
theorem one_sub_sub_I_div_add_I {z : ℂ} (hz : z + I ≠ 0) :
    1 - (z - I) / (z + I) = 2 * I / (z + I) := by
  field_simp
  ring

/-- Away from `w = 1`, the value `i (1 + w) / (1 - w)` of the inverse Cayley transform keeps the
denominator `z + i` of the transform away from `0`. -/
theorem I_mul_one_add_div_one_sub_add_I_ne_zero {w : ℂ} (hw : w ≠ 1) :
    I * (1 + w) / (1 - w) + I ≠ 0 := by
  rw [I_mul_one_add_div_one_sub_add_I hw]
  exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.mpr hw.symm)

/-- The inverse Cayley transform `w ↦ i (1 + w) / (1 - w)` is a right inverse of the transform
away from `w = 1`. -/
theorem sub_I_div_add_I_I_mul_one_add_div_one_sub {w : ℂ} (hw : w ≠ 1) :
    (I * (1 + w) / (1 - w) - I) / (I * (1 + w) / (1 - w) + I) = w := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hnum : I * (1 + w) / (1 - w) - I = 2 * I * w / (1 - w) := by
    field_simp
    ring
  rw [I_mul_one_add_div_one_sub_add_I hw, hnum]
  field_simp

/-- The inverse Cayley transform takes the Cayley image of a point back to that point. -/
theorem I_mul_one_add_sub_I_div_add_I_div_one_sub {z : ℂ} (hz : z + I ≠ 0) :
    I * (1 + (z - I) / (z + I)) / (1 - (z - I) / (z + I)) = z := by
  field_simp
  ring

/-- The imaginary part of `i (ζ - z) / (ζ + z)` is `(‖ζ‖² - ‖z‖²) / ‖ζ + z‖²`. -/
theorem im_I_mul_sub_div_add (ζ z : ℂ) :
    (I * (ζ - z) / (ζ + z)).im = (normSq ζ - normSq z) / normSq (ζ + z) := by
  rw [div_im, ← sub_div, normSq_apply, normSq_apply, normSq_apply]
  congr 1
  simp only [mul_re, mul_im, I_re, I_im, sub_re, sub_im, add_re, add_im]
  ring

end TauCeti

namespace Complex

/-- The real inverse Cayley coordinate, with value zero at its singular point `1`. -/
noncomputable def inverseCayleyCoord (w : ℂ) : ℝ := (I * (1 + w) / (1 - w)).re

/-- Formula for the real inverse Cayley coordinate. -/
theorem inverseCayleyCoord_def (w : ℂ) :
    inverseCayleyCoord w = (I * (1 + w) / (1 - w)).re := (rfl)

/-- The real inverse Cayley coordinate is continuous at every complex point other than its pole. -/
@[fun_prop] theorem continuousAt_inverseCayleyCoord {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt inverseCayleyCoord z := by
  have h : ContinuousAt (fun w : ℂ ↦ I * (1 + w) / (1 - w)) z :=
    (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hz.symm)
  have hcoord : inverseCayleyCoord = re ∘ (fun w : ℂ ↦ I * (1 + w) / (1 - w)) := by
    funext w
    simp only [Function.comp_apply, inverseCayleyCoord_def]
  rw [hcoord]
  exact continuous_re.continuousAt.comp h

/-- The inverse Cayley coordinate has value zero at `1`. -/
@[simp] theorem inverseCayleyCoord_one : inverseCayleyCoord 1 = 0 := by
  simp [inverseCayleyCoord]

/-- Applying the inverse coordinate to a complex Cayley parameter recovers its real part. -/
@[simp] theorem inverseCayleyCoord_cayley (z : ℂ) :
    inverseCayleyCoord ((z - I) / (z + I)) = z.re := by
  by_cases hz : z + I = 0
  · rw [eq_neg_of_add_eq_zero_left hz]
    simp [inverseCayleyCoord]
  · rw [inverseCayleyCoord_def, TauCeti.I_mul_one_add_sub_I_div_add_I_div_one_sub hz]

/-- On the unit circle the inverse Cayley coordinate is real:
`inverseCayleyCoord w = i (1 + w) / (1 - w)`. -/
theorem ofReal_inverseCayleyCoord {w : ℂ} (hw : ‖w‖ = 1) :
    (inverseCayleyCoord w : ℂ) = I * (1 + w) / (1 - w) := by
  have him : (I * (1 + w) / (1 - w)).im = 0 := by
    simpa [normSq_eq_norm_sq, hw, sub_eq_add_neg] using TauCeti.im_I_mul_sub_div_add 1 (-w)
  exact Complex.ext (by simp [inverseCayleyCoord_def]) (by simp [him])

/-- The Cayley transform recovers every unit-circle point other than `1`. -/
theorem cayley_inverseCayleyCoord {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) :
    ((inverseCayleyCoord w : ℂ) - I) / ((inverseCayleyCoord w : ℂ) + I) = w := by
  rw [ofReal_inverseCayleyCoord hw]
  exact TauCeti.sub_I_div_add_I_I_mul_one_add_div_one_sub h1

/-- On the unit circle the inverse Cayley coordinate is `w ↦ -Im w / (1 - Re w)`. -/
theorem inverseCayleyCoord_eq_neg_im_div {w : ℂ} (hw : ‖w‖ = 1) :
    inverseCayleyCoord w = -w.im / (1 - w.re) := by
  have hre : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := normSq_eq_norm_sq w
    rw [hw, normSq_apply] at this
    nlinarith
  rw [inverseCayleyCoord_def]
  simp only [div_re, mul_re, mul_im, I_re, I_im, add_re, add_im, sub_re, sub_im, one_re, one_im,
    normSq_apply]
  by_cases h1 : 1 - w.re = 0
  · have : w.im = 0 := by nlinarith
    simp [this, show w.re = 1 by linarith]
  · field_simp
    linear_combination w.im * hre

end Complex
