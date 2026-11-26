/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Scalar Cayley transform and its real inverse coordinate

The fractional-linear formulas `(z - i) / (z + i)` and `i (1 + w) / (1 - w)` are inverse away
from their poles. The first formula sends real inputs to the unit circle and the second is real
on that circle.

`TauCeti.continuousAt_sub_I_div_add_I` gives continuity away from the pole `-i`.
`TauCeti.norm_sub_I_div_norm_add_I_ofReal` gives unit norm on the real axis. The real inverse
`Complex.inverseCayleyCoord` is continuous away from `1` and is
`-w.im / (1 - w.re)` on the circle. The norm comparisons identify the open and closed unit
discs by the sign of the imaginary part, also for the rotated transform.

These scalar lemmas come from the Tau Ceti modules `Analysis.Complex.UpperHalfPlane.Cayley`
and `Analysis.Complex.Pick.Nevanlinna`, by the Tau Ceti contributors, Jon Crall,
Claude Opus 5 and OpenAI gpt-6.1-sol. The real inverse coordinate API is adapted from Kitware DKPS
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`
(Jon Crall and Claude Opus 5, copyright (c) 2026 Kitware, Inc., Apache-2.0).
The Cayley transform is treated in Ahlfors, *Complex Analysis*, 3rd ed., Ch. 3 §3.
-/

public section

open Complex Set

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

/-- A point is closer to `i` than to `-i` exactly when it lies in the open upper half-plane. -/
theorem norm_sub_I_lt_norm_add_I_iff {z : ℂ} : ‖z - I‖ < ‖z + I‖ ↔ 0 < z.im := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- The Cayley transform lies in the closed unit disc exactly on the closed upper half-plane. -/
theorem norm_sub_I_div_add_I_le_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖(z - I) / (z + I)‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr hz), ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- The Cayley transform lies in the open unit disc exactly on the open upper half-plane. -/
theorem norm_sub_I_div_add_I_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖(z - I) / (z + I)‖ < 1 ↔ 0 < z.im := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- The Cayley transform is continuous away from its pole `-i`. -/
theorem continuousAt_sub_I_div_add_I {z : ℂ} (hz : z + I ≠ 0) :
    ContinuousAt (fun w : ℂ ↦ (w - I) / (w + I)) z :=
  (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) hz

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

/-- The closed-disc criterion in the normal form used by `simp` after `norm_div`. -/
@[simp] theorem norm_sub_I_div_norm_add_I_le_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖z - I‖ / ‖z + I‖ ≤ 1 ↔ 0 ≤ z.im := by
  simpa only [norm_div] using norm_sub_I_div_add_I_le_one_iff hz

/-- The open-disc criterion in the normal form used by `simp` after `norm_div`. -/
@[simp] theorem norm_sub_I_div_norm_add_I_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖z - I‖ / ‖z + I‖ < 1 ↔ 0 < z.im := by
  simpa only [norm_div] using norm_sub_I_div_add_I_lt_one_iff hz

/-- The Cayley transform is injective wherever its denominator does not vanish. -/
theorem injOn_sub_I_div_add_I :
    InjOn (fun z : ℂ => (z - I) / (z + I)) {z | z + I ≠ 0} := by
  intro z hz w hw h
  simp only [mem_ofPred_eq] at hz hw
  rw [div_eq_div_iff hz hw] at h
  have h2 : (2 * I) * (z - w) = 0 := by linear_combination h
  simpa [sub_eq_zero, I_ne_zero] using h2

/-- The Cayley transform has the difference quotient `2 * i / ((s + i) * (t + i))`. -/
theorem sub_I_div_add_I_sub_sub_I_div_add_I {s t : ℂ} (hs : s + I ≠ 0) (ht : t + I ≠ 0) :
    (s - I) / (s + I) - (t - I) / (t + I) = 2 * I * (s - t) / ((s + I) * (t + I)) := by
  rw [div_sub_div _ _ hs ht]
  ring

/-- The real part of the inverse Cayley transform `i (1 + w) / (1 - w)`, weighted by
`‖1 - w‖²`, is `-2 im w`: the identity `re (i (1 + w) / (1 - w)) ‖1 - w‖² = -2 im w`. At the pole
`w = 1` both sides vanish, by the convention `x / 0 = 0`. -/
theorem re_I_mul_one_add_div_one_sub_mul_norm_one_sub_sq (w : ℂ) :
    (I * (1 + w) / (1 - w)).re * ‖1 - w‖ ^ 2 = -2 * w.im := by
  rcases eq_or_ne w 1 with rfl | h1
  · simp
  have hn0 : normSq (1 - w) ≠ 0 := normSq_eq_zero.not.mpr (sub_ne_zero.mpr h1.symm)
  rw [Complex.sq_norm, div_re]
  simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im]
  field_simp
  ring

/-- Under the inverse Cayley transform `c`, the simple fraction `c' / (c - x)` at a real point `x`
splits into the simple fraction at its Cayley image and one at `1`. -/
theorem cayley_simple_fraction {ζ : ℂ} (x : ℝ) (hζ1 : ζ ≠ 1)
    (hζx : ζ ≠ ((x : ℂ) - I) / ((x : ℂ) + I)) :
    1 / (I * (1 + ζ) / (1 - ζ) - x) * (2 * I / (1 - ζ) ^ 2) =
      1 / (ζ - ((x : ℂ) - I) / ((x : ℂ) + I)) + 1 / (1 - ζ) := by
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr hζ1.symm
  have hxI : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hD : I * (1 + ζ) - x * (1 - ζ) ≠ 0 := by
    intro h
    apply hζx
    rw [eq_div_iff hxI]
    linear_combination h
  have hc : I * (1 + ζ) / (1 - ζ) - x = (I * (1 + ζ) - x * (1 - ζ)) / (1 - ζ) := by
    field_simp
  have hw : ζ - ((x : ℂ) - I) / ((x : ℂ) + I) = (I * (1 + ζ) - x * (1 - ζ)) / ((x : ℂ) + I) := by
    field_simp
    ring
  rw [hc, hw]
  field_simp
  ring

/-- The map `z ↦ i (ζ - z) / (ζ + z)` sends the closed disc of radius `‖ζ‖` into the closed upper
half-plane. -/
theorem im_I_mul_sub_div_add_nonneg {ζ z : ℂ} (hz : ‖z‖ ≤ ‖ζ‖) :
    0 ≤ (I * (ζ - z) / (ζ + z)).im := by
  rw [im_I_mul_sub_div_add, normSq_eq_norm_sq, normSq_eq_norm_sq]
  exact div_nonneg (sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) hz 2)) (normSq_nonneg _)

/-- For `‖ζ‖ ≤ 1`, the map `w ↦ ζ (i - w) / (w + i)` sends the closed upper half-plane into the
closed unit disc. -/
theorem norm_mul_I_sub_div_add_I_le_one {ζ w : ℂ} (hζ : ‖ζ‖ ≤ 1) (hw : 0 ≤ w.im) :
    ‖ζ * (I - w) / (w + I)‖ ≤ 1 := by
  rw [mul_div_assoc, norm_mul, norm_div, norm_sub_rev]
  exact (mul_le_of_le_one_left (by positivity) hζ).trans
    ((norm_sub_I_div_norm_add_I_le_one_iff (add_I_ne_zero_of_im_nonneg hw)).2 hw)

/-- For `ζ ≠ 0`, the map `w ↦ ζ (i - w) / (w + i)` never takes the value `-ζ`. -/
theorem mul_I_sub_div_add_I_ne_neg {ζ : ℂ} (hζ : ζ ≠ 0) (w : ℂ) : ζ * (I - w) / (w + I) ≠ -ζ := by
  intro h
  rcases eq_or_ne (w + I) 0 with hw | hw
  · rw [hw, div_zero, eq_comm, neg_eq_zero] at h
    exact hζ h
  · rw [div_eq_iff hw] at h
    have : ζ * (2 * I) = 0 := by linear_combination h
    simp [hζ, I_ne_zero] at this

/-- The map `w ↦ ζ (i - w) / (w + i)` inverts `z ↦ i (ζ - z) / (ζ + z)` away from `-ζ`. -/
theorem mul_I_sub_I_mul_sub_div_add_div_add_I {ζ z : ℂ} (hζ : ζ ≠ 0) (hz : ζ + z ≠ 0) :
    ζ * (I - I * (ζ - z) / (ζ + z)) / (I * (ζ - z) / (ζ + z) + I) = z := by
  have h2 : I * (ζ - z) / (ζ + z) + I = 2 * I * ζ / (ζ + z) := by
    field_simp
    ring
  rw [h2, div_eq_iff (by simp [hζ, hz, I_ne_zero])]
  field_simp
  ring

/-- The map `z ↦ i (ζ - z) / (ζ + z)` inverts `w ↦ ζ (i - w) / (w + i)` away from `-i`. -/
theorem I_mul_sub_mul_I_sub_div_add_I_div_add {ζ w : ℂ} (hζ : ζ ≠ 0) (hw : w + I ≠ 0) :
    I * (ζ - ζ * (I - w) / (w + I)) / (ζ + ζ * (I - w) / (w + I)) = w := by
  have h2 : ζ + ζ * (I - w) / (w + I) = 2 * I * ζ / (w + I) := by
    field_simp
    ring
  rw [h2, div_eq_iff (by simp [hζ, hw, I_ne_zero])]
  field_simp
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

/-- The real inverse Cayley coordinate in terms of the imaginary part and distance to its pole. -/
theorem inverseCayleyCoord_eq_neg_two_mul_im_div_norm_one_sub_sq (w : ℂ) :
    inverseCayleyCoord w = -2 * w.im / ‖1 - w‖ ^ 2 := by
  by_cases hw : w = 1
  · subst w
    simp
  · have hne : ‖1 - w‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hw)))
    rw [eq_div_iff hne, inverseCayleyCoord_def]
    exact TauCeti.re_I_mul_one_add_div_one_sub_mul_norm_one_sub_sq w

/-- On the unit circle the inverse Cayley coordinate is `w ↦ -Im w / (1 - Re w)`. -/
theorem inverseCayleyCoord_eq_neg_im_div {w : ℂ} (hw : ‖w‖ = 1) :
    inverseCayleyCoord w = -w.im / (1 - w.re) := by
  have hnorm : ‖1 - w‖ ^ 2 = 2 * (1 - w.re) := by
    rw [← normSq_eq_norm_sq, normSq_sub, normSq_eq_norm_sq w, hw]
    simp only [normSq_one, one_pow, one_mul, conj_re]
    ring
  rw [inverseCayleyCoord_eq_neg_two_mul_im_div_norm_one_sub_sq, hnorm]
  simpa only [mul_neg, neg_mul] using
    mul_div_mul_left (-w.im) (1 - w.re) (two_ne_zero : (2 : ℝ) ≠ 0)

end Complex
