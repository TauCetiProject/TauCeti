/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Basic.Complex.OfRealSub
import TauCeti.MeasureTheory.Measure.ResolventTransform.Real
import TauCeti.Probability.Distributions.Semicircle.ResolventTransform

/-!
# The resolvent transform of the Marchenko–Pastur law

For an aspect ratio `y ≥ 0`, the resolvent transform
`m(z) = ∫ (x - z)⁻¹ d(marchenkoPastur y)(x)` (Mathlib's `MeasureTheory.resolventTransform` with
base field `ℝ` and values in `ℂ`) satisfies the Marchenko–Pastur quadratic equation

`y * z * (m(z) * m(z)) + (z + y - 1) * m(z) + 1 = 0`

at every `z : ℂ` outside the support of `marchenkoPastur y`. In the upper half-plane `m(z)` is the
unique root with positive imaginary part: at `y = 0` this reduces to the linear equation
`(z - 1) * m + 1 = 0`, while for `y > 0` the other root is `(y * z * m(z))⁻¹` and the size-biasing
relation `1 + z * m(z) = m_{semicircleReal (1 + y) y}(z)` shows that `z * m(z)` also has positive
imaginary part in the upper half-plane, forcing `(y * z * m(z))⁻¹` into the lower half-plane.

For `y < 1`, the origin lies outside the support `[(1 - √y)², (1 + √y)²]`, and evaluating the
quadratic equation at `z = 0` yields `m(0) = (1 - y)⁻¹`, that is,
`∫ x⁻¹ d(marchenkoPastur y)(x) = (1 - y)⁻¹`.

At real points `x` off the support, the real-valued transform satisfies the same quadratic
equation. Above the upper edge `(1 + √y)²` it is the root to the right of the midpoint of the two
roots, `2 y x m(x) + (x + y - 1) = √((x + y - 1)² - 4 y x)`: the left-hand side squares to the
discriminant, which is positive there, so it cannot change sign, and it is positive far above the
edge because `m(x)` is bounded below by `-(x - (1 + √y)²)⁻¹`.

## Main results

* `TauCeti.Probability.hasSum_resolventTransform_marchenkoPastur`: the Laurent expansion
  `m(z) = -∑ₙ (∫ xⁿ dMP_y) z⁻⁽ⁿ⁺¹⁾` outside the disc `|z| ≤ (1 + √y)²`.
* `TauCeti.Probability.resolventTransform_semicircleReal_one_add_eq`: the size-biasing identity
  `m_{semicircleReal (1 + y) y}(z) = 1 + z * m_{MP_y}(z)` off the support of `MP_y`.
* `TauCeti.Probability.im_mul_resolventTransform_marchenkoPastur_pos`: `Im (z * m(z)) > 0` on the
  upper half-plane.
* `TauCeti.Probability.resolventTransform_marchenkoPastur_quadratic_eq_zero`: the quadratic
  equation `y * z * (m * m) + (z + y - 1) * m + 1 = 0` off the support of `MP_y`.
* `TauCeti.Probability.eq_resolventTransform_marchenkoPastur_iff`: on the upper half-plane, `m(z)`
  is the unique root of the quadratic equation with positive imaginary part.
* `TauCeti.Probability.resolventTransform_marchenkoPastur_zero_of_lt_one`,
  `TauCeti.Probability.integral_inv_marchenkoPastur`: for `y < 1`, `m(0) = (1 - y)⁻¹` and
  `∫ x⁻¹ dMP_y = (1 - y)⁻¹`.
* `TauCeti.Probability.resolventTransform_marchenkoPastur_one_one_add_I_div_two`: for `MP_1` at
  `z = (1 + i) / 2`, `m((1 + i) / 2) = i`.
* `TauCeti.Probability.resolventTransform_marchenkoPastur_real_quadratic_eq_zero`: the quadratic
  equation of the real transform at real points off the support.
* `TauCeti.Probability.two_mul_mul_resolventTransform_marchenkoPastur_add_pos`,
  `TauCeti.Probability.two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt`: the choice of
  root above the upper edge, which gives the closed form of the real transform there.

## Implementation notes

Rather than repeating the analytic-continuation argument used for the semicircle law, we deduce
both the quadratic equation and the Herglotz property of `z * m(z)` directly from the size-biasing
identity `x · MP_y = semicircleReal (1 + y) y` (`withDensity_ofReal_marchenkoPastur`) together with
`resolventTransform_semicircleReal_quadratic_eq_zero`. Substituting `s = 1 + z * m` into
`y * s² + (z - (1 + y)) * s + 1 = 0` factors algebraically as
`z * (y * z * m² + (z + y - 1) * m + 1) = 0`, which immediately gives the equation for `z ≠ 0`;
when `0` is outside the support (`y < 1`), continuity of the resolvent transform off the support
extends the identity to `z = 0`.

## References

* V. A. Marchenko, L. A. Pastur, *Distribution of eigenvalues for some sets of random matrices*,
  Mat. Sb. 72 (1967), 507–536.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.3.1.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter
open scoped NNReal Topology

namespace TauCeti.Probability

variable {y : ℝ≥0} {z : ℂ}

/-- Outside the disc `|z| ≤ (1 + √y)²`, the resolvent transform of `marchenkoPastur y` is the
Laurent series `-∑ₙ (∫ xⁿ dMP_y) z⁻⁽ⁿ⁺¹⁾`. -/
theorem hasSum_resolventTransform_marchenkoPastur (hz : (1 + √(y : ℝ)) ^ 2 < ‖z‖) :
    HasSum (fun n ↦ -((∫ x, x ^ n ∂marchenkoPastur y : ℝ) : ℂ) * z⁻¹ ^ (n + 1))
      (resolventTransform (marchenkoPastur y) z) := by
  have hnorm : ∀ᵐ x : ℝ ∂marchenkoPastur y, ‖(x : ℂ) - 0‖ ≤ (1 + √(y : ℝ)) ^ 2 := by
    filter_upwards [ae_mem_Icc_zero_marchenkoPastur y] with x hx
    rw [sub_zero, norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hint := hasSum_resolventTransform_of_ae_norm_le hnorm (by simpa using hz)
  refine hint.congr_fun fun n ↦ ?_
  simp only [sub_zero, ← integral_complex_ofReal, ofReal_pow]

/-- Off the support of `marchenkoPastur y`, the resolvent transforms of
`semicircleReal (1 + y) y` and `marchenkoPastur y` are linked by
`m_{semicircleReal (1 + y) y}(z) = 1 + z * m_{MP_y}(z)`. -/
theorem resolventTransform_semicircleReal_one_add_eq
    (hz : z ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support) :
    resolventTransform (semicircleReal (1 + y) y) z =
      1 + z * resolventTransform (marchenkoPastur y) z := by
  have hint : Integrable (resolvent (R := ℝ) z) (marchenkoPastur y) :=
    integrable_resolvent (by simpa using hz)
  rw [resolventTransform_apply, ← integral_smul_marchenkoPastur y (resolvent (R := ℝ) z)]
  have hae : ∀ᵐ x : ℝ ∂marchenkoPastur y,
      x • resolvent (R := ℝ) z x = 1 + z * resolvent (R := ℝ) z x := by
    filter_upwards [Measure.support_mem_ae] with x hx
    have hxz : (x : ℂ) - z ≠ 0 := sub_ne_zero.2 fun h ↦ hz ⟨x, hx, h⟩
    rw [Complex.real_smul, Complex.resolvent_real_eq_inv]
    field_simp
    ring
  rw [integral_congr_ae hae, integral_add (integrable_const _) (hint.const_mul z),
    integral_const, probReal_univ, one_smul, integral_const_mul, ← resolventTransform_apply]

/-- Away from the real axis, `m_{semicircleReal (1 + y) y}(z) = 1 + z * m_{MP_y}(z)`. -/
theorem resolventTransform_semicircleReal_one_add_eq_of_im_ne_zero (hz : z.im ≠ 0) :
    resolventTransform (semicircleReal (1 + y) y) z =
      1 + z * resolventTransform (marchenkoPastur y) z :=
  resolventTransform_semicircleReal_one_add_eq (notMem_image_ofReal_of_im_ne_zero hz)

/-- In the upper half-plane, `z * m_{MP_y}(z)` has strictly positive imaginary part. -/
theorem im_mul_resolventTransform_marchenkoPastur_pos (hz : 0 < z.im) :
    0 < (z * resolventTransform (marchenkoPastur y) z).im := by
  have h := congrArg Complex.im
    (resolventTransform_semicircleReal_one_add_eq_of_im_ne_zero (y := y) hz.ne')
  rw [add_im, one_im, zero_add] at h
  exact h ▸ im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz

/-- The quadratic equation at nonzero points outside the support of `marchenkoPastur y`. -/
private lemma quadratic_eq_zero_of_ne_zero
    (hz : z ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support) (hz0 : z ≠ 0) :
    (y : ℂ) * z * (resolventTransform (marchenkoPastur y) z *
      resolventTransform (marchenkoPastur y) z) +
      (z + y - 1) * resolventTransform (marchenkoPastur y) z + 1 = 0 := by
  have hs_sqrt := Real.sq_sqrt y.coe_nonneg
  have hsub : Icc (1 + (y : ℝ) - 2 * √(y : ℝ)) (1 + (y : ℝ) + 2 * √(y : ℝ)) ⊆
      (marchenkoPastur y).support := by
    have hIcc : Icc (1 + (y : ℝ) - 2 * √(y : ℝ)) (1 + (y : ℝ) + 2 * √(y : ℝ)) =
        Icc ((1 - √(y : ℝ)) ^ 2) ((1 + √(y : ℝ)) ^ 2) := by
      congr 1 <;> linear_combination -hs_sqrt
    rw [hIcc, support_marchenkoPastur]
    split_ifs <;> [exact Subset.rfl; exact subset_insert _ _]
  have hz_semi : z ∉ ((↑) : ℝ → ℂ) ''
      Icc (1 + (y : ℝ) - 2 * √(y : ℝ)) (1 + (y : ℝ) + 2 * √(y : ℝ)) :=
    fun ⟨x, hx, hxz⟩ ↦ hz ⟨x, hsub hx, hxz⟩
  have hq := resolventTransform_semicircleReal_quadratic_eq_zero hz_semi
  rw [resolventTransform_semicircleReal_one_add_eq hz] at hq
  push_cast at hq
  set m := resolventTransform (marchenkoPastur y) z
  have hfac : z * ((y : ℂ) * z * (m * m) + (z + y - 1) * m + 1) = 0 := by
    linear_combination hq
  exact (mul_eq_zero.1 hfac).resolve_left hz0

/-- Off the support of `marchenkoPastur y`, its resolvent transform `m` satisfies the quadratic
equation `y * z * (m * m) + (z + y - 1) * m + 1 = 0`. -/
theorem resolventTransform_marchenkoPastur_quadratic_eq_zero
    (hz : z ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support) :
    (y : ℂ) * z * (resolventTransform (marchenkoPastur y) z *
      resolventTransform (marchenkoPastur y) z) +
      (z + y - 1) * resolventTransform (marchenkoPastur y) z + 1 = 0 := by
  rcases ne_or_eq z 0 with hz0 | rfl
  · exact quadratic_eq_zero_of_ne_zero hz hz0
  -- When `0` is outside the support, pass to the limit along `𝓝[≠] 0`.
  set U : Set ℂ := (((↑) : ℝ → ℂ) '' (marchenkoPastur y).support)ᶜ
  have hUo : IsOpen U := by
    rw [isOpen_compl_iff, ← Complex.coe_algebraMap]
    exact (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed
      (algebraMap_isometry ℝ ℂ).isClosedEmbedding).1 Measure.isClosed_support
  set F : ℂ → ℂ := fun w ↦ (y : ℂ) * w *
    (resolventTransform (marchenkoPastur y) w * resolventTransform (marchenkoPastur y) w) +
    (w + y - 1) * resolventTransform (marchenkoPastur y) w + 1
  have hm_cont : ContinuousAt (resolventTransform (marchenkoPastur y) : ℂ → ℂ) 0 :=
    (hasDerivAt_resolventTransform (0 : ℂ) (by simpa using hz)).continuousAt
  have hF_cont : ContinuousAt F 0 := by
    dsimp only [F]
    fun_prop (disch := exact hm_cont)
  have hF_zero : F =ᶠ[𝓝[≠] (0 : ℂ)] 0 :=
    eventually_nhdsWithin_iff.2 <| Filter.eventually_of_mem (hUo.mem_nhds hz) fun w hw hw0 ↦
      quadratic_eq_zero_of_ne_zero hw (mem_compl_singleton_iff.1 hw0)
  exact tendsto_nhds_unique (hF_cont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hF_zero.symm)

/-- When `y < 1`, the origin lies outside the image of `(marchenkoPastur y).support` in `ℂ`. -/
private lemma zero_notMem_image_support_of_lt_one (hy : y < 1) :
    (0 : ℂ) ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support := by
  simp [not_le.2 hy]

/-- For `y < 1`, the resolvent transform of `marchenkoPastur y` at `0` is `(1 - y)⁻¹`. -/
theorem resolventTransform_marchenkoPastur_zero_of_lt_one (hy : y < 1) :
    resolventTransform (marchenkoPastur y) (0 : ℂ) = (1 - (y : ℂ))⁻¹ := by
  have hq := resolventTransform_marchenkoPastur_quadratic_eq_zero
    (zero_notMem_image_support_of_lt_one hy)
  simp only [mul_zero, zero_mul, zero_add] at hq
  have h1y : (1 : ℂ) - y ≠ 0 := sub_ne_zero.2 <| by
    exact_mod_cast hy.ne'
  apply mul_left_cancel₀ h1y
  rw [mul_inv_cancel₀ h1y]
  linear_combination -hq

/-- For `y < 1`, the reciprocal `x⁻¹` is integrable against `marchenkoPastur y`. -/
theorem integrable_inv_marchenkoPastur (hy : y < 1) :
    Integrable (fun x : ℝ ↦ x⁻¹) (marchenkoPastur y) := by
  have hint : Integrable (resolvent (R := ℝ) (0 : ℂ)) (marchenkoPastur y) :=
    integrable_resolvent (by simpa using zero_notMem_image_support_of_lt_one hy)
  have hre := hint.re
  simpa [resolvent, Ring.inverse_eq_inv'] using hre

/-- For `y < 1`, the first negative moment of `marchenkoPastur y` is `(1 - y)⁻¹`. -/
theorem integral_inv_marchenkoPastur (hy : y < 1) :
    ∫ x, x⁻¹ ∂marchenkoPastur y = (1 - (y : ℝ))⁻¹ := by
  have h := resolventTransform_marchenkoPastur_zero_of_lt_one hy
  have hres : resolventTransform (marchenkoPastur y) (0 : ℂ) =
      ((∫ x, x⁻¹ ∂marchenkoPastur y : ℝ) : ℂ) := by
    rw [resolventTransform_apply, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [resolvent, Ring.inverse_eq_inv']
  rw [hres] at h
  exact ofReal_inj.1 (by simpa [ofReal_inv, ofReal_sub] using h)

/-- In the upper half-plane, the resolvent transform of `marchenkoPastur y` is the unique root of
`y * z * (w * w) + (z + y - 1) * w + 1 = 0` with positive imaginary part. -/
theorem eq_resolventTransform_marchenkoPastur_iff (hz : 0 < z.im) {w : ℂ} :
    w = resolventTransform (marchenkoPastur y) z ↔
      0 < w.im ∧ (y : ℂ) * z * (w * w) + (z + y - 1) * w + 1 = 0 := by
  set m := resolventTransform (marchenkoPastur y) z
  have hm : (y : ℂ) * z * (m * m) + (z + y - 1) * m + 1 = 0 :=
    resolventTransform_marchenkoPastur_quadratic_eq_zero
      (notMem_image_ofReal_of_im_ne_zero hz.ne')
  have hmim : 0 < m.im := im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz
  refine ⟨fun h ↦ h ▸ ⟨hmim, hm⟩, fun ⟨_, hw⟩ ↦ ?_⟩
  by_contra hne
  -- Any root `w ≠ m` obeys `w * (y * (z * m)) = 1`, while `Im (z * m) > 0`, forcing `Im w ≤ 0`.
  have hprod : w * ((y : ℂ) * (z * m)) = 1 := by
    have h : (w - m) * ((y : ℂ) * z * (w + m) + (z + y - 1)) = 0 := by
      linear_combination hw - hm
    have h' := (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)
    linear_combination m * h' - hm
  have hinv : w = ((y : ℂ) * (z * m))⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hzm_pos : 0 < (z * m).im := im_mul_resolventTransform_marchenkoPastur_pos hz
  have : w.im ≤ 0 := by
    rw [hinv, inv_im, im_ofReal_mul]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (mul_nonneg y.coe_nonneg hzm_pos.le))
      (normSq_nonneg _)
  linarith

/-- At `z = (1 + i) / 2`, the resolvent transform of `marchenkoPastur 1` equals `i`, the unique
root of `((1 + i) / 2) * w² + ((1 + i) / 2) * w + 1 = 0` with positive imaginary part; the other
root is `-1 - i`. -/
theorem resolventTransform_marchenkoPastur_one_one_add_I_div_two :
    resolventTransform (marchenkoPastur 1) ((1 + I) / 2) = I := by
  refine ((eq_resolventTransform_marchenkoPastur_iff (by simp)).2 ⟨by simp, ?_⟩).symm
  push_cast
  linear_combination ((1 + I) / 2 + 1 / 2) * I_sq

section Real

variable {x : ℝ}

/-- Off the support of `MP_y`, its real resolvent transform `m` satisfies the quadratic equation
`y * x * (m * m) + (x + y - 1) * m + 1 = 0`. -/
theorem resolventTransform_marchenkoPastur_real_quadratic_eq_zero
    (hx : x ∉ (marchenkoPastur y).support) :
    y * x * (resolventTransform (marchenkoPastur y) x * resolventTransform (marchenkoPastur y) x) +
      (x + y - 1) * resolventTransform (marchenkoPastur y) x + 1 = 0 := by
  have hz : (x : ℂ) ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support := by
    rintro ⟨t, ht, htx⟩
    exact hx (Complex.ofReal_injective htx ▸ ht)
  have h := resolventTransform_marchenkoPastur_quadratic_eq_zero hz
  rw [Measure.resolventTransform_ofReal] at h
  exact_mod_cast h

/-- Off the support of `MP_y`, the square of `2 y x m(x) + (x + y - 1)` is the discriminant
`(x + y - 1)² - 4 y x` of the quadratic equation of its real resolvent transform `m`. -/
private lemma two_mul_mul_resolventTransform_add_sq (hx : x ∉ (marchenkoPastur y).support) :
    (2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1)) ^ 2 =
      (x + y - 1) ^ 2 - 4 * y * x := by
  linear_combination (4 * y * x) * resolventTransform_marchenkoPastur_real_quadratic_eq_zero hx

/-- The discriminant `(x + y - 1)² - 4 y x` is positive above the upper edge of `MP_y`. -/
private lemma discr_pos (hx : (1 + √(y : ℝ)) ^ 2 < x) : 0 < (x + y - 1) ^ 2 - 4 * y * x := by
  have hr := Real.sq_sqrt y.coe_nonneg
  have hr0 := Real.sqrt_nonneg (y : ℝ)
  have hfac : (x + y - 1) ^ 2 - 4 * y * x =
      (x - (1 + √(y : ℝ)) ^ 2) * (x - (1 - √(y : ℝ)) ^ 2) := by
    linear_combination (2 * x + 2 - y - √(y : ℝ) ^ 2) * hr
  rw [hfac]
  exact mul_pos (by linarith) (by nlinarith)

/-- Far above the upper edge of `MP_y`, at `x ≥ 2 (1 + √y)² + 3 y + 1`, the quantity
`2 y x m(x) + (x + y - 1)` is positive. -/
private lemma two_mul_mul_resolventTransform_add_pos_of_far
    (hx : 2 * (1 + √(y : ℝ)) ^ 2 + 3 * y + 1 ≤ x) :
    0 < 2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1) := by
  set e := (1 + √(y : ℝ)) ^ 2
  have he : 1 ≤ e := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
  have hy := y.coe_nonneg
  have hb : ∀ᵐ t ∂marchenkoPastur y, t ≤ e := by
    filter_upwards [ae_mem_Icc_zero_marchenkoPastur y] with t ht using ht.2
  have hex : e < x := by linarith
  set m := resolventTransform (marchenkoPastur y) x
  have hm0 : m ≤ 0 := resolventTransform_nonpos_of_ae_le hb hex
  have hlow : -(x - e)⁻¹ ≤ m := by
    simpa [div_eq_mul_inv] using neg_div_sub_le_resolventTransform_of_ae_le hb hex
  have hd : 0 < x - e := sub_pos.2 hex
  have hmd : -1 ≤ m * (x - e) := by
    have := mul_le_mul_of_nonneg_right hlow hd.le
    rwa [neg_mul, inv_mul_cancel₀ hd.ne'] at this
  have hxd : x - 2 * (x - e) ≤ 0 := by linarith
  nlinarith [mul_nonneg hy (mul_nonneg_of_nonpos_of_nonpos hxd hm0),
    mul_le_mul_of_nonneg_left hmd hy]

/-- Above the upper edge of `MP_y`, its real resolvent transform `m` lies strictly to the right of
the midpoint of the two roots of its quadratic equation: `0 < 2 y x m(x) + (x + y - 1)`. -/
theorem two_mul_mul_resolventTransform_marchenkoPastur_add_pos (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    0 < 2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1) := by
  set φ : ℝ → ℝ := fun x ↦ 2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1)
  have hcont : ContinuousOn φ (Ioi ((1 + √(y : ℝ)) ^ 2)) := by
    have hm : ContinuousOn (resolventTransform (marchenkoPastur y) : ℝ → ℝ)
        (Ioi ((1 + √(y : ℝ)) ^ 2)) := fun x hx ↦
      (hasDerivAt_resolventTransform x (by simpa using notMem_support_marchenkoPastur_of_lt hx))
        |>.continuousAt.continuousWithinAt
    fun_prop
  -- `φ` is positive far above the edge and, squaring to the positive discriminant, has no zero
  -- above the edge, so it is positive everywhere above the edge.
  have hfar : 2 * (1 + √(y : ℝ)) ^ 2 + 3 * y + 1 ∈ Ioi ((1 + √(y : ℝ)) ^ 2) := by
    have : 0 ≤ (1 + √(y : ℝ)) ^ 2 := sq_nonneg _
    simp only [mem_Ioi]
    linarith [y.coe_nonneg]
  by_contra! hneg
  obtain ⟨x', hx', h0⟩ := isPreconnected_Ioi.intermediate_value hx hfar hcont
    ⟨hneg, (two_mul_mul_resolventTransform_add_pos_of_far le_rfl).le⟩
  have hsq := two_mul_mul_resolventTransform_add_sq (notMem_support_marchenkoPastur_of_lt hx')
  rw [show 2 * y * x' * resolventTransform (marchenkoPastur y) x' + (x' + y - 1) = 0 from h0]
    at hsq
  linarith [discr_pos (y := y) hx']

/-- Above the upper edge of `MP_y`, its real resolvent transform `m` is the root of
`y x m² + (x + y - 1) m + 1 = 0` given by `2 y x m + (x + y - 1) = √((x + y - 1)² - 4 y x)`: for
`y > 0` this is `m(x) = (√((x + y - 1)² - 4 y x) - (x + y - 1)) / (2 y x)`. -/
theorem two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt
    (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1) =
      √((x + y - 1) ^ 2 - 4 * y * x) := by
  rw [← two_mul_mul_resolventTransform_add_sq (notMem_support_marchenkoPastur_of_lt hx),
    Real.sqrt_sq (two_mul_mul_resolventTransform_marchenkoPastur_add_pos hx).le]

end Real

end TauCeti.Probability
