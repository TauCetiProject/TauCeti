/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import TauCeti.Probability.Distributions.Semicircle.ResolventTransform

/-!
# The resolvent transform of the Marchenko–Pastur law

For an aspect ratio `y ≥ 0`, the resolvent transform
`m(z) = ∫ (x - z)⁻¹ d(marchenkoPastur y)(x)` (Mathlib's `MeasureTheory.resolventTransform` with
base field `ℝ` and values in `ℂ`) satisfies the Marchenko–Pastur quadratic equation

`y * z * (m(z) * m(z)) + (z + y - 1) * m(z) + 1 = 0`

at every `z : ℂ` outside the support of `marchenkoPastur y`. In the upper half-plane `m(z)` is the
unique root with positive imaginary part: the other root is `(y * z * m(z))⁻¹`, while the
size-biasing relation `1 + z * m(z) = m_{semicircleReal (1 + y) y}(z)` shows that `z * m(z)` also
has positive imaginary part in the upper half-plane, forcing `(y * z * m(z))⁻¹` into the closed
lower half-plane.

For `y < 1`, the origin lies outside the support `[(1 - √y)², (1 + √y)²]`, and evaluating the
quadratic equation at `z = 0` yields `m(0) = (1 - y)⁻¹`, that is,
`∫ x⁻¹ d(marchenkoPastur y)(x) = (1 - y)⁻¹`.

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
    rw [Complex.real_smul, resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
    field_simp
    ring
  rw [integral_congr_ae hae, integral_add (integrable_const _) (hint.const_mul z),
    integral_const, probReal_univ, one_smul, integral_const_mul, ← resolventTransform_apply]

/-- Away from the real axis, `m_{semicircleReal (1 + y) y}(z) = 1 + z * m_{MP_y}(z)`. -/
theorem resolventTransform_semicircleReal_one_add_eq_of_im_ne_zero (hz : z.im ≠ 0) :
    resolventTransform (semicircleReal (1 + y) y) z =
      1 + z * resolventTransform (marchenkoPastur y) z :=
  resolventTransform_semicircleReal_one_add_eq fun ⟨x, _, hx⟩ ↦
    hz (by simpa using (congrArg Complex.im hx).symm)

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
  have hzU : z ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support := by
    rintro ⟨x, -, rfl⟩
    simp at hz
  have hm : (y : ℂ) * z * (m * m) + (z + y - 1) * m + 1 = 0 :=
    resolventTransform_marchenkoPastur_quadratic_eq_zero hzU
  have hmim : 0 < m.im := im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz
  refine ⟨fun h ↦ h ▸ ⟨hmim, hm⟩, fun ⟨hwim, hw⟩ ↦ ?_⟩
  by_contra hne
  -- The second root satisfies `w * (y * (z * m)) = 1`, while `Im (z * m) > 0`, forcing `Im w ≤ 0`.
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

end TauCeti.Probability
