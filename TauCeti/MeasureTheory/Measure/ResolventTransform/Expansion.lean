/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Moment expansion of the resolvent transform at infinity

For a finite measure `μ` on `ℝ` and `z : ℂ` off the real axis, the resolvent transform
`m_μ(z) = ∫ (x - z)⁻¹ dμ(x)` is Mathlib's `MeasureTheory.resolventTransform` with base field `ℝ`
and values in `ℂ`. If `∫ |x| ^ r dμ < ∞`, then with the moments `m_k = ∫ x ^ k dμ` it has the
finite expansion

`m_μ(z) = -∑_{k < r} m_k z^{-(k+1)} + z^{-r} ∫ x ^ r (x - z)⁻¹ dμ(x)`,

whose remainder is bounded by `∫ |x| ^ r dμ / (|z| ^ r |Im z|)`. Along the imaginary axis the
remainder is `-m_r (iy)^{-(r+1)} + o(y^{-(r+1)})` as `y → ∞`. For `r = 0` this is the total-mass
asymptotic `iy m_μ(iy) → -μ(ℝ)`, which requires no moment assumption.

These expansions are the link between the moments of a measure and its resolvent transform at
infinity, used when the moment method and the resolvent method are compared for spectral measures.

## Main statements

* `MeasureTheory.resolventTransform_add_sum_eq`: the exact expansion, with integral remainder.
* `MeasureTheory.norm_resolventTransform_add_sum_le`: the bound on the remainder.
* `MeasureTheory.tendsto_mul_I_pow_mul_resolventTransform_add_sum`: the sharp asymptotic of the
  remainder along the imaginary axis.
* `MeasureTheory.tendsto_mul_I_mul_resolventTransform`: the total-mass asymptotic.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1 and Appendix B.
-/

public section

noncomputable section

open Complex Filter Finset
open scoped Topology

namespace MeasureTheory

variable {μ : Measure ℝ}

/-- The geometric expansion of the real resolvent kernel in powers of `z⁻¹`. -/
private lemma resolvent_add_sum_eq {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) (r : ℕ) :
    resolvent z x + ∑ k ∈ range r, (x : ℂ) ^ k * z⁻¹ ^ (k + 1) =
      z⁻¹ ^ r * ((x : ℂ) ^ r * resolvent z x) := by
  have hz₀ : z ≠ 0 := fun h ↦ hz (by simp [h])
  have hxz : (x : ℂ) - z ≠ 0 := fun h ↦ hz (by simpa using (congrArg Complex.im h).symm)
  have hg := geom_sum_mul ((x : ℂ) * z⁻¹) r
  simp_rw [pow_succ, ← mul_assoc, ← sum_mul, ← mul_pow]
  rw [resolvent, Ring.inverse_eq_inv', coe_algebraMap]
  field_simp at hg ⊢
  linear_combination hg

/-- **Finite moment expansion of the resolvent transform.** If `μ` is a finite measure on `ℝ`
with finite `r`th absolute moment and `z` is off the real axis, then
`m_μ(z) + ∑_{k < r} m_k z^{-(k+1)} = z^{-r} ∫ x ^ r (x - z)⁻¹ dμ(x)`. -/
theorem resolventTransform_add_sum_eq [IsFiniteMeasure μ] {r : ℕ}
    (hr : Integrable (fun x : ℝ ↦ x ^ r) μ) {z : ℂ} (hz : z.im ≠ 0) :
    resolventTransform μ z + ∑ k ∈ range r, ((∫ x, x ^ k ∂μ : ℝ) : ℂ) * z⁻¹ ^ (k + 1) =
      z⁻¹ ^ r * ∫ x, (x : ℂ) ^ r * resolvent z x ∂μ := by
  have hk (k : ℕ) (hk : k ∈ range r) :
      Integrable (fun x : ℝ ↦ (x : ℂ) ^ k * z⁻¹ ^ (k + 1)) μ := by
    -- The `r`th absolute moment controls the lower ones, since `μ` is finite.
    have hnorm := integrable_norm_pow_of_le (f := id) aestronglyMeasurable_id
      (mem_range.1 hk).le (by simpa only [id, norm_pow] using hr.norm)
    refine (hnorm.ofReal (𝕜 := ℂ)).mul_const (z⁻¹ ^ (k + 1)) |>.mono (by fun_prop)
      (ae_of_all _ fun x ↦ ?_)
    simp
  have hsum (k : ℕ) : ((∫ x, x ^ k ∂μ : ℝ) : ℂ) * z⁻¹ ^ (k + 1) =
      ∫ x, (x : ℂ) ^ k * z⁻¹ ^ (k + 1) ∂μ := by
    rw [integral_mul_const, ← integral_complex_ofReal]
    push_cast
    rfl
  simp_rw [hsum, resolventTransform_apply, ← integral_finsetSum _ hk,
    ← integral_add (integrable_resolvent_of_im_ne_zero hz) (integrable_finsetSum _ hk),
    ← integral_const_mul, resolvent_add_sum_eq hz]

/-- The remainder integral `∫ x ^ r (x - z)⁻¹ dμ(x)` is bounded by `∫ |x| ^ r dμ / |Im z|`. -/
theorem norm_integral_pow_mul_resolvent_le {r : ℕ} (hr : Integrable (fun x : ℝ ↦ x ^ r) μ)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖∫ x, (x : ℂ) ^ r * resolvent z x ∂μ‖ ≤ (∫ x, |x| ^ r ∂μ) / |z.im| := by
  rw [← integral_div]
  have habs : Integrable (fun x : ℝ ↦ |x| ^ r) μ := by
    simpa only [Real.norm_eq_abs, abs_pow] using hr.norm
  refine norm_integral_le_of_norm_le (habs.div_const _) (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, div_eq_mul_inv, resolvent,
    Ring.inverse_eq_inv', norm_inv]
  gcongr
  simpa using abs_im_le_norm ((x : ℂ) - z)

/-- **Remainder bound for the moment expansion.** If `μ` is a finite measure on `ℝ` with finite
`r`th absolute moment and `z` is off the real axis, then
`‖m_μ(z) + ∑_{k < r} m_k z^{-(k+1)}‖ ≤ ∫ |x| ^ r dμ / (|z| ^ r |Im z|)`. -/
theorem norm_resolventTransform_add_sum_le [IsFiniteMeasure μ] {r : ℕ}
    (hr : Integrable (fun x : ℝ ↦ x ^ r) μ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform μ z + ∑ k ∈ range r, ((∫ x, x ^ k ∂μ : ℝ) : ℂ) * z⁻¹ ^ (k + 1)‖ ≤
      (∫ x, |x| ^ r ∂μ) / (‖z‖ ^ r * |z.im|) := by
  rw [resolventTransform_add_sum_eq hr hz, norm_mul, norm_pow, norm_inv, mul_comm (‖z‖ ^ r),
    ← div_div, div_eq_inv_mul _ (‖z‖ ^ r), inv_pow]
  gcongr
  exact norm_integral_pow_mul_resolvent_le hr hz

/-- Along the imaginary axis, `iy (x - iy)⁻¹` tends to `-1` as `y → ∞`. -/
private lemma tendsto_mul_I_mul_resolvent (x : ℝ) :
    Tendsto (fun y : ℝ ↦ y * I * resolvent (y * I) x) atTop (𝓝 (-1)) := by
  have hinv : Tendsto (fun y : ℝ ↦ (y : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  have h : Tendsto (fun y : ℝ ↦ I / ((x : ℂ) * (y : ℂ)⁻¹ - I)) atTop (𝓝 (-1)) := by
    simpa [Pi.div_def] using tendsto_const_nhds (x := I) |>.div
      ((tendsto_const_nhds (x := (x : ℂ))).mul hinv |>.sub (tendsto_const_nhds (x := I)))
      (by simp)
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with y hy
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy
  have hxz : (x : ℂ) - y * I ≠ 0 := fun h ↦ hy (by simpa using (congrArg Complex.im h).symm)
  rw [resolvent, Ring.inverse_eq_inv', coe_algebraMap]
  field_simp

/-- **Sharp remainder asymptotic along the imaginary axis.** If `μ` is a finite measure on `ℝ`
with finite `r`th absolute moment, then
`(iy) ^ (r + 1) (m_μ(iy) + ∑_{k < r} m_k (iy)^{-(k+1)}) → -m_r` as `y → ∞`; that is,
`m_μ(iy) = -∑_{k ≤ r} m_k (iy)^{-(k+1)} + o(y^{-(r+1)})`. -/
theorem tendsto_mul_I_pow_mul_resolventTransform_add_sum [IsFiniteMeasure μ] {r : ℕ}
    (hr : Integrable (fun x : ℝ ↦ x ^ r) μ) :
    Tendsto (fun y : ℝ ↦ (y * I) ^ (r + 1) * (resolventTransform μ (y * I) +
        ∑ k ∈ range r, ((∫ x, x ^ k ∂μ : ℝ) : ℂ) * (y * I)⁻¹ ^ (k + 1)))
      atTop (𝓝 (-((∫ x, x ^ r ∂μ : ℝ) : ℂ))) := by
  have hlim : Tendsto (fun y : ℝ ↦ ∫ x, (x : ℂ) ^ r * (y * I * resolvent (y * I) x) ∂μ) atTop
      (𝓝 (∫ x, (x : ℂ) ^ r * (-1) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ |x| ^ r)
      (Eventually.of_forall fun y ↦ by fun_prop) ?_
      (by simpa only [Real.norm_eq_abs, abs_pow] using hr.norm)
      (ae_of_all _ fun x ↦ tendsto_const_nhds.mul (tendsto_mul_I_mul_resolvent x))
    filter_upwards [eventually_ne_atTop 0] with y hy
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, resolvent, Ring.inverse_eq_inv',
      norm_mul, norm_inv, ← div_eq_mul_inv]
    refine mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ ?_ (norm_nonneg _))
    simpa using abs_im_le_norm ((x : ℂ) - y * I)
  have hval : ∫ x, (x : ℂ) ^ r * (-1) ∂μ = -((∫ x, x ^ r ∂μ : ℝ) : ℂ) := by
    rw [integral_mul_const, ← integral_complex_ofReal]
    push_cast
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with y hy
  have hz : (y * I : ℂ).im ≠ 0 := by simpa using hy
  have hyI : ((y : ℂ) * I) ^ r ≠ 0 := pow_ne_zero _ (by simpa using hy)
  rw [resolventTransform_add_sum_eq hr hz]
  calc _ = ∫ x, y * I * ((x : ℂ) ^ r * resolvent (y * I) x) ∂μ := by congr 1; ext x; ring
    _ = _ := by rw [integral_const_mul, inv_pow, pow_succ]; field_simp

/-- **Total-mass asymptotic of the resolvent transform.** For every finite measure `μ` on `ℝ`,
`iy m_μ(iy) → -μ(ℝ)` as `y → ∞`. -/
theorem tendsto_mul_I_mul_resolventTransform [IsFiniteMeasure μ] :
    Tendsto (fun y : ℝ ↦ y * I * resolventTransform μ (y * I)) atTop
      (𝓝 (-(μ.real Set.univ : ℂ))) := by
  simpa using tendsto_mul_I_pow_mul_resolventTransform_add_sum (μ := μ) (r := 0) (by simp)

end MeasureTheory
