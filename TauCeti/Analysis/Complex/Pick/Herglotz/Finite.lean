/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Herglotz.Basic
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Herglotz representations with a decaying imaginary-axis bound

Let `F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` on the upper half-plane be a Herglotz
representation (`TauCeti.exists_eq_subtractedResolventKernel_add`). If `y |Im F(i y)|` stays
bounded as `y → ∞`, then

* the linear coefficient vanishes, `b = 0` (this needs only `Im F(i y) / y → 0`);
* `ν` is a finite measure when it has finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`, as in the
  Herglotz representation, and then its total mass is `ν(ℝ) = lim y Im F(i y)`.

If moreover `y ‖F(i y)‖` stays bounded, as it does for the function `⟪v, (A - z)⁻¹ v⟫` of a
self-adjoint operator `A`, then `F` is the resolvent transform of `ν`: `F z = ∫ (t - z)⁻¹ dν(t)`.
Without finite weighted mass, the real total mass `ν.real univ` and the integral are zero by
convention, and the statements still hold.

Finiteness follows from `y Im F(i y) = ∫ y ^ 2 / (t ^ 2 + y ^ 2) dν(t)` by Fatou's lemma, and the
total mass is then the total-mass asymptotic `MeasureTheory.tendsto_mul_I_mul_resolventTransform`.
For the resolvent transform, a finite `ν` splits the subtracted kernel, so
`F z = c + ∫ (t - z)⁻¹ dν(t)` for a constant `c`, and both `F(i y)` and the transform tend to `0`.

## Main results

* `TauCeti.eq_zero_of_eq_subtractedResolventKernel_add_of_tendsto`: `b = 0` as soon as
  `Im F(i y) / y → 0`, and `TauCeti.eq_zero_of_eq_subtractedResolventKernel_add_of_bound` under
  the bound on `y |Im F(i y)|`.
* `TauCeti.isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound`: `ν` is finite when it
  has finite weighted mass.
* `TauCeti.tendsto_mul_im_of_eq_subtractedResolventKernel_add_of_bound`:
  `y Im F(i y) → ν.real univ`.
* `TauCeti.integral_subtractedResolventKernel_eq`: for finite `ν`, the unsubtracted form
  `∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t) = ∫ (t - z)⁻¹ dν(t) - ∫ t / (1 + t ^ 2) dν(t)`.
* `TauCeti.eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound`:
  `F z = ∫ (t - z)⁻¹ dν(t)` on the upper half-plane.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, §3.4, Theorem 3.20 (finiteness of the
  measure and the resolvent-transform form) and Theorem 3.21 (the total-mass limit).
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology

namespace TauCeti

variable {F : ℂ → ℂ} {a b C : ℝ} {nu : Measure ℝ}

/-- If `Im F(i y) / y → 0` as `y → ∞`, the linear coefficient of a Herglotz representation of `F`
vanishes. -/
theorem eq_zero_of_eq_subtractedResolventKernel_add_of_tendsto
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (h : Tendsto (fun y : ℝ ↦ (F (y * I)).im / y) atTop (𝓝 0)) : b = 0 :=
  tendsto_nhds_unique (tendsto_im_div_of_eq_subtractedResolventKernel_add hrep) h

/-- If `y |Im F(i y)|` is eventually bounded, the linear coefficient of a Herglotz representation
of `F` vanishes. -/
theorem eq_zero_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * |(F (y * I)).im| ≤ C) : b = 0 := by
  refine eq_zero_of_eq_subtractedResolventKernel_add_of_tendsto hrep ?_
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero) :
    Tendsto (fun y : ℝ ↦ C / y ^ 2) atTop (𝓝 0))
  filter_upwards [hbound, eventually_gt_atTop 0] with y hy hy0
  rw [norm_div, Real.norm_of_nonneg hy0.le, div_le_div_iff₀ hy0 (by positivity),
    Real.norm_eq_abs]
  nlinarith

/-- On the imaginary axis, a Herglotz representation gives
`y Im F(i y) = b y ^ 2 + ∫ y ^ 2 / (t ^ 2 + y ^ 2) dν(t)`. -/
theorem mul_im_eq_of_eq_subtractedResolventKernel_add
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) {y : ℝ} (hy : 0 < y) :
    y * (F (y * I)).im = b * y ^ 2 + ∫ t, y ^ 2 / (t ^ 2 + y ^ 2) ∂nu := by
  have hz : (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using hy
  rw [hrep _ hz]
  have him : (∫ t, subtractedResolventKernel (y * I) t ∂nu).im = ∫ t, y / (t ^ 2 + y ^ 2) ∂nu := by
    simp_rw [← subtractedResolventKernel_ofReal_mul_I_im y]
    by_cases hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤
    · simpa only [RCLike.im_to_complex] using
        (integral_im (integrable_subtractedResolventKernel hnu (ne_of_gt hz))).symm
    · rw [integral_subtractedResolventKernel_eq_zero hnu (ne_of_gt hz),
        integral_im_subtractedResolventKernel_eq_zero hnu (ne_of_gt hz), zero_im]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add, him]
  rw [mul_add, ← integral_const_mul]
  congr 1
  · ring
  · congr 1 with t
    ring

/-- If `y |Im F(i y)|` is eventually bounded, the measure `ν` of a Herglotz representation of `F`
of finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν < ∞` is finite. -/
theorem isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound
    (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * |(F (y * I)).im| ≤ C) : IsFiniteMeasure nu := by
  have hb := eq_zero_of_eq_subtractedResolventKernel_add_of_bound hrep hbound
  subst hb
  let g : ℕ → ℝ → ℝ := fun n t ↦ ((n : ℝ) + 1) ^ 2 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)
  have hg0 (n : ℕ) (t : ℝ) : 0 ≤ g n t := by positivity
  have hgi (n : ℕ) : Integrable (g n) nu := by
    have hz : (((n : ℝ) + 1 : ℝ) : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simpa using (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    refine ((integrable_subtractedResolventKernel hnu (ne_of_gt hz)).im.const_mul
      ((n : ℝ) + 1)).congr (.of_forall fun t ↦ ?_)
    simp only [RCLike.im_to_complex, subtractedResolventKernel_ofReal_mul_I_im, g]
    ring
  have hlim (t : ℝ) : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (g n t)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal ((Real.tendsto_sq_div_sq_add_sq_atTop t).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hle : ∀ᶠ n : ℕ in atTop, ∫⁻ t, ENNReal.ofReal (g n t) ∂nu ≤ ENNReal.ofReal C := by
    have hN := tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
    filter_upwards [hN.eventually hbound] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (.of_forall (hg0 n))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := mul_im_eq_of_eq_subtractedResolventKernel_add hrep
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    simp only [zero_mul, zero_add] at h
    rw [← h]
    refine (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans ?_
    exact_mod_cast hn
  refine ⟨?_⟩
  calc nu Set.univ = ∫⁻ t, Filter.liminf (fun n ↦ ENNReal.ofReal (g n t)) atTop ∂nu := by
        simp [(hlim _).liminf_eq]
    _ ≤ Filter.liminf (fun n ↦ ∫⁻ t, ENNReal.ofReal (g n t) ∂nu) atTop :=
        lintegral_liminf_le fun n ↦ by fun_prop
    _ ≤ ENNReal.ofReal C := Filter.liminf_le_of_frequently_le' hle.frequently
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- If `y |Im F(i y)|` is eventually bounded, the real total mass `ν.real univ` of the measure of
a Herglotz representation of `F` is `lim y Im F(i y)`. This is the total mass `ν(ℝ)` when `ν` has
finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν < ∞`; otherwise both sides are `0`. -/
theorem tendsto_mul_im_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * |(F (y * I)).im| ≤ C) :
    Tendsto (fun y : ℝ ↦ y * (F (y * I)).im) atTop (𝓝 (nu.real Set.univ)) := by
  have hb := eq_zero_of_eq_subtractedResolventKernel_add_of_bound hrep hbound
  subst hb
  have heq : (fun y : ℝ ↦ ∫ t, y ^ 2 / (t ^ 2 + y ^ 2) ∂nu) =ᶠ[atTop]
      fun y : ℝ ↦ y * (F (y * I)).im := by
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp [mul_im_eq_of_eq_subtractedResolventKernel_add hrep hy]
  refine Tendsto.congr' heq ?_
  by_cases hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤
  swap
  · -- Without finite weighted mass, `ν` is infinite and the integrals vanish.
    have htop : nu Set.univ = ⊤ := by
      by_contra h
      have : IsFiniteMeasure nu := ⟨lt_top_iff_ne_top.mpr h⟩
      exact hnu (lintegral_inv_one_add_sq_lt_top nu)
    rw [measureReal_def, htop, ENNReal.toReal_top]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : ((y : ℂ) * I).im ≠ 0 := by simpa using hy.ne'
    calc (0 : ℝ) = y * ∫ t, (subtractedResolventKernel (y * I) t).im ∂nu := by
          rw [integral_im_subtractedResolventKernel_eq_zero hnu hz, mul_zero]
      _ = _ := by
          rw [← integral_const_mul]
          congr 1 with t
          rw [subtractedResolventKernel_ofReal_mul_I_im]
          ring
  -- With finite weighted mass, `ν` is finite and this is the total-mass asymptotic.
  have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep hbound
  have h := ((continuous_re.tendsto _).comp
    (tendsto_mul_I_mul_resolventTransform (μ := nu))).neg
  refine (by simpa using h : Tendsto (fun y : ℝ ↦ -(y * I * resolventTransform nu (y * I)).re)
    atTop (𝓝 (nu.real Set.univ))).congr fun y ↦ ?_
  have hm := mul_im_resolventTransform (μ := nu) (a := 0) (η := y)
  simp only [ofReal_zero, zero_add, sub_zero] at hm
  simp [← hm]

/-- **The unsubtracted form.** For a finite measure `ν` and a nonreal `z`, the integral of the
subtracted resolvent kernel splits as
`∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t) = ∫ (t - z)⁻¹ dν(t) - ∫ t / (1 + t ^ 2) dν(t)`. -/
theorem integral_subtractedResolventKernel_eq [IsFiniteMeasure nu] {z : ℂ} (hz : z.im ≠ 0) :
    ∫ t, subtractedResolventKernel z t ∂nu =
      resolventTransform nu z - ∫ t, (t : ℂ) / (1 + (t : ℂ) ^ 2) ∂nu := by
  have hcast (t : ℝ) : (t : ℂ) / (1 + (t : ℂ) ^ 2) = ((t / (1 + t ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  have hr : Integrable (fun t : ℝ ↦ t / (1 + t ^ 2)) nu := by
    refine (integrable_const (1 : ℝ)).mono'
      (by fun_prop : Measurable fun t : ℝ ↦ t / (1 + t ^ 2)).aestronglyMeasurable
      (.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2),
      div_le_one (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  have hint : Integrable (fun t : ℝ ↦ (t : ℂ) / (1 + (t : ℂ) ^ 2)) nu :=
    hr.ofReal.congr (.of_forall fun t ↦ (hcast t).symm)
  have hi : Integrable (fun t : ℝ ↦ ((t : ℂ) - z)⁻¹) nu :=
    (integrable_resolvent_of_im_ne_zero (μ := nu) hz).congr
      (.of_forall fun t ↦ resolvent_real_eq_inv z t)
  have hk : (fun t ↦ subtractedResolventKernel z t) =
      fun t : ℝ ↦ ((t : ℂ) - z)⁻¹ - (t : ℂ) / (1 + (t : ℂ) ^ 2) :=
    funext fun t ↦ subtractedResolventKernel_def z t
  rw [resolventTransform_apply, hk, integral_sub hi hint]
  simp_rw [resolvent_real_eq_inv]

/-- **The resolvent case.** If `y ‖F(i y)‖` is eventually bounded, a function with a Herglotz
representation with measure `ν` is the resolvent transform `∫ (t - z)⁻¹ dν(t)` of `ν` on the upper
half-plane. -/
theorem eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) :
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, F z = resolventTransform nu z := by
  have him : ∀ᶠ y : ℝ in atTop, y * |(F (y * I)).im| ≤ C :=
    eventually_mul_abs_im_le_of_mul_norm_le hbound
  have hb := eq_zero_of_eq_subtractedResolventKernel_add_of_bound hrep him
  subst hb
  -- `F` is a constant plus the transform, which vanishes along the imaginary axis.
  obtain ⟨c, hrep', hm⟩ : ∃ c : ℂ, (∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = c + resolventTransform nu z) ∧
      Tendsto (fun y : ℝ ↦ resolventTransform nu (y * I)) atTop (𝓝 0) := by
    by_cases hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤
    · have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep him
      refine ⟨a - ∫ t, (t : ℂ) / (1 + (t : ℂ) ^ 2) ∂nu, fun z hz ↦ ?_, ?_⟩
      · rw [hrep z hz, integral_subtractedResolventKernel_eq (ne_of_gt hz)]
        push_cast
        ring
      refine tendsto_zero_of_eventually_mul_norm_le (K := nu.real Set.univ) tendsto_id ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact mul_norm_resolventTransform_ofReal_mul_I_le hy
    · -- Without finite weighted mass, neither kernel is integrable.
      refine ⟨a, fun z hz ↦ ?_, tendsto_const_nhds.congr' ?_⟩
      · rw [hrep z hz, integral_subtractedResolventKernel_eq_zero hnu (ne_of_gt hz),
          resolventTransform_eq_zero_of_not_lintegral_lt_top hnu (ne_of_gt hz)]
        simp
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (resolventTransform_eq_zero_of_not_lintegral_lt_top hnu
          (by simpa using hy.ne')).symm
  suffices hc : c = 0 by
    intro z hz
    rw [hrep' z hz, hc, zero_add]
  have hF : Tendsto (fun y : ℝ ↦ F (y * I)) atTop (𝓝 0) :=
    tendsto_zero_of_eventually_mul_norm_le tendsto_id hbound
  have hc : Tendsto (fun y : ℝ ↦ F (y * I) - resolventTransform nu (y * I)) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [hrep' _ (by simpa using hy)]
      ring)
  simpa using tendsto_nhds_unique hc (by simpa using hF.sub hm)

end TauCeti
