/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Herglotz
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic

/-!
# Herglotz representations with a decaying imaginary-axis bound

Let `F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` on the upper half-plane be a Herglotz
representation (`TauCeti.exists_eq_subtractedResolventKernel_add`). If `y ‖F(i y)‖` stays bounded
as `y → ∞`, as it does for the function `⟪v, (A - z)⁻¹ v⟫` of a self-adjoint operator `A`, then

* the linear coefficient vanishes, `b = 0`;
* `ν` has total mass `ν(ℝ) = lim y Im F(i y)`, and it is a finite measure when it has finite
  weighted mass `∫ (1 + t ^ 2)⁻¹ dν`, as in the Herglotz representation;
* `F` is the resolvent transform of `ν`: `F z = ∫ (t - z)⁻¹ dν(t)`.

Without finite weighted mass, the integrals in the last two points are zero by convention.

The second point follows from `y Im F(i y) = ∫ y ^ 2 / (t ^ 2 + y ^ 2) dν(t)` by Fatou's lemma and
then by dominated convergence. For the third, a finite `ν` splits the subtracted kernel, so
`F z = c + ∫ (t - z)⁻¹ dν(t)` for a constant `c`, and both `F(i y)` and the transform tend to `0`.

## Main results

* `TauCeti.eq_zero_of_eq_subtractedResolventKernel_add_of_bound`: `b = 0`.
* `TauCeti.isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound`: `ν` is finite.
* `TauCeti.tendsto_mul_im_of_eq_subtractedResolventKernel_add_of_bound`:
  `y Im F(i y) → ν(ℝ)`.
* `TauCeti.eq_add_resolventTransform_of_eq_subtractedResolventKernel_add`: for finite `ν`, the
  unsubtracted form `F z = c + b z + ∫ (t - z)⁻¹ dν(t)`.
* `TauCeti.eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound`:
  `F z = ∫ (t - z)⁻¹ dν(t)` on the upper half-plane.

## References

* TauCetiRoadmap, `AutomorphicSpectralTheory/README.md`, §0.5 (Herglotz representation, the
  resolvent case).
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology

namespace TauCeti

variable {F : ℂ → ℂ} {a b C : ℝ} {nu : Measure ℝ}

/-- `y ^ 2 / (t ^ 2 + y ^ 2) → 1` as `y → ∞`. -/
private theorem tendsto_sq_div_sq_add_sq (t : ℝ) :
    Tendsto (fun y : ℝ ↦ y ^ 2 / (t ^ 2 + y ^ 2)) atTop (𝓝 1) := by
  have hd : Tendsto (fun y : ℝ ↦ t ^ 2 + y ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h : Tendsto (fun y : ℝ ↦ 1 - t ^ 2 / (t ^ 2 + y ^ 2)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := t ^ 2)).div_atTop hd)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have : 0 < t ^ 2 + y ^ 2 := by positivity
  field_simp
  ring

/-- On the imaginary axis, the imaginary part of the subtracted resolvent kernel is
`y / (t ^ 2 + y ^ 2)`. -/
theorem subtractedResolventKernel_ofReal_mul_I_im (y t : ℝ) :
    (subtractedResolventKernel (y * I) t).im = y / (t ^ 2 + y ^ 2) := by
  rw [subtractedResolventKernel_im, normSq_apply]
  simp
  ring_nf

/-- If the imaginary part of the subtracted resolvent kernel at a nonreal point is `ν`-integrable,
then `ν` has finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. -/
private theorem lintegral_lt_top_of_integrable_im {z : ℂ} (hz : z.im ≠ 0)
    (h : Integrable (fun t ↦ (subtractedResolventKernel z t).im) nu) :
    ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ := by
  refine Integrable.lintegral_lt_top ?_
  refine (h.norm.const_mul (2 * (1 + ‖z‖ ^ 2) / |z.im|)).mono' (by fun_prop)
    (.of_forall fun t ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  exact inv_one_add_sq_le_mul_abs_im_subtractedResolventKernel hz t

/-- If `y ‖F(i y)‖` is eventually bounded, the linear coefficient of a Herglotz representation of
`F` vanishes. -/
theorem eq_zero_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) : b = 0 := by
  refine tendsto_nhds_unique (tendsto_im_div_of_eq_subtractedResolventKernel_add hrep) ?_
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero) :
    Tendsto (fun y : ℝ ↦ C / y ^ 2) atTop (𝓝 0))
  filter_upwards [hbound, eventually_gt_atTop 0] with y hy hy0
  rw [norm_div, Real.norm_of_nonneg hy0.le, div_le_div_iff₀ hy0 (by positivity)]
  have := abs_im_le_norm (F (y * I))
  rw [Real.norm_eq_abs]
  nlinarith

/-- On the imaginary axis, a Herglotz representation gives
`y Im F(i y) = b y ^ 2 + ∫ y ^ 2 / (t ^ 2 + y ^ 2) dν(t)`. -/
theorem mul_im_eq_of_eq_subtractedResolventKernel_add
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) {y : ℝ} (hy : 0 < y) :
    y * (F (y * I)).im = b * y ^ 2 + ∫ t, y ^ 2 / (t ^ 2 + y ^ 2) ∂nu := by
  have hz : (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using hy
  have hK : ∀ t, (subtractedResolventKernel (y * I) t).im = y / (t ^ 2 + y ^ 2) :=
    subtractedResolventKernel_ofReal_mul_I_im y
  rw [hrep _ hz]
  have him : (∫ t, subtractedResolventKernel (y * I) t ∂nu).im = ∫ t, y / (t ^ 2 + y ^ 2) ∂nu := by
    by_cases hi : Integrable (subtractedResolventKernel (y * I)) nu
    · rw [← RCLike.im_to_complex, ← integral_im hi]
      simp_rw [RCLike.im_to_complex, hK]
    · rw [integral_undef hi, integral_undef fun h ↦ hi (integrable_subtractedResolventKernel
        (lintegral_lt_top_of_integrable_im (ne_of_gt hz) (h.congr (.of_forall fun t ↦
          (hK t).symm))) (ne_of_gt hz))]
      simp
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add, him]
  rw [mul_add, ← integral_const_mul]
  congr 1
  · ring
  · congr 1 with t
    ring

/-- If `y ‖F(i y)‖` is eventually bounded, the measure of a Herglotz representation of `F` is
finite. -/
theorem isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound
    (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) : IsFiniteMeasure nu := by
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
    simpa using ENNReal.tendsto_ofReal ((tendsto_sq_div_sq_add_sq t).comp
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
    refine (mul_le_mul_of_nonneg_left (im_le_norm _) (by positivity)).trans ?_
    exact_mod_cast hn
  refine ⟨?_⟩
  calc nu Set.univ = ∫⁻ t, Filter.liminf (fun n ↦ ENNReal.ofReal (g n t)) atTop ∂nu := by
        simp [(hlim _).liminf_eq]
    _ ≤ Filter.liminf (fun n ↦ ∫⁻ t, ENNReal.ofReal (g n t) ∂nu) atTop :=
        lintegral_liminf_le fun n ↦ by fun_prop
    _ ≤ ENNReal.ofReal C := Filter.liminf_le_of_frequently_le' hle.frequently
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- If `y ‖F(i y)‖` is eventually bounded, the total mass of the measure of a Herglotz
representation of `F` is `lim y Im F(i y)`. -/
theorem tendsto_mul_im_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) :
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
      refine hnu ((lintegral_mono fun t ↦ ?_).trans_lt ((lintegral_one (μ := nu)).trans_lt
        (lt_top_iff_ne_top.mpr h)))
      exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t]))
    rw [measureReal_def, htop, ENNReal.toReal_top]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : ((y : ℂ) * I).im ≠ 0 := by simpa using hy.ne'
    refine (integral_undef fun h ↦ hnu (lintegral_lt_top_of_integrable_im hz
      ((h.const_mul y⁻¹).congr (.of_forall fun t ↦ ?_)))).symm
    simp only [subtractedResolventKernel_ofReal_mul_I_im]
    field_simp
  have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep hbound
  have h1 : nu.real Set.univ = ∫ _ : ℝ, (1 : ℝ) ∂nu := by simp
  rw [h1]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_
    (integrable_const 1) (.of_forall fun t ↦ ?_)
  · exact .of_forall fun y ↦ (by fun_prop : Measurable fun t : ℝ ↦ y ^ 2 / (t ^ 2 + y ^ 2))
      |>.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with y hy
    refine .of_forall fun t ↦ ?_
    rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg t]
  · exact tendsto_sq_div_sq_add_sq t

/-- **The unsubtracted form.** For a finite measure `ν`, a Herglotz representation
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` splits as
`F z = c + b z + ∫ (t - z)⁻¹ dν(t)` with `c = a - ∫ t / (1 + t ^ 2) dν(t)`. -/
theorem eq_add_resolventTransform_of_eq_subtractedResolventKernel_add [IsFiniteMeasure nu]
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) :
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (a - ∫ t, (t : ℂ) / (1 + (t : ℂ) ^ 2) ∂nu) + b * z + resolventTransform nu z := by
  have hcast (t : ℝ) : (t : ℂ) / (1 + (t : ℂ) ^ 2) = ((t / (1 + t ^ 2) : ℝ) : ℂ) := by
    push_cast; rfl
  have hr : Integrable (fun t : ℝ ↦ t / (1 + t ^ 2)) nu := by
    refine (integrable_const (1 : ℝ)).mono'
      (by fun_prop : Measurable fun t : ℝ ↦ t / (1 + t ^ 2)).aestronglyMeasurable
      (.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2),
      div_le_one (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  have hint : Integrable (fun t : ℝ ↦ (t : ℂ) / (1 + (t : ℂ) ^ 2)) nu :=
    hr.ofReal.congr (.of_forall fun t ↦ (hcast t).symm)
  have hres (z : ℂ) (t : ℝ) : resolvent (R := ℝ) z t = ((t : ℂ) - z)⁻¹ := by
    rw [_root_.resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
  intro z hz
  have hi : Integrable (fun t : ℝ ↦ ((t : ℂ) - z)⁻¹) nu :=
    (integrable_resolvent_of_im_ne_zero (μ := nu) (ne_of_gt hz)).congr
      (.of_forall fun t ↦ hres z t)
  have hk : (fun t ↦ subtractedResolventKernel z t) =
      fun t : ℝ ↦ ((t : ℂ) - z)⁻¹ - (t : ℂ) / (1 + (t : ℂ) ^ 2) :=
    funext fun t ↦ subtractedResolventKernel_def z t
  rw [hrep z hz, resolventTransform_apply, hk, integral_sub hi hint]
  simp_rw [hres]
  ring

/-- **The resolvent case.** If `y ‖F(i y)‖` is eventually bounded, a function with a Herglotz
representation with measure `ν` is the resolvent transform `∫ (t - z)⁻¹ dν(t)` of `ν` on the upper
half-plane. -/
theorem eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hbound : ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) :
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, F z = resolventTransform nu z := by
  have hb := eq_zero_of_eq_subtractedResolventKernel_add_of_bound hrep hbound
  subst hb
  -- `F` is a constant plus the transform, which vanishes along the imaginary axis.
  obtain ⟨c, hrep', hm⟩ : ∃ c : ℂ, (∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = c + resolventTransform nu z) ∧
      Tendsto (fun y : ℝ ↦ resolventTransform nu (y * I)) atTop (𝓝 0) := by
    by_cases hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤
    · have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep hbound
      refine ⟨_, fun z hz ↦ by
        simpa using eq_add_resolventTransform_of_eq_subtractedResolventKernel_add hrep z hz, ?_⟩
      refine squeeze_zero_norm' ?_ (show Tendsto (fun y : ℝ ↦ y⁻¹ * nu.real Set.univ) atTop
        (𝓝 0) by simpa using tendsto_inv_atTop_zero.mul_const (nu.real Set.univ))
      filter_upwards [eventually_gt_atTop 0] with y hy
      have := norm_resolventTransform_le (μ := nu) (z := y * I) (by simpa using hy.ne')
      simpa [abs_of_pos hy] using this
    · -- Without finite weighted mass, neither kernel is integrable.
      have hm (z : ℂ) (hz : z.im ≠ 0) : resolventTransform nu z = 0 := by
        rw [resolventTransform_apply]
        refine integral_undef fun (h : Integrable (resolvent (R := ℝ) z) nu) ↦
          hnu (lintegral_lt_top_of_integrable_im hz
          (h.im.congr (.of_forall fun t ↦ ?_)))
        simp only [RCLike.im_to_complex, Complex.im_resolvent_real,
          subtractedResolventKernel_im, normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im]
        ring
      refine ⟨a, fun z hz ↦ ?_, tendsto_const_nhds.congr' ?_⟩
      · rw [hrep z hz, integral_undef (mt (integrable_subtractedResolventKernel_iff
          (ne_of_gt hz)).1 hnu), hm z (ne_of_gt hz)]
        simp
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (hm _ (by simpa using hy.ne')).symm
  suffices hc : c = 0 by
    intro z hz
    rw [hrep' z hz, hc, zero_add]
  have hF : Tendsto (fun y : ℝ ↦ F (y * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun y : ℝ ↦ C / y) atTop (𝓝 0))
    filter_upwards [hbound, eventually_gt_atTop 0] with y hy hy0
    rw [le_div_iff₀ hy0, mul_comm]
    exact hy
  have hc : Tendsto (fun y : ℝ ↦ F (y * I) - resolventTransform nu (y * I)) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [hrep' _ (by simpa using hy)]
      ring)
  simpa using tendsto_nhds_unique hc (by simpa using hF.sub hm)

end TauCeti
