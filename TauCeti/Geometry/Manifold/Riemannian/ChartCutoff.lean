/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Chart cutoffs on a Riemannian manifold

To localize an integral estimate from the model space to a manifold with a continuous Riemannian
metric, one reads a function `u` in a chart around a point `c` and cuts it off with a bump function
`b` centred at the chart image of `c`. This file supplies the comparisons that such a localization
needs:

* near the chart image of `c` there is a coordinate ball on which the coordinate derivative of
  every function is bounded by a fixed multiple of the length of its gradient, and the chart volume
  density is comparable to its value at `c`
  (`TauCeti.Manifold.exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo`);
* on such a ball, `∫ ‖D(b · u)‖ ^ p` with respect to Lebesgue measure on the model space is bounded
  by a constant multiple of `C₁ ^ p ∫ |∇u| ^ p dV + G ^ p ∫ |u| ^ p dV`, where `C₁` is the
  derivative comparison constant and `G` bounds the derivative of the bump
  (`ContDiffBump.lintegral_enorm_fderiv_mul_comp_extChartAt_symm_rpow_le`), so its `Lᵖ` norm
  is at most a constant times `‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ}`
  (`ContDiffBump.eLpNorm_fderiv_mul_comp_extChartAt_symm_le`);
* where the bump is `1` and the chart density is at most `m`, an integral of `F ∘ u` over the
  chart preimage of a ball is bounded by `m` times the integral of `F (b · u)` over the ball
  (`ContDiffBump.setLIntegral_inter_preimage_le_mul_setLIntegral_mul_comp_extChartAt_symm`).

They are used for the Trudinger and Sobolev inequalities on a closed Riemannian manifold.
-/

public section

open Bundle Filter MeasureTheory Metric Module Set TauCeti TauCeti.Manifold
open scoped ENNReal NNReal Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

namespace TauCeti.Manifold

/-- Around the chart image of `c` there is a coordinate ball inside the chart target on which the
coordinate derivative of every function is bounded by a fixed multiple of the length of its
gradient, and the chart density lies between half and twice its value at `c`. -/
theorem exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (c : M) :
    ∃ C₁ > 0, ∃ r > 0, ball (extChartAt I c c) r ⊆ (extChartAt I c).target ∧
      ∀ y ∈ ball (extChartAt I c c) r, (∀ f : M → ℝ,
        ‖fderiv ℝ (f ∘ (extChartAt I c).symm) y‖ ≤
          C₁ * ‖mgradient I f ((extChartAt I c).symm y)‖) ∧
        chartVolumeDensity (I := I) c ((extChartAt I c).symm y) ∈
          Ioo (chartVolumeDensity (I := I) c c / 2) (2 * chartVolumeDensity (I := I) c c) := by
  obtain ⟨C₁, hC₁, hcmp⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) (M := M) c
  set φ := extChartAt I c
  set ρ := chartVolumeDensity (I := I) c
  have hρc : 0 < ρ c := chartVolumeDensity_pos c (FiberBundle.mem_baseSet_trivializationAt' c)
  have hρcont : ContinuousAt ρ c := by
    have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
    have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
      IsContinuousRiemannianBundle.toIsContMDiffZero
    exact ((contMDiffOn_chartVolumeDensity (I := I) (n := 0) c).continuousOn.continuousAt
      ((trivializationAt E (TangentSpace I) c).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' c)))
  have hρev : ∀ᶠ x in 𝓝 c, ρ x ∈ Ioo (ρ c / 2) (2 * ρ c) :=
    hρcont.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  -- Read both neighbourhoods of `c` in the chart.
  have hsymm : Tendsto φ.symm (𝓝 (φ c)) (𝓝 c) := by
    have h := continuousAt_extChartAt_symm (I := I) c
    rwa [ContinuousAt, extChartAt_to_inv] at h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (extChartAt_target_mem_nhds (I := I) c) (hsymm.eventually (hcmp.and hρev)))
  refine ⟨C₁, hC₁, r, hr, fun y hy ↦ (hball hy).1, fun y hy ↦ ⟨fun f ↦ ?_, (hball hy).2.2⟩⟩
  have h := (hball hy).2.1 f
  rwa [φ.right_inv (hball hy).1] at h

end TauCeti.Manifold

namespace ContDiffBump

variable [MeasurableSpace M] [BorelSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **The derivative of a chart cutoff in `Lᵖ`.** Let `1 ≤ p`. On a coordinate ball where the
chart derivative is bounded by `C₁` times the gradient and the chart density is at least `m`, the
cut-off coordinate expression of a `C¹` function `u` has `∫ ‖D(b · u)‖ ^ p` bounded by
`2 ^ (p - 1) m⁻¹ (C₁ ^ p ∫ |∇u| ^ p dV + G ^ p ∫ |u| ^ p dV)`, where `G` bounds the derivative of
the bump `b`. -/
theorem lintegral_enorm_fderiv_mul_comp_extChartAt_symm_rpow_le [LindelofSpace M] {c : M}
    (b : ContDiffBump (extChartAt I c c)) {r : ℝ}
    (hbr : closedBall (extChartAt I c c) b.rOut ⊆ ball (extChartAt I c c) r)
    (hrt : ball (extChartAt I c c) r ⊆ (extChartAt I c).target) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hcmp : ∀ y ∈ ball (extChartAt I c c) r, ∀ f : M → ℝ,
      ‖fderiv ℝ (f ∘ (extChartAt I c).symm) y‖ ≤ C₁ * ‖mgradient I f ((extChartAt I c).symm y)‖)
    {m : ℝ} (hm : 0 < m) (hρ : ∀ y ∈ ball (extChartAt I c c) r,
      m ≤ chartVolumeDensity (I := I) c ((extChartAt I c).symm y))
    {G : ℝ} (hG : ∀ y, ‖fderiv ℝ b y‖ ≤ G) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ y, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ p
        ∂(Module.finBasis ℝ E).addHaar ≤
      2 ^ (p - 1) * ENNReal.ofReal m⁻¹ *
        (ENNReal.ofReal C₁ ^ p * ∫⁻ x, ‖mgradient I u x‖ₑ ^ p ∂riemannianVolume I M +
          ENNReal.ofReal G ^ p * ∫⁻ x, ‖u x‖ₑ ^ p ∂riemannianVolume I M) := by
  set μ := (Module.finBasis ℝ E).addHaar
  set B := ball (extChartAt I c c) r
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hfin (a : ℝ) : ENNReal.ofReal a ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  -- On `B` the integrand is dominated by the gradient and the function.
  have hpt : ∀ y ∈ B, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ p ≤
      2 ^ (p - 1) * (ENNReal.ofReal C₁ ^ p * ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ p +
        ENNReal.ofReal G ^ p * ‖u ((extChartAt I c).symm y)‖ₑ ^ p) := fun y hy ↦ by
    have hbd := (b.norm_fderiv_mul_comp_extChartAt_symm_le hu hG (hrt hy)).trans
      (add_le_add (hcmp y hy u) le_rfl)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.mul_rpow_of_nonneg _ _ hp0]
    refine (ENNReal.rpow_le_rpow ?_ hp0).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC₁,
      ← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_add (by positivity) (by positivity),
      Real.norm_eq_abs (u _)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hmeas : AEMeasurable
      (fun y ↦ ENNReal.ofReal G ^ p * ‖u ((extChartAt I c).symm y)‖ₑ ^ p) (μ.restrict B) :=
    ((((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn.continuousOn.mono
      hrt).aemeasurable measurableSet_ball).enorm.pow_const p).const_mul _
  calc ∫⁻ y, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ p ∂μ
      = ∫⁻ y in B, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ p ∂μ := by
        -- The integrand vanishes off the support of the bump, which lies in `B`.
        refine (setLIntegral_eq_of_support_subset fun y hy ↦ ?_).symm
        by_contra hyB
        refine hy ?_
        simp only [b.fderiv_mul_comp_extChartAt_symm_eq_zero (u := u) fun h ↦ hyB (hbr h)]
        rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero,
          ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)]
    _ ≤ ∫⁻ y in B, 2 ^ (p - 1) *
          (ENNReal.ofReal C₁ ^ p * ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ p +
            ENNReal.ofReal G ^ p * ‖u ((extChartAt I c).symm y)‖ₑ ^ p) ∂μ :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = 2 ^ (p - 1) *
          (ENNReal.ofReal C₁ ^ p * ∫⁻ y in B, ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ p ∂μ +
            ENNReal.ofReal G ^ p * ∫⁻ y in B, ‖u ((extChartAt I c).symm y)‖ₑ ^ p ∂μ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
          lintegral_add_right' _ hmeas, lintegral_const_mul' _ _ (hfin _),
          lintegral_const_mul' _ _ (hfin _)]
    _ ≤ 2 ^ (p - 1) * (ENNReal.ofReal C₁ ^ p *
            (ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖mgradient I u x‖ₑ ^ p ∂riemannianVolume I M) +
          ENNReal.ofReal G ^ p *
            (ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖u x‖ₑ ^ p ∂riemannianVolume I M)) := by
        gcongr
        · exact setLIntegral_comp_extChartAt_symm_le_mul_lintegral c isOpen_ball hrt hm hρ
            fun x ↦ ‖mgradient I u x‖ₑ ^ p
        · exact setLIntegral_comp_extChartAt_symm_le_mul_lintegral c isOpen_ball hrt hm hρ
            fun x ↦ ‖u x‖ₑ ^ p
    _ = _ := by ring

/-- **The derivative of a chart cutoff in `Lᵖ`, in norm form.** Let `1 ≤ p`. On a coordinate ball
where the chart derivative is bounded by `C₁` times the gradient and the chart density is at least
`m`, the cut-off coordinate expression of a `C¹` function `u` has
`‖D(b · u)‖_{Lᵖ} ≤ 2 (C₁ + G) m^{-1/p} (‖∇u‖_{Lᵖ} + ‖u‖_{Lᵖ})`, where `G` bounds the derivative of
the bump `b`. -/
theorem eLpNorm_fderiv_mul_comp_extChartAt_symm_le [LindelofSpace M] {c : M}
    (b : ContDiffBump (extChartAt I c c)) {r : ℝ}
    (hbr : closedBall (extChartAt I c c) b.rOut ⊆ ball (extChartAt I c c) r)
    (hrt : ball (extChartAt I c c) r ⊆ (extChartAt I c).target) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hcmp : ∀ y ∈ ball (extChartAt I c c) r, ∀ f : M → ℝ,
      ‖fderiv ℝ (f ∘ (extChartAt I c).symm) y‖ ≤ C₁ * ‖mgradient I f ((extChartAt I c).symm y)‖)
    {m : ℝ} (hm : 0 < m) (hρ : ∀ y ∈ ball (extChartAt I c c) r,
      m ≤ chartVolumeDensity (I := I) c ((extChartAt I c).symm y))
    {G : ℝ} (hG : ∀ y, ‖fderiv ℝ b y‖ ≤ G) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u)
    {p : ℝ≥0} (hp : 1 ≤ p) :
    eLpNorm (fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y))) p
        (Module.finBasis ℝ E).addHaar ≤
      2 * ENNReal.ofReal (C₁ + G) * ENNReal.ofReal m⁻¹ ^ (p : ℝ)⁻¹ *
        (eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) +
          eLpNorm u p (riemannianVolume I M)) := by
  set X := eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) +
    eLpNorm u p (riemannianVolume I M)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpR : 0 < (p : ℝ) := NNReal.coe_pos.2 (zero_lt_one.trans_le hp)
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hw := b.contDiff_mul_comp_extChartAt_symm (hbr.trans hrt) hu
  have hgrad := lintegral_rpow_enorm_le_rpow_eLpNorm (μ := riemannianVolume I M) hp0
    fun x ↦ ‖mgradient I u x‖
  simp only [enorm_norm] at hgrad
  rw [← ENNReal.rpow_le_rpow_iff hpR,
    eLpNorm_nnreal_pow_eq_lintegral hp0 (hw.continuous_fderiv one_ne_zero).aestronglyMeasurable]
  calc _ ≤ 2 ^ ((p : ℝ) - 1) * ENNReal.ofReal m⁻¹ *
          (ENNReal.ofReal C₁ ^ (p : ℝ) * ∫⁻ x, ‖mgradient I u x‖ₑ ^ (p : ℝ) ∂riemannianVolume I M +
            ENNReal.ofReal G ^ (p : ℝ) * ∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂riemannianVolume I M) :=
        b.lintegral_enorm_fderiv_mul_comp_extChartAt_symm_rpow_le hbr hrt hC₁ hcmp hm hρ hG hu
          (by exact_mod_cast hp)
    _ ≤ 2 ^ ((p : ℝ) - 1) * ENNReal.ofReal m⁻¹ *
          (ENNReal.ofReal (C₁ + G) ^ (p : ℝ) * X ^ (p : ℝ) +
            ENNReal.ofReal (C₁ + G) ^ (p : ℝ) * X ^ (p : ℝ)) := by
        gcongr
        · exact le_add_of_nonneg_right hG0
        · exact hgrad.trans (ENNReal.rpow_le_rpow le_self_add hpR.le)
        · exact le_add_of_nonneg_left hC₁
        · exact (lintegral_rpow_enorm_le_rpow_eLpNorm hp0 u).trans
            (ENNReal.rpow_le_rpow le_add_self hpR.le)
    _ = _ := by
        have h2 : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * 2 ^ (1 : ℝ) = 2 ^ (p : ℝ) := by
          rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, sub_add_cancel]
        rw [ENNReal.rpow_one] at h2
        rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ hpR.le,
          ENNReal.mul_rpow_of_nonneg _ _ hpR.le, ENNReal.mul_rpow_of_nonneg _ _ hpR.le,
          ENNReal.rpow_inv_rpow hpR.ne', ← h2]
        ring

omit [I.Boundaryless] in
/-- **Reading a chart cutoff back on `M`.** If the chart density is at most `m` on the ball of
radius `b.rIn`, where the bump is `1`, then for every `F : ℝ → ℝ≥0∞` the integral of `F ∘ u` over
the chart preimage of that ball is at most `m` times the integral of `F (b · u)` over the ball, with
respect to Lebesgue measure on the model space. -/
theorem setLIntegral_inter_preimage_le_mul_setLIntegral_mul_comp_extChartAt_symm [LindelofSpace M]
    {c : M}
    (b : ContDiffBump (extChartAt I c c))
    (hbt : ball (extChartAt I c c) b.rIn ⊆ (extChartAt I c).target) {m : ℝ}
    (hρ : ∀ y ∈ ball (extChartAt I c c) b.rIn,
      chartVolumeDensity (I := I) c ((extChartAt I c).symm y) ≤ m)
    (u : M → ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in (extChartAt I c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) b.rIn,
        F (u x) ∂riemannianVolume I M ≤
      ENNReal.ofReal m * ∫⁻ y in ball (extChartAt I c c) b.rIn,
        F (b y * u ((extChartAt I c).symm y)) ∂(Module.finBasis ℝ E).addHaar := by
  rw [setLIntegral_riemannianVolume_inter_preimage c isOpen_ball hbt,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
  rw [b.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  gcongr
  exact hρ y hy

end ContDiffBump
