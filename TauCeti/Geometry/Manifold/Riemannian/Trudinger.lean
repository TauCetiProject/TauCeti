/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Sobolev.Trudinger
public import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Trudinger's inequality on a closed Riemannian manifold

Let `M` be a compact manifold without boundary, of dimension `n ≥ 2`, with a continuous
Riemannian metric and its Riemannian volume `dV`. **Trudinger's inequality** says that a function
of unit `W^{1,n}` norm is exponentially integrable: there are constants `β > 0` and `C` such that

`∫_M exp (β |u| ^ (n / (n - 1))) dV ≤ C`

for every `C¹` function `u` with `‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`
(`TauCeti.Manifold.exists_lintegral_exp_mul_abs_rpow_le`). On a closed surface, `n = 2`, this is
the two-dimensional exponential estimate `∫_M exp (β u²) dV ≤ C` for `‖∇u‖_{L²} + ‖u‖_{L²} ≤ 1`
(`TauCeti.Manifold.exists_lintegral_exp_mul_sq_le_of_finrank_eq_two`). It is what makes `e^(2u)`
integrable, with a bound in terms of the `H¹` norm of `u`, in the variational treatment of the
prescribed Gaussian curvature equation `Δ⁺u + K₀ = K e^(2u)` on a closed surface.

The proof localizes the flat inequality
`TauCeti.setLIntegral_exp_norm_div_rpow_le_of_eLpNorm_fderiv_le`. Near each point `c`, in a
coordinate ball around the chart image of `c`, the chart density is comparable to its value at `c`
and the coordinate derivative of every function is bounded by a fixed multiple of the length of
its gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`). A bump
function equal to `1` on a smaller coordinate ball cuts `u` off to a compactly supported `C¹`
function on the model space, whose derivative has `Lⁿ` norm bounded by a constant depending only
on `c`, the metric and the bump; the flat inequality then bounds the integral of
`exp (β |u| ^ (n / (n - 1)))` over the chart preimage of the smaller ball
(`TauCeti.Manifold.exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le`). Finitely many such
neighbourhoods cover `M`.

## Main results

* `TauCeti.Manifold.exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le`: the local inequality,
  near any point of a manifold without boundary.
* `TauCeti.Manifold.exists_lintegral_exp_mul_abs_rpow_le`: Trudinger's inequality on a closed
  Riemannian manifold of dimension at least two.
* `TauCeti.Manifold.exists_lintegral_exp_mul_sq_le_of_finrank_eq_two`: its form on a closed
  surface.

## References

* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
-/

public section

open Bundle Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Around the chart image of `c` there is a coordinate ball inside the chart target on which the
coordinate derivative of every function is bounded by a fixed multiple of the length of its
gradient, and the chart density lies between half and twice its value at `c`. -/
private theorem exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (c : M) :
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

variable [MeasurableSpace M] [BorelSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **The derivative of the cut-off function in `Lⁿ`.** On a coordinate ball where the chart
derivative is bounded by `C₁` times the gradient and the chart density is at least `m`, the
cut-off coordinate expression of `u` has `∫ ‖D(b · u)‖ⁿ` bounded by a constant multiple of
`C₁ⁿ ∫ |∇u|ⁿ dV + Gⁿ ∫ |u|ⁿ dV`. -/
private theorem lintegral_enorm_fderiv_bump_mul_rpow_le [LindelofSpace M] [Nontrivial E] {c : M}
    (b : ContDiffBump (extChartAt I c c)) {r : ℝ}
    (hbr : closedBall (extChartAt I c c) b.rOut ⊆ ball (extChartAt I c c) r)
    (hrt : ball (extChartAt I c c) r ⊆ (extChartAt I c).target) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hcmp : ∀ y ∈ ball (extChartAt I c c) r, ∀ f : M → ℝ,
      ‖fderiv ℝ (f ∘ (extChartAt I c).symm) y‖ ≤ C₁ * ‖mgradient I f ((extChartAt I c).symm y)‖)
    {m : ℝ} (hm : 0 < m) (hρ : ∀ y ∈ ball (extChartAt I c c) r,
      m ≤ chartVolumeDensity (I := I) c ((extChartAt I c).symm y))
    {G : ℝ} (hG : ∀ y, ‖fderiv ℝ b y‖ ≤ G) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u) :
    ∫⁻ y, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ (finrank ℝ E : ℝ)
        ∂(Module.finBasis ℝ E).addHaar ≤
      2 ^ ((finrank ℝ E : ℝ) - 1) * ENNReal.ofReal m⁻¹ *
        (ENNReal.ofReal C₁ ^ (finrank ℝ E : ℝ) *
            ∫⁻ x, ‖mgradient I u x‖ₑ ^ (finrank ℝ E : ℝ) ∂riemannianVolume I M +
          ENNReal.ofReal G ^ (finrank ℝ E : ℝ) *
            ∫⁻ x, ‖u x‖ₑ ^ (finrank ℝ E : ℝ) ∂riemannianVolume I M) := by
  set n : ℝ := (finrank ℝ E : ℝ)
  set μ := (Module.finBasis ℝ E).addHaar
  set B := ball (extChartAt I c c) r
  have hn : 1 ≤ n := Nat.one_le_cast.2 Module.finrank_pos
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hfin (a : ℝ) : ENNReal.ofReal a ^ n ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hn0 ENNReal.ofReal_ne_top
  -- On `B` the integrand is dominated by the gradient and the function.
  have hpt : ∀ y ∈ B, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ n ≤
      2 ^ (n - 1) * (ENNReal.ofReal C₁ ^ n * ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ n +
        ENNReal.ofReal G ^ n * ‖u ((extChartAt I c).symm y)‖ₑ ^ n) := fun y hy ↦ by
    have hbd := (b.norm_fderiv_mul_comp_extChartAt_symm_le hu hG (hrt hy)).trans
      (add_le_add (hcmp y hy u) le_rfl)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hn0, ← ENNReal.mul_rpow_of_nonneg _ _ hn0]
    refine (ENNReal.rpow_le_rpow ?_ hn0).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hn)
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC₁,
      ← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_add (by positivity) (by positivity),
      Real.norm_eq_abs (u _)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hmeas : AEMeasurable
      (fun y ↦ ENNReal.ofReal G ^ n * ‖u ((extChartAt I c).symm y)‖ₑ ^ n) (μ.restrict B) :=
    ((((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn.continuousOn.mono
      hrt).aemeasurable measurableSet_ball).enorm.pow_const n).const_mul _
  calc ∫⁻ y, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ n ∂μ
      = ∫⁻ y in B, ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ₑ ^ n ∂μ := by
        -- The integrand vanishes off the support of the bump, which lies in `B`.
        refine (setLIntegral_eq_of_support_subset fun y hy ↦ ?_).symm
        by_contra hyB
        refine hy ?_
        simp only [b.fderiv_mul_comp_extChartAt_symm_eq_zero (u := u) fun h ↦ hyB (hbr h)]
        rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero,
          ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hn)]
    _ ≤ ∫⁻ y in B, 2 ^ (n - 1) *
          (ENNReal.ofReal C₁ ^ n * ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ n +
            ENNReal.ofReal G ^ n * ‖u ((extChartAt I c).symm y)‖ₑ ^ n) ∂μ :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = 2 ^ (n - 1) *
          (ENNReal.ofReal C₁ ^ n * ∫⁻ y in B, ‖mgradient I u ((extChartAt I c).symm y)‖ₑ ^ n ∂μ +
            ENNReal.ofReal G ^ n * ∫⁻ y in B, ‖u ((extChartAt I c).symm y)‖ₑ ^ n ∂μ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
          lintegral_add_right' _ hmeas, lintegral_const_mul' _ _ (hfin _),
          lintegral_const_mul' _ _ (hfin _)]
    _ ≤ 2 ^ (n - 1) * (ENNReal.ofReal C₁ ^ n *
            (ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖mgradient I u x‖ₑ ^ n ∂riemannianVolume I M) +
          ENNReal.ofReal G ^ n *
            (ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖u x‖ₑ ^ n ∂riemannianVolume I M)) := by
        gcongr
        · exact setLIntegral_comp_extChartAt_symm_le_mul_lintegral c isOpen_ball hrt hm hρ
            fun x ↦ ‖mgradient I u x‖ₑ ^ n
        · exact setLIntegral_comp_extChartAt_symm_le_mul_lintegral c isOpen_ball hrt hm hρ
            fun x ↦ ‖u x‖ₑ ^ n
    _ = _ := by ring

/-! ### Trudinger's inequality -/

/-- **Trudinger's inequality near a point.** Every point `c` of a manifold without boundary, of
dimension `n ≥ 2`, with a continuous Riemannian metric, has a neighbourhood `V` with constants
`β > 0` and `C` such that `∫_V exp (β |u| ^ (n / (n - 1))) dV ≤ C` for every `C¹` function `u`
with `‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`. -/
theorem exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le [LindelofSpace M] (hn : 2 ≤ finrank ℝ E)
    (c : M) :
    ∃ V ∈ 𝓝 c, ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) (finrank ℝ E) (riemannianVolume I M) +
          eLpNorm u (finrank ℝ E) (riemannianVolume I M) ≤ 1 →
        ∫⁻ x in V, ENNReal.ofReal (Real.exp (β * |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1))))
          ∂riemannianVolume I M ≤ C := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- A coordinate ball of radius `r` around the chart image of `c`, adapted to the metric.
  obtain ⟨C₁, hC₁, r, hr, hrt, hball⟩ :=
    exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (I := I) (M := M) c
  set n := finrank ℝ E
  set q : ℝ := (n : ℝ) / (n - 1)
  set φ := extChartAt I c
  set μ := (Module.finBasis ℝ E).addHaar
  set ρ := chartVolumeDensity (I := I) c
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < q := div_pos (by positivity) (by linarith)
  have hρc : 0 < ρ c := chartVolumeDensity_pos c (FiberBundle.mem_baseSet_trivializationAt' c)
  -- The bump function equal to `1` on the ball of radius `r / 4`, supported in radius `r / 2`.
  let b : ContDiffBump (φ c) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbr : closedBall (φ c) b.rOut ⊆ ball (φ c) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨G, hG⟩ := ((b.contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support (b.hasCompactSupport.fderiv ℝ)
  -- The constants: `Λ` bounds `∫ ‖D(b u)‖ⁿ`, so `A` bounds `‖D(b u)‖_{Lⁿ}`.
  set Λ : ℝ≥0∞ := 2 ^ ((n : ℝ) - 1) * ENNReal.ofReal (ρ c / 2)⁻¹ *
    (ENNReal.ofReal C₁ ^ (n : ℝ) * 1 + ENNReal.ofReal G ^ (n : ℝ) * 1)
  have hΛ : Λ ^ (n : ℝ)⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)
  set A : ℝ := (Λ ^ (n : ℝ)⁻¹).toReal + 1
  have hA : 0 < A := by positivity
  set κ : ℝ := (2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * (n : ℝ)⁻¹ *
    μ.real (ball 0 1) ^ (-(n : ℝ)⁻¹)
  have hκ : 0 < κ := by
    have : 0 < μ.real (ball 0 1) :=
      ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
    positivity
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * ρ c) *
    (ENNReal.ofReal (Real.exp 1 * (n ^ n + 5)) * μ (ball (φ c) r))
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ c) (r / 4),
    inter_mem (extChartAt_source_mem_nhds c)
      ((continuousAt_extChartAt c).preimage_mem_nhds (ball_mem_nhds _ (by positivity))),
    ((κ * A) ^ q)⁻¹, by positivity, C.toNNReal, fun u hu hnorm ↦ ?_⟩
  -- Cut `u` off in the chart.
  set w : E → ℝ := fun y ↦ b y * u (φ.symm y)
  have hw : ContDiff ℝ 1 w := b.contDiff_mul_comp_extChartAt_symm (hbr.trans hrt) hu
  have hwcs : HasCompactSupport w := b.hasCompactSupport.mul_right
  have hwsupp : tsupport w ⊆ ball (φ c) r := tsupport_mul_subset_left.trans (b.tsupport_eq ▸ hbr)
  -- A function of unit `Lⁿ` norm has `∫ ‖f‖ ^ n ≤ 1`.
  have hint : ∀ f : M → ℝ, eLpNorm f n (riemannianVolume I M) ≤ 1 →
      ∫⁻ x, ‖f x‖ₑ ^ (n : ℝ) ∂riemannianVolume I M ≤ 1 := fun f hf ↦ by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := (n : ℝ≥0)) (by simp; omega)
      (aestronglyMeasurable_of_eLpNorm_ne_top (hf.trans_lt ENNReal.one_lt_top).ne)
    rw [ENNReal.coe_natCast, NNReal.coe_natCast] at h
    exact h ▸ ENNReal.rpow_le_one hf (Nat.cast_nonneg _)
  have hgrad := hint _ (le_self_add.trans hnorm)
  simp only [enorm_norm] at hgrad
  -- The derivative of the cut-off function has `Lⁿ` norm at most `A`.
  have hDw : ∫⁻ y, ‖fderiv ℝ w y‖ₑ ^ (n : ℝ) ∂μ ≤ Λ :=
    (lintegral_enorm_fderiv_bump_mul_rpow_le b hbr hrt hC₁.le (fun y hy ↦ (hball y hy).1)
      (m := ρ c / 2) (by positivity) (fun y hy ↦ (hball y hy).2.1.le) hG hu).trans (by
        simp only [Λ]
        gcongr
        exact hint u (le_add_self.trans hnorm))
  have hDwA : eLpNorm (fderiv ℝ w) n μ ≤ ENNReal.ofReal A := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega) (ENNReal.natCast_ne_top n)
      (hw.continuous_fderiv one_ne_zero).aestronglyMeasurable, ENNReal.toReal_natCast, one_div]
    calc (∫⁻ y, ‖fderiv ℝ w y‖ₑ ^ (n : ℝ) ∂μ) ^ (n : ℝ)⁻¹ ≤ Λ ^ (n : ℝ)⁻¹ :=
          ENNReal.rpow_le_rpow hDw (by positivity)
      _ = ENNReal.ofReal (Λ ^ (n : ℝ)⁻¹).toReal := (ENNReal.ofReal_toReal hΛ).symm
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  -- The flat Trudinger inequality for `w` on the ball of radius `r`, read back on `M`.
  have htr := setLIntegral_exp_norm_div_rpow_le_of_eLpNorm_fderiv_le (μ := μ) hw hwcs
    measurableSet_ball hwsupp hn hA hDwA
  rw [ENNReal.coe_toNNReal hC, setLIntegral_riemannianVolume_inter_preimage c isOpen_ball
    ((ball_subset_ball (by linarith)).trans hrt)]
  calc ∫⁻ y in ball (φ c) (r / 4), ENNReal.ofReal (ρ (φ.symm y)) *
        ENNReal.ofReal (Real.exp (((κ * A) ^ q)⁻¹ * |u (φ.symm y)| ^ q)) ∂μ
      ≤ ∫⁻ y in ball (φ c) (r / 4), ENNReal.ofReal (2 * ρ c) *
          ENNReal.ofReal (Real.exp ((‖w y‖ / (κ * A)) ^ q)) ∂μ := by
        refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
        -- On the ball of radius `r / 4` the bump is `1`, so `w` is `u` read in the chart.
        have hwy : w y = u (φ.symm y) := by
          simp only [w, b.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
        gcongr
        · exact (hball y (ball_subset_ball (by linarith) hy)).2.2.le
        · rw [Real.div_rpow (norm_nonneg _) (by positivity), Real.norm_eq_abs, hwy,
            div_eq_inv_mul]
    _ ≤ ∫⁻ y in ball (φ c) r, ENNReal.ofReal (2 * ρ c) *
          ENNReal.ofReal (Real.exp ((‖w y‖ / (κ * A)) ^ q)) ∂μ :=
        lintegral_mono_set (ball_subset_ball (by linarith))
    _ = ENNReal.ofReal (2 * ρ c) *
          ∫⁻ y in ball (φ c) r, ENNReal.ofReal (Real.exp ((‖w y‖ / (κ * A)) ^ q)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ C := mul_le_mul_of_nonneg_left htr bot_le

/-- **Trudinger's inequality on a closed Riemannian manifold.** On a compact manifold without
boundary, of dimension `n ≥ 2`, with a continuous Riemannian metric, there are constants `β > 0`
and `C` such that `∫_M exp (β |u| ^ (n / (n - 1))) dV ≤ C` for every `C¹` function `u` with
`‖∇u‖_{Lⁿ} + ‖u‖_{Lⁿ} ≤ 1`. -/
theorem exists_lintegral_exp_mul_abs_rpow_le [CompactSpace M] (hn : 2 ≤ finrank ℝ E) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) (finrank ℝ E) (riemannianVolume I M) +
          eLpNorm u (finrank ℝ E) (riemannianVolume I M) ≤ 1 →
        ∫⁻ x, ENNReal.ofReal (Real.exp (β * |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1))))
          ∂riemannianVolume I M ≤ C := by
  choose V hV β hβ C hC using exists_mem_nhds_setLIntegral_exp_mul_abs_rpow_le (I := I) (M := M) hn
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V fun c _ ↦ hV c
  -- A common exponent: `β₀⁻¹ = 1 + ∑ c ∈ t, (β c)⁻¹`.
  have hsum : 0 ≤ ∑ c ∈ t, (β c)⁻¹ := Finset.sum_nonneg fun c _ ↦ (inv_pos.2 (hβ c)).le
  refine ⟨(1 + ∑ c ∈ t, (β c)⁻¹)⁻¹, inv_pos.2 (by linarith), ∑ c ∈ t, C c,
    fun u hu hnorm ↦ ?_⟩
  calc ∫⁻ x, ENNReal.ofReal (Real.exp ((1 + ∑ c ∈ t, (β c)⁻¹)⁻¹ *
          |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂riemannianVolume I M
      ≤ ∑ c ∈ t, ∫⁻ x in V c, ENNReal.ofReal (Real.exp ((1 + ∑ c ∈ t, (β c)⁻¹)⁻¹ *
          |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂riemannianVolume I M := by
        rw [← setLIntegral_univ]
        refine (lintegral_mono_set ht).trans ?_
        rw [← iUnion_subtype (· ∈ t) fun c ↦ V c]
        refine (lintegral_iUnion_le _ _).trans_eq ?_
        rw [tsum_fintype]
        exact Finset.sum_coe_sort t fun c ↦ ∫⁻ x in V c, ENNReal.ofReal (Real.exp
          ((1 + ∑ c ∈ t, (β c)⁻¹)⁻¹ * |u x| ^ ((finrank ℝ E : ℝ) / (finrank ℝ E - 1))))
          ∂riemannianVolume I M
    _ ≤ ∑ c ∈ t, (C c : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun c hc ↦ (lintegral_mono fun x ↦ ?_).trans (hC c u hu hnorm)
        gcongr
        exact inv_le_of_inv_le₀ (hβ c) (le_add_of_nonneg_of_le zero_le_one
          (Finset.single_le_sum (f := fun c ↦ (β c)⁻¹) (fun c _ ↦ (inv_pos.2 (hβ c)).le) hc))
    _ = ((∑ c ∈ t, C c : ℝ≥0) : ℝ≥0∞) := (ENNReal.ofNNReal_finsetSum _ _).symm

/-- **The two-dimensional exponential estimate.** On a closed surface with a continuous Riemannian
metric, there are constants `β > 0` and `C` such that `∫_M exp (β u²) dV ≤ C` for every `C¹`
function `u` with `‖∇u‖_{L²} + ‖u‖_{L²} ≤ 1`. -/
theorem exists_lintegral_exp_mul_sq_le_of_finrank_eq_two [CompactSpace M]
    (hE : finrank ℝ E = 2) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ ‖mgradient I u x‖) 2 (riemannianVolume I M) +
          eLpNorm u 2 (riemannianVolume I M) ≤ 1 →
        ∫⁻ x, ENNReal.ofReal (Real.exp (β * u x ^ 2)) ∂riemannianVolume I M ≤ C := by
  obtain ⟨β, hβ, C, h⟩ := exists_lintegral_exp_mul_abs_rpow_le (I := I) (M := M) hE.ge
  refine ⟨β, hβ, C, fun u hu hnorm ↦ ?_⟩
  have h2 := h u hu (by rwa [hE, Nat.cast_ofNat])
  norm_num [hE] at h2
  simpa only [Real.rpow_two, sq_abs] using h2

end TauCeti.Manifold
