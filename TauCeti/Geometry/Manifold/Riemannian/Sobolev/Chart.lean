/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.MeasureTheory.Function.Lp.Precomposition

/-!
# Elements of `H¹(M)` read in a chart

Let `M` be a compact manifold without boundary with a continuous Riemannian metric, and let
`H¹(M)` (`TauCeti.Manifold.SobolevH1`) be the completion of the smooth functions on `M` for the
`H¹` norm `(∫ u² dV + ∫ ‖∇u‖² dV)^(1/2)`. This file shows that an element of `H¹(M)`, read in a
chart, is a Euclidean Sobolev function: near every point `p` there is an open set `Ω` of
coordinates on which reading in the chart is a continuous linear map

`H¹(M) → W^{1,2}(Ω)`

(`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`). The coordinates are those
of the extended chart at `p`, composed with an arbitrary continuous linear equivalence `L` from the
model space to a finite-dimensional inner product space `F` carrying a Haar measure, such as
`EuclideanSpace ℝ (Fin n)` with Lebesgue measure. On a smooth function `u` the map is
`u ↦ u ∘ φ⁻¹`, with `φ = L ∘ extChartAt I p`, together with its classical gradient, and on all of
`H¹(M)` its value is the value of `w` in `L²(M)` read in the chart.

This is the bridge from `H¹(M)` to the Euclidean theory of weak solutions: read in a chart, a weak
solution in `H¹(M)` of an elliptic equation such as the Poisson equation
(`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`) is an element of `W^{1,2}(Ω)`, the
space on which the interior regularity theory of divergence-form equations is stated.

## The argument

Near `p` the coordinate derivative of every function is bounded by a fixed multiple of the length
of its gradient, and the chart volume density is bounded below
(`TauCeti.Manifold.exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo`). The second bound
says that the inverse chart pushes Lebesgue measure on `Ω` forward to at most a constant multiple
of the Riemannian volume, so precomposition with it is a bounded operator `L²(M) → L²(Ω)`
(`MeasureTheory.Lp.compOfMapLeSmul`). The first bound controls the coordinate gradient of
`u ∘ φ⁻¹` by the Riemannian gradient of `u`. Together they bound the `W^{1,2}(Ω)` norm of
`u ∘ φ⁻¹` by the `H¹(M)` norm of `u`, so reading in the chart extends from the smooth functions to
their completion. The value of the extension is identified with precomposition of the value in
`L²(M)` by continuity, since both agree on the dense set of smooth functions.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`: reading an element of
  `H¹(M)` in a chart near a point is a continuous linear map into `W^{1,2}(Ω)`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §2.2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
-/

public section

open Bundle MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Manifold Gradient ENNReal NNReal InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The open set of points of `F` whose image under `L⁻¹` lies in the coordinate ball of radius
`r` around the chart image of `p`. -/
private def coordBall (L : E ≃L[ℝ] F) (p : M) (r : ℝ) : Opens F :=
  ⟨L.symm ⁻¹' ball (extChartAt I p p) r, isOpen_ball.preimage L.symm.continuous⟩

private theorem mem_coordBall {L : E ≃L[ℝ] F} {p : M} {r : ℝ} {y : F} :
    y ∈ coordBall (I := I) L p r ↔ L.symm y ∈ ball (extChartAt I p p) r :=
  Iff.rfl

open Classical in
/-- The inverse of the extended chart at `p` on the coordinate ball of radius `r` around `p`,
extended by the constant `p` off the ball: a measurable function agreeing with
`(extChartAt I p).symm` on the ball. -/
private def ballChartInv (p : M) (r : ℝ) : E → M :=
  (ball (extChartAt I p p) r).piecewise (extChartAt I p).symm fun _ ↦ p

private theorem ballChartInv_of_mem {p : M} {r : ℝ} {z : E} (hz : z ∈ ball (extChartAt I p p) r) :
    ballChartInv (I := I) p r z = (extChartAt I p).symm z := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

section CoordinateMeasure

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

variable [MeasurableSpace M] [BorelSpace M]

private theorem measurable_ballChartInv {p : M} {r : ℝ}
    (hr : ball (extChartAt I p p) r ⊆ (extChartAt I p).target) :
    Measurable (ballChartInv (I := I) p r) := by
  classical
  exact ContinuousOn.measurable_piecewise ((continuousOn_extChartAt_symm p).mono hr)
    continuousOn_const measurableSet_ball

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a coordinate ball where the chart density is at least `m > 0`, the inverse chart pushes the
coordinate measure forward to at most `m⁻¹` times the Riemannian volume. -/
private theorem map_restrict_ballChartInv_le {p : M} {r m : ℝ}
    (hr : ball (extChartAt I p p) r ⊆ (extChartAt I p).target) (hm : 0 < m)
    (hρ : ∀ y ∈ ball (extChartAt I p p) r,
      m ≤ chartVolumeDensity (I := I) p ((extChartAt I p).symm y)) :
    ((Module.finBasis ℝ E).addHaar.restrict (ball (extChartAt I p p) r)).map
        (ballChartInv (I := I) p r) ≤ ENNReal.ofReal m⁻¹ • riemannianVolume I M := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  have hf := measurable_ballChartInv hr
  rw [Measure.map_apply hf hs, smul_apply, smul_eq_mul, ← lintegral_indicator_one hs,
    ← lintegral_indicator_one (hf hs)]
  calc ∫⁻ z, (ballChartInv (I := I) p r ⁻¹' s).indicator 1 z
        ∂(Module.finBasis ℝ E).addHaar.restrict (ball (extChartAt I p p) r)
      = ∫⁻ z in ball (extChartAt I p p) r, s.indicator 1 ((extChartAt I p).symm z)
          ∂(Module.finBasis ℝ E).addHaar := by
        refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
        rw [← ballChartInv_of_mem hz, ← indicator_comp_right, Pi.one_comp]
    _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ x, s.indicator 1 x ∂riemannianVolume I M :=
        setLIntegral_comp_extChartAt_symm_le_mul_lintegral p isOpen_ball hr hm hρ _

end CoordinateMeasure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- On the preimage of a coordinate ball on which the chart derivative of every function is at
most `C₁` times the length of its gradient, the coordinate gradient of
`u ∘ (extChartAt I p).symm ∘ L⁻¹` is at most `‖L⁻¹‖ C₁` times the length of the gradient of `u`. -/
private theorem norm_gradient_comp_le {p : M} {r C₁ : ℝ} (L : E ≃L[ℝ] F)
    (hcmp : ∀ y ∈ ball (extChartAt I p p) r, ∀ f : M → ℝ,
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) y‖ ≤ C₁ * ‖mgradient I f ((extChartAt I p).symm y)‖)
    (u : M → ℝ) {y : F} (hy : L.symm y ∈ ball (extChartAt I p p) r) :
    ‖∇ (fun y ↦ u ((extChartAt I p).symm (L.symm y))) y‖ ≤
      ‖(L.symm : F →L[ℝ] E)‖ * C₁ * ‖mgradient I u ((extChartAt I p).symm (L.symm y))‖ := by
  have h : (fun y ↦ u ((extChartAt I p).symm (L.symm y))) =
      (u ∘ (extChartAt I p).symm) ∘ L.symm := rfl
  rw [gradient, LinearIsometryEquiv.norm_map, h, L.symm.comp_right_fderiv]
  calc ‖(fderiv ℝ (u ∘ (extChartAt I p).symm) (L.symm y)).comp (L.symm : F →L[ℝ] E)‖
      ≤ ‖fderiv ℝ (u ∘ (extChartAt I p).symm) (L.symm y)‖ * ‖(L.symm : F →L[ℝ] E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C₁ * ‖mgradient I u ((extChartAt I p).symm (L.symm y))‖ * ‖(L.symm : F →L[ℝ] E)‖ := by
        gcongr
        exact hcmp _ hy u
    _ = _ := by ring

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

/-- An element `U` of `W^{1,2}(Ω)` whose value and weak gradient are those of a smooth function `u`
read in the chart has norm at most `‖P‖ (1 + ‖L⁻¹‖ C₁)` times the `H¹` norm of `u`, where `P` is a
bounded precomposition with the inverse chart and `C₁` bounds chart derivatives by gradients. -/
private theorem norm_le_mul_norm_ofSmooth {p : M} {r C₁ : ℝ} (L : E ≃L[ℝ] F) {Ω : Opens F}
    (hΩ : ∀ y ∈ Ω, L.symm y ∈ ball (extChartAt I p p) r) (hC₁ : 0 ≤ C₁)
    (hcmp : ∀ y ∈ ball (extChartAt I p p) r, ∀ f : M → ℝ,
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) y‖ ≤ C₁ * ‖mgradient I f ((extChartAt I p).symm y)‖)
    (P : Lp ℝ 2 (riemannianVolume I M) →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set F)))
    (hP : ∀ {g : Lp ℝ 2 (riemannianVolume I M)} {G : M → ℝ}, g =ᵐ[riemannianVolume I M] G →
      P g =ᵐ[volume.restrict (Ω : Set F)] fun y ↦ G ((extChartAt I p).symm (L.symm y)))
    (u : C^∞⟮I, M; ℝ⟯) (U : W1p volume Ω 2)
    (hv : W1p.value U =ᵐ[volume.restrict (Ω : Set F)]
      fun y ↦ u ((extChartAt I p).symm (L.symm y)))
    (hg : W1p.gradient U =ᵐ[volume.restrict (Ω : Set F)]
      ∇ fun y ↦ u ((extChartAt I p).symm (L.symm y))) :
    ‖U‖ ≤ ‖P‖ * (1 + ‖(L.symm : F →L[ℝ] E)‖ * C₁) * ‖ofSmooth u‖ := by
  set c := ‖(L.symm : F →L[ℝ] E)‖ * C₁
  have hc : 0 ≤ c := by positivity
  set n : C(M, ℝ) :=
    ⟨fun x ↦ ‖mgradient I u x‖, continuous_norm_mgradient (u.contMDiff.of_le (by simp))⟩
  set N := ContinuousMap.toLp 2 (riemannianVolume I M) ℝ n
  have hN : ⇑(c • N) =ᵐ[riemannianVolume I M] fun x ↦ c * ‖mgradient I u x‖ := by
    filter_upwards [Lp.coeFn_smul c N, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (riemannianVolume I M) n] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, ContinuousMap.coe_mk]
  -- The value is `P u`, and the gradient is dominated pointwise by `P (c ‖∇u‖)`.
  have hval : W1p.value U = P (toLp (ofSmooth u)) :=
    Lp.ext (hv.trans (hP (toLp_ofSmooth_ae_eq u)).symm)
  have hgrad : ‖W1p.gradient U‖ ≤ ‖P (c • N)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hg, hP hN, ae_restrict_mem Ω.isOpen.measurableSet] with y h1 h2 hy
    rw [h1, h2, Real.norm_of_nonneg (by positivity)]
    exact norm_gradient_comp_le L hcmp u (hΩ y hy)
  calc ‖U‖ ≤ ‖W1p.value U‖ + ‖W1p.gradient U‖ := W1p.norm_le_norm_value_add_norm_gradient _
    _ ≤ ‖P‖ * ‖toLp (ofSmooth u)‖ + ‖P‖ * (c * ‖N‖) := by
        rw [hval]
        refine add_le_add (P.le_opNorm _) (hgrad.trans ((P.le_opNorm _).trans_eq ?_))
        rw [norm_smul, Real.norm_of_nonneg hc]
    _ ≤ ‖P‖ * ‖ofSmooth u‖ + ‖P‖ * (c * ‖ofSmooth u‖) := by
        gcongr
        exacts [norm_toLp_le _, norm_toLp_norm_mgradient_le u]
    _ = ‖P‖ * (1 + c) * ‖ofSmooth u‖ := by ring

omit [FiniteDimensional ℝ F] in
/-- On the preimage under `L⁻¹` of a coordinate ball inside the chart target, where the chart
density is at least `m > 0`, precomposition with the inverse chart is a bounded operator
`L²(M) → L²(Ω)`. -/
private theorem exists_compL_extChartAt_symm {p : M} {r m : ℝ} (L : E ≃L[ℝ] F)
    (hr : ball (extChartAt I p p) r ⊆ (extChartAt I p).target) (hm : 0 < m)
    (hρ : ∀ y ∈ ball (extChartAt I p p) r,
      m ≤ chartVolumeDensity (I := I) p ((extChartAt I p).symm y)) :
    ∃ P : Lp ℝ 2 (riemannianVolume I M) →L[ℝ]
        Lp ℝ 2 (volume.restrict (coordBall (I := I) L p r : Set F)),
      ∀ {g : Lp ℝ 2 (riemannianVolume I M)} {G : M → ℝ}, g =ᵐ[riemannianVolume I M] G →
        P g =ᵐ[volume.restrict (coordBall (I := I) L p r : Set F)]
          fun y ↦ G ((extChartAt I p).symm (L.symm y)) := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : ((volume : Measure F).map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map volume
  -- The image of the Haar measure of `F` is a multiple of the Haar measure of the model space.
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volume : Measure F).map L.symm = c • (Module.finBasis ℝ E).addHaar :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hres : ((volume : Measure F).restrict (coordBall (I := I) L p r : Set F)).map L.symm =
      ((volume : Measure F).map L.symm).restrict (ball (extChartAt I p p) r) :=
    (L.symm.toHomeomorph.toMeasurableEquiv.restrict_map volume _).symm
  have hf : Measurable (ballChartInv (I := I) p r ∘ L.symm) :=
    (measurable_ballChartInv hr).comp L.symm.continuous.measurable
  -- The inverse chart pushes the Haar measure on the coordinate ball forward to at most a finite
  -- multiple of the Riemannian volume.
  have hmap : ((volume : Measure F).restrict (coordBall (I := I) L p r : Set F)).map
      (ballChartInv (I := I) p r ∘ L.symm) ≤ ((c : ℝ≥0∞) * ENNReal.ofReal m⁻¹) •
        riemannianVolume I M := by
    rw [← Measure.map_map (measurable_ballChartInv hr) L.symm.continuous.measurable, hres, hc,
      Measure.restrict_smul, Measure.map_smul, ENNReal.smul_def, mul_smul]
    exacts [smul_le_smul_left _ (map_restrict_ballChartInv_le hr hm hρ),
      (measurable_ballChartInv hr).aemeasurable]
  have hK : (c : ℝ≥0∞) * ENNReal.ofReal m⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  refine ⟨Lp.compOfMapLeSmul ℝ hf hK hmap, fun {g G} hg ↦ ?_⟩
  filter_upwards [Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) hf hK hmap g,
    (QuasiMeasurePreserving.of_map_le_smul hf hmap).ae_eq_comp hg,
    ae_restrict_mem (coordBall (I := I) L p r).isOpen.measurableSet] with y h1 h2 hy
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2, ballChartInv_of_mem (mem_coordBall.1 hy)]

variable [I.Boundaryless]

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- A smooth function read in the chart at `p` through `L` is an element of `W^{1,2}` on the
preimage of a coordinate ball of half the radius of a ball inside the chart target. -/
private theorem exists_w1p_comp_extChartAt_symm {p : M} {r : ℝ} (L : E ≃L[ℝ] F) (hr : 0 < r)
    (hrt : ball (extChartAt I p p) r ⊆ (extChartAt I p).target) (u : C^∞⟮I, M; ℝ⟯) :
    ∃ U : W1p volume (coordBall (I := I) L p (r / 2)) 2,
      W1p.value U =ᵐ[volume.restrict (coordBall (I := I) L p (r / 2) : Set F)]
          (fun y ↦ u ((extChartAt I p).symm (L.symm y))) ∧
        W1p.gradient U =ᵐ[volume.restrict (coordBall (I := I) L p (r / 2) : Set F)]
          ∇ fun y ↦ u ((extChartAt I p).symm (L.symm y)) := by
  have hu : ContDiffOn ℝ 1 (fun y ↦ u ((extChartAt I p).symm (L.symm y)))
      (L.symm ⁻¹' (extChartAt I p).target) :=
    (((u.contMDiff.of_le (by simp)).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p)).contDiffOn).comp L.symm.contDiff.contDiffOn
      (mapsTo_preimage _ _)
  refine W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    ((isOpen_extChartAt_target p).preimage L.symm.continuous) hu
    ((isCompact_closedBall (extChartAt I p p) (r / 2)).image L.continuous) ?_ ?_
  · intro y hy
    exact ⟨L.symm y, ball_subset_closedBall (mem_coordBall.1 hy), L.apply_symm_apply y⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_preimage, L.symm_apply_apply]
    exact hrt (closedBall_subset_ball (by linarith) hz)

/-- **Elements of `H¹(M)` in a chart.** Let `M` be a closed manifold with a continuous Riemannian
metric, `p ∈ M`, and `L` a continuous linear equivalence from the model space to a
finite-dimensional inner product space `F` with a Haar measure. There is an open neighbourhood
`Ω` of the image of `p` under `φ = L ∘ extChartAt I p`, inside the image of the chart, and a
continuous linear map `T : H¹(M) → W^{1,2}(Ω)` reading elements of `H¹(M)` in the chart: for a
smooth function `u`, the value and weak gradient of `T u` are `u ∘ φ⁻¹` and its classical
gradient, and for every `w ∈ H¹(M)` the value of `T w` is the value of `w` in `L²(M)` composed
with `φ⁻¹`. -/
theorem exists_continuousLinearMap_w1p_extChartAt (p : M) (L : E ≃L[ℝ] F) :
    ∃ Ω : Opens F, L (extChartAt I p p) ∈ Ω ∧ MapsTo L.symm Ω (extChartAt I p).target ∧
      ∃ T : SobolevH1 I M →L[ℝ] W1p volume Ω 2,
        (∀ u : C^∞⟮I, M; ℝ⟯,
          W1p.value (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set F)]
              (fun y ↦ u ((extChartAt I p).symm (L.symm y))) ∧
            W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set F)]
              ∇ fun y ↦ u ((extChartAt I p).symm (L.symm y))) ∧
        ∀ w : SobolevH1 I M, W1p.value (T w) =ᵐ[volume.restrict (Ω : Set F)]
          fun y ↦ toLp w ((extChartAt I p).symm (L.symm y)) := by
  obtain ⟨C₁, hC₁, r, hr, hrt, hball⟩ :=
    exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (I := I) (M := M) p
  set Ω := coordBall (I := I) L p (r / 2)
  have hsr : ball (extChartAt I p p) (r / 2) ⊆ ball (extChartAt I p p) r :=
    ball_subset_ball (by linarith)
  -- Precomposition with the inverse chart is a bounded operator `P : L²(M) → L²(Ω)`.
  obtain ⟨P, hP⟩ := exists_compL_extChartAt_symm L (hsr.trans hrt)
    (half_pos (chartVolumeDensity_pos p (FiberBundle.mem_baseSet_trivializationAt' p)))
    fun y hy ↦ (hball y (hsr hy)).2.1.le
  -- Smooth functions read in the chart, with `‖T₀ u‖ ≤ A ‖u‖_{H¹}`.
  choose T₀ hT₀v hT₀g using exists_w1p_comp_extChartAt_symm L hr hrt (M := M)
  have hval (u : C^∞⟮I, M; ℝ⟯) : W1p.value (T₀ u) = P (toLp (ofSmooth u)) :=
    Lp.ext ((hT₀v u).trans (hP (toLp_ofSmooth_ae_eq u)).symm)
  set A := ‖P‖ * (1 + ‖(L.symm : F →L[ℝ] E)‖ * C₁)
  have hbound (u : C^∞⟮I, M; ℝ⟯) : ‖T₀ u‖ ≤ A * ‖ofSmooth u‖ :=
    norm_le_mul_norm_ofSmooth L (fun y hy ↦ hsr (mem_coordBall.1 hy)) hC₁.le
      (fun y hy ↦ (hball y hy).1) P hP u _ (hT₀v u) (hT₀g u)
  -- The linear map on the smooth functions, extended to the completion.
  let T₁ : PreSobolevH1 I M →ₗ[ℝ] W1p volume Ω 2 :=
    { toFun v := T₀ (PreSobolevH1.ofPreSobolevH1 v)
      map_add' v w := W1p.ext_value <| by
        simp only [← W1p.valueL_apply, map_add]
        simp only [W1p.valueL_apply, hval, map_add]
      map_smul' a v := W1p.ext_value <| by
        simp only [← W1p.valueL_apply, map_smul]
        simp only [W1p.valueL_apply, hval, map_smul, RingHom.id_apply] }
  have hT₁u (u : C^∞⟮I, M; ℝ⟯) : T₁ (PreSobolevH1.toPreSobolevH1 u) = T₀ u := by
    simp only [T₁, LinearMap.coe_mk, AddHom.coe_mk, PreSobolevH1.ofPreSobolevH1_toPreSobolevH1]
  have hT₁ (v : PreSobolevH1 I M) : ‖T₁ v‖ ≤ A * ‖v‖ := by
    obtain ⟨u, rfl⟩ := PreSobolevH1.toPreSobolevH1.surjective v
    have := hbound u
    rwa [ofSmooth_apply, UniformSpace.Completion.norm_coe, ← hT₁u] at this
  set T := (T₁.mkContinuous A hT₁).fromCompletion
  have hTu (u : C^∞⟮I, M; ℝ⟯) : T (ofSmooth u) = T₀ u := by
    rw [ofSmooth_apply, ContinuousLinearMap.fromCompletion_apply_coe,
      LinearMap.mkContinuous_apply, hT₁u]
  -- By density, the value of `T w` is `P` applied to the value of `w`.
  have hTP : W1p.valueL.comp T = P.comp toLp := by
    ext1 w
    induction w using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | h u =>
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, W1p.valueL_apply,
        hTu, hval]
  refine ⟨Ω, ?_, fun y hy ↦ hrt (hsr hy), T, fun u ↦ ?_, fun w ↦ ?_⟩
  · refine mem_coordBall.2 ?_
    rw [L.symm_apply_apply]
    exact mem_ball_self (half_pos hr)
  · rw [hTu]
    exact ⟨hT₀v u, hT₀g u⟩
  · have h := congr($hTP w)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, W1p.valueL_apply] at h
    rw [h]
    exact hP (Filter.EventuallyEq.refl _ _)

end TauCeti.Manifold.SobolevH1
