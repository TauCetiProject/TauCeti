/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# `H¹(M)` is the space of functions that are `W^{1,2}` in charts

Let `M` be a closed smooth manifold with a continuous Riemannian metric, and let
`H¹(M)` (`TauCeti.Manifold.SobolevH1`) be the completion of the smooth functions on `M` for the
norm `(∫ u² dV + ∫ ‖∇u‖² dV)^(1/2)`. This file proves that the completion is the Sobolev space
defined in charts: a function `f ∈ L²(M)` is the value of an element of `H¹(M)` exactly when,
near every point `p`, its reading `f ∘ φ⁻¹` in the chart `φ = L ∘ extChartAt I p` agrees almost
everywhere with an element of `W^{1,2}(Ω)` on an open set `Ω` of coordinates around `φ p`
(`TauCeti.Manifold.SobolevH1.exists_toLp_eq_iff_forall_exists_w1p`).

One direction is the chart reading `H¹(M) → W^{1,2}(Ω)`
(`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`). The converse
(`TauCeti.Manifold.SobolevH1.exists_toLp_eq_of_forall_exists_w1p`) says that every function which
is locally `W^{1,2}` in charts is approximated in the `H¹` norm by smooth functions on `M`.

## The argument

The statement is local. Near a point `p`, the chart density is bounded and the Riemannian length
of a gradient is at most a fixed multiple of the length of the coordinate gradient
(`TauCeti.Manifold.eventually_norm_mgradient_le_mul_norm_fderiv_comp_extChartAt_symm`). Hence a
smooth function `Φ` on `M` supported in a fixed compact set `Q` of the chart neighbourhood, and
equal to a test function `ϑ` in the chart, has `‖Φ‖_{H¹} ≤ A ‖ϑ‖_{W^{1,2}}` with `A` independent
of `Φ`; this uses the comparison of integrals over a chart neighbourhood with integrals in
coordinates (`TauCeti.exists_setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm`).

Let `χ` be a smooth function supported near `p`. In the chart, `χ f` is the product of the chart
reading of `f`, an element of `W^{1,2}(Ω)`, with a compactly supported smooth function, so it is
an element `v` of `W^{1,2}` of the whole coordinate space with compact support
(`TauCeti.W1p.exists_top_value_gradient_ae_eq_mul_sub_const`). Test functions are dense in it
(`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`); after multiplying them by a fixed cutoff equal to
`1` on the support of `v`, the approximants `ϑₙ` are supported in a fixed compact set. Transplanted
to `M` they give smooth functions `Φₙ` (`TauCeti.Manifold.exists_contMDiff_comp_extChartAt_symm_eq`)
which form a Cauchy sequence in `H¹(M)` by the estimate above, and whose values converge to `χ f`
in `L²(M)`. So `χ f` is the value of the limit. A smooth partition of unity subordinate to such
neighbourhoods writes `f` as a finite sum of functions `χ f`.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_toLp_eq_of_forall_exists_w1p`: a function in `L²(M)` which is
  `W^{1,2}` in a chart near every point is the value of an element of `H¹(M)`.
* `TauCeti.Manifold.SobolevH1.exists_toLp_eq_iff_forall_exists_w1p`: the characterization of the
  values of `H¹(M)` in `L²(M)` by charts.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §2.2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
-/

public section

open Bundle Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
/-- If `L⁻¹` maps a set `B` of coordinates into the chart target at `p`, the chart image of a
subset `S` of `B` lies in the chart neighbourhood of `B`. -/
private theorem image_symm_subset_source_inter_preimage {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (p : M) {S B : Set F} (hSB : S ⊆ B)
    (hBt : ∀ y ∈ B, L.symm y ∈ (extChartAt I p).target) :
    (extChartAt I p).symm '' (L.symm '' S) ⊆
      (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' B) := by
  rw [(extChartAt I p).symm_image_eq_source_inter_preimage
    (image_subset_iff.2 fun y hy ↦ hBt y (hSB hy))]
  exact inter_subset_inter_right _ (preimage_mono (image_mono hSB))

variable [I.Boundaryless] [CompactSpace M] [T2Space M] [IsManifold I ∞ M] [MeasurableSpace M]
  [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

omit [I.Boundaryless] [T2Space M] [FiniteDimensional ℝ F] in
/-- The `L²` norm of a function vanishing outside the chart neighbourhood of an open set `V` of
coordinates is at most a constant multiple, independent of the function, of the `L²(V)` norm of
its reading in the chart. -/
private theorem exists_eLpNorm_le_mul_eLpNorm_comp (L : E ≃L[ℝ] F) (p : M)
    {V K : Set F} (hV : IsOpen V) (hK : IsCompact K) (hVK : V ⊆ K)
    (hKt : MapsTo L.symm K (extChartAt I p).target) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : M → ℝ, AEStronglyMeasurable g (riemannianVolume I M) →
      (∀ᵐ x ∂riemannianVolume I M,
        x ∉ (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' V) → g x = 0) →
      eLpNorm g 2 (riemannianVolume I M) ≤
        C * eLpNorm (fun y ↦ g ((extChartAt I p).symm (L.symm y))) 2 (volume.restrict V) := by
  obtain ⟨C, hC, hle⟩ :=
    exists_setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm (I := I) (M := M)
      L p hV hK hVK hKt
  have hC1 : C + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hC, ENNReal.one_ne_top⟩
  refine ⟨(C + 1) ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC1,
    fun g hgm hg ↦ ?_⟩
  by_cases hgψ : AEStronglyMeasurable (fun y ↦ g ((extChartAt I p).symm (L.symm y)))
    (volume.restrict V)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hgψ, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.rpow_pos (by positivity) hC1).ne'
  set S := (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' V)
  have hS : MeasurableSet S :=
    (isOpen_extChartAt_preimage' p (L.symm.toHomeomorph.isOpenMap _ hV)).measurableSet
  have hgS : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M =
      ∫⁻ x in S, ‖g x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M := by
    rw [← lintegral_indicator hS]
    refine lintegral_congr_ae ?_
    filter_upwards [hg] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS, hx hxS, eNorm_zero, ENNReal.zero_rpow_of_pos two_pos]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hgm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hgψ]
  simp only [ENNReal.toReal_ofNat]
  rw [hgS, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow ((hle _).trans (by gcongr; exact le_self_add)) (by norm_num)

omit [I.Boundaryless] [T2Space M] in
/-- An `L²` bound by a multiple of the `L²` norm of an element of an `Lp` space, read as a bound on
real norms. -/
private theorem toReal_eLpNorm_le_mul_norm {X α : Type*} [NormedAddCommGroup X]
    [MeasurableSpace α] {g : M → ℝ} {ν : Measure α} {h : Lp X 2 ν} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hgh : eLpNorm g 2 (riemannianVolume I M) ≤ C * eLpNorm h 2 ν) :
    (eLpNorm g 2 (riemannianVolume I M)).toReal ≤ C.toReal * ‖h‖ := by
  rw [Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.eLpNorm_ne_top _)) hgh

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [IsManifold I ∞ M] [MeasurableSpace M]
  [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
/-- The `L²` norm on a subset `V` of a function agreeing almost everywhere with the coercion of
an element of `Lp` over the whole space is at most the norm of that element. -/
private theorem eLpNorm_restrict_le_of_ae_eq {X : Type*} [NormedAddCommGroup X] {f g : F → X}
    (hfg : g =ᵐ[volume] f) (V : Set F) :
    eLpNorm f 2 (volume.restrict V) ≤ eLpNorm g 2 (volume.restrict ((⊤ : Opens F) : Set F)) :=
  calc eLpNorm f 2 (volume.restrict V) ≤ eLpNorm f 2 volume := eLpNorm_restrict_le _ _ _ _
    _ = eLpNorm g 2 volume := eLpNorm_congr_ae hfg.symm
    _ ≤ eLpNorm g 2 (volume.restrict ((⊤ : Opens F) : Set F)) :=
        eLpNorm_mono_measure _ (le_of_eq (by simp))

omit [I.Boundaryless] [T2Space M] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure] in
/-- The `H¹` norm of a smooth function is at most `a + b` when the `L²` norms of the function and
of the length of its gradient are at most `a` and `b`. -/
private theorem norm_ofSmooth_le_add {Φ : C^∞⟮I, M; ℝ⟯} {a b : ℝ}
    (ha : ‖toLp (ofSmooth Φ)‖ ≤ a)
    (hb : ‖ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨fun x ↦ ‖mgradient I Φ x‖,
      continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))⟩‖ ≤ b) :
    ‖ofSmooth Φ‖ ≤ a + b := by
  have hsq : ‖ofSmooth Φ‖ ^ 2 = ‖toLp (ofSmooth Φ)‖ ^ 2 +
      ‖ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨fun x ↦ ‖mgradient I Φ x‖,
        continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))⟩‖ ^ 2 := by
    rw [norm_ofSmooth_sq, ← integral_toLp_sq_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ContinuousMap.inner_toLp]
    simp only [ContinuousMap.coe_mk, conj_trivial, ← sq]
    congr 1
    exact integral_congr_ae ((toLp_ofSmooth_ae_eq Φ).mono fun x hx ↦ by simp only [hx])
  have ha0 := (norm_nonneg _).trans ha
  have hb0 := (norm_nonneg _).trans hb
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hsq]
  nlinarith [norm_nonneg (toLp (ofSmooth Φ)), norm_nonneg (ContinuousMap.toLp 2
    (riemannianVolume I M) ℝ ⟨fun x ↦ ‖mgradient I Φ x‖,
      continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))⟩)]

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure] in
/-- If on the coordinate ball of radius `r` around `y₀ = L (φ p)` the length of a gradient is at
most `C₂` times the length of the coordinate derivative, then the gradient of a function `Φ` on `M`
agreeing in the chart with a differentiable `ϑ` on that ball is at most `C₂ ‖L‖ ‖∇ϑ‖` there. -/
private theorem norm_mgradient_le_of_forall_eq (L : E ≃L[ℝ] F) (p : M) {r C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hgrad : ∀ y ∈ ball (L (extChartAt I p p)) r, ∀ f : M → ℝ,
      DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) (L.symm y) →
      ‖mgradient I f ((extChartAt I p).symm (L.symm y))‖ ≤
        C₂ * ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (L.symm y)‖)
    {Φ : M → ℝ} {ϑ : F → ℝ} (hϑ : Differentiable ℝ ϑ)
    (hΦϑ : ∀ y ∈ ball (L (extChartAt I p p)) r, Φ ((extChartAt I p).symm (L.symm y)) = ϑ y)
    {y : F} (hy : y ∈ ball (L (extChartAt I p p)) r) :
    ‖mgradient I Φ ((extChartAt I p).symm (L.symm y))‖ ≤
      C₂ * ‖(L : E →L[ℝ] F)‖ * ‖∇ ϑ y‖ := by
  -- Near `L⁻¹ y` the coordinate expression of `Φ` is `ϑ ∘ L`.
  have hev : (Φ ∘ (extChartAt I p).symm) =ᶠ[𝓝 (L.symm y)] (ϑ ∘ L) := by
    have hU : L ⁻¹' ball (L (extChartAt I p p)) r ∈ 𝓝 (L.symm y) :=
      (isOpen_ball.preimage L.continuous).mem_nhds (by simpa using hy)
    filter_upwards [hU] with z hz
    simpa using hΦϑ (L z) hz
  have hfd : fderiv ℝ (Φ ∘ (extChartAt I p).symm) (L.symm y) =
      (fderiv ℝ ϑ y).comp (L : E →L[ℝ] F) := by
    rw [hev.fderiv_eq, L.comp_right_fderiv, L.apply_symm_apply]
  refine (hgrad y hy Φ ((hϑ.differentiableAt.comp _ L.differentiableAt).congr_of_eventuallyEq
    hev)).trans ?_
  rw [hfd, norm_gradient_eq_norm_fderiv, mul_assoc, mul_comm ‖(L : E →L[ℝ] F)‖]
  gcongr
  exact ContinuousLinearMap.opNorm_comp_le _ _

omit [I.Boundaryless] [T2Space M] in
/-- If the `L²(M)` norm of the length of the gradient of a smooth `Φ` is at most `C` times the
`L²(V)` norm of its reading through `ψ : F → M`, and that reading is at most `K ‖∇ϑ‖` on `V` for
a test function `ϑ`, then the length of the gradient of `Φ` has `L²` norm at most
`C K ‖ϑ‖_{W^{1,2}}`. -/
private theorem norm_toLp_norm_mgradient_le_of_ae_le {ψ : F → M} {V : Set F} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) {K : ℝ} (hK : 0 ≤ K) {Φ : C^∞⟮I, M; ℝ⟯} {ϑ : 𝓓((⊤ : Opens F), ℝ)}
    (h1 : eLpNorm (fun x ↦ ‖mgradient I Φ x‖) 2 (riemannianVolume I M) ≤
      C * eLpNorm (fun y ↦ ‖mgradient I Φ (ψ y)‖) 2 (volume.restrict V))
    (hmeas : AEStronglyMeasurable (fun y ↦ ‖mgradient I Φ (ψ y)‖) (volume.restrict V))
    (hpt : ∀ᵐ y ∂volume.restrict V, ‖‖mgradient I Φ (ψ y)‖‖ ≤ K * ‖∇ (ϑ : F → ℝ) y‖) :
    ‖ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨fun x ↦ ‖mgradient I Φ x‖,
      continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))⟩‖ ≤
      C.toReal * K * ‖W1p.ofTestFunctionₗ volume ⊤ 2 ϑ‖ := by
  set u := W1p.ofTestFunctionₗ volume ⊤ 2 ϑ
  have hgr : eLpNorm (fun x ↦ ‖mgradient I Φ x‖) 2 (riemannianVolume I M) ≤
      C * (ENNReal.ofReal K *
        eLpNorm (W1p.gradient u) 2 (volume.restrict ((⊤ : Opens F) : Set F))) := by
    refine h1.trans ?_
    gcongr
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpt 2).trans ?_
    gcongr
    exact eLpNorm_restrict_le_of_ae_eq (W1p.gradient_ofTestFunctionₗ_top_ae ϑ) V
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _)]
  calc (eLpNorm (fun x ↦ ‖mgradient I Φ x‖) 2 (riemannianVolume I M)).toReal
      ≤ (C * (ENNReal.ofReal K *
          eLpNorm (W1p.gradient u) 2 (volume.restrict ((⊤ : Opens F) : Set F)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _))) hgr
    _ = C.toReal * K * ‖W1p.gradient u‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK, Lp.norm_def]
        ring
    _ ≤ C.toReal * K * ‖u‖ := by gcongr; exact W1p.norm_gradient_le _

omit [I.Boundaryless] in
/-- **The `H¹` norm of a function transplanted from a chart.** Let `r > R > 0` be such that on
the coordinate ball of radius `r` around `y₀ = L (φ p)` the inverse chart is defined and the
length of a gradient is at most `C₂` times the length of the coordinate derivative, and let `Kθ`
be a compact subset of the ball of radius `R`. A smooth function `Φ` on `M` vanishing outside the
chart image of `Kθ`, which in the chart agrees with a test function `ϑ`, has `H¹` norm at most a
constant multiple, independent of `Φ` and `ϑ`, of the `W^{1,2}` norm of `ϑ`. -/
private theorem exists_norm_ofSmooth_le (L : E ≃L[ℝ] F) (p : M) {r R C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hrt : ∀ y ∈ ball (L (extChartAt I p p)) r, L.symm y ∈ (extChartAt I p).target)
    (hgrad : ∀ y ∈ ball (L (extChartAt I p p)) r, ∀ f : M → ℝ,
      DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) (L.symm y) →
      ‖mgradient I f ((extChartAt I p).symm (L.symm y))‖ ≤
        C₂ * ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (L.symm y)‖)
    (hRr : R < r) {Kθ : Set F} (hKθ : IsCompact Kθ) (hKθR : Kθ ⊆ ball (L (extChartAt I p p)) R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Φ : C^∞⟮I, M; ℝ⟯) (ϑ : 𝓓((⊤ : Opens F), ℝ)),
      (∀ x ∉ (extChartAt I p).symm '' (L.symm '' Kθ), Φ x = 0) →
      (∀ y ∈ ball (L (extChartAt I p p)) r, Φ ((extChartAt I p).symm (L.symm y)) = ϑ y) →
      ‖ofSmooth Φ‖ ≤ A * ‖W1p.ofTestFunctionₗ volume ⊤ 2 ϑ‖ := by
  set φ := extChartAt I p
  set y₀ := L (φ p)
  set V := ball y₀ R
  have hKt : MapsTo L.symm (closedBall y₀ R) φ.target :=
    fun y hy ↦ hrt y (closedBall_subset_ball hRr hy)
  obtain ⟨C, hC, hE2⟩ := exists_eLpNorm_le_mul_eLpNorm_comp (I := I) L p isOpen_ball
    (isCompact_closedBall y₀ R) ball_subset_closedBall hKt
  set Q := φ.symm '' (L.symm '' Kθ)
  have hVt (y : F) (hy : y ∈ V) : L.symm y ∈ φ.target := hrt y (ball_subset_ball hRr.le hy)
  have hQ : IsClosed Q :=
    ((hKθ.image L.symm.continuous).image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono
        (image_subset_iff.2 fun y hy ↦ hVt y (hKθR hy)))).isClosed
  have hQS : Q ⊆ φ.source ∩ φ ⁻¹' (L.symm '' V) :=
    image_symm_subset_source_inter_preimage L p hKθR hVt
  have hvan (g : M → ℝ) (hg : ∀ x ∉ Q, g x = 0) :
      ∀ᵐ x ∂riemannianVolume I M, x ∉ φ.source ∩ φ ⁻¹' (L.symm '' V) → g x = 0 :=
    Eventually.of_forall fun x hx ↦ hg x fun hxQ ↦ hx (hQS hxQ)
  have hψV : ContinuousOn (fun y ↦ φ.symm (L.symm y)) V :=
    (continuousOn_extChartAt_symm p).comp L.symm.continuous.continuousOn hVt
  set nL := ‖(L : E →L[ℝ] F)‖
  refine ⟨C.toReal * (1 + C₂ * nL), by positivity, fun Φ ϑ hΦQ hΦϑ ↦ ?_⟩
  set u := W1p.ofTestFunctionₗ volume ⊤ 2 ϑ
  have hΦϑV : ∀ᵐ y ∂volume.restrict V, Φ (φ.symm (L.symm y)) = ϑ y :=
    (ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun y hy ↦ hΦϑ y (ball_subset_ball hRr.le hy))
  -- The value part: `‖Φ‖_{L²(M)} ≤ C ‖ϑ‖_{L²}`.
  have hval : ‖toLp (ofSmooth Φ)‖ ≤ C.toReal * ‖u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (toLp_ofSmooth_ae_eq Φ)]
    refine (toReal_eLpNorm_le_mul_norm hC ((hE2 Φ (map_continuous Φ).aestronglyMeasurable
      (hvan Φ hΦQ)).trans ?_)).trans (by gcongr; exact W1p.norm_value_le _)
    rw [eLpNorm_congr_ae hΦϑV]
    gcongr
    exact eLpNorm_restrict_le_of_ae_eq (W1p.value_ofTestFunctionₗ_top_ae ϑ) V
  -- The gradient part: `‖∇Φ‖_{L²(M)} ≤ C C₂ ‖L‖ ‖∇ϑ‖_{L²}`.
  refine (norm_ofSmooth_le_add (b := C.toReal * (C₂ * nL) * ‖u‖) hval ?_).trans_eq (by ring)
  have hpt : ∀ᵐ y ∂volume.restrict V,
      ‖‖mgradient I Φ (φ.symm (L.symm y))‖‖ ≤ (C₂ * nL) * ‖∇ (ϑ : F → ℝ) y‖ := by
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦ ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_mgradient_le_of_forall_eq L p hC₂ hgrad (ϑ.contDiff.differentiable (by simp))
      hΦϑ (ball_subset_ball hRr.le hy)
  have htsQ : tsupport (Φ : M → ℝ) ⊆ Q :=
    closure_minimal (fun z hz ↦ not_not.1 fun hzQ ↦ hz (hΦQ z hzQ)) hQ
  exact norm_toLp_norm_mgradient_le_of_ae_le hC (by positivity)
    (hE2 _ (continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))).aestronglyMeasurable
      (hvan _ fun x hx ↦ by rw [mgradient_eq_zero_of_notMem_tsupport fun h ↦ hx (htsQ h),
        norm_zero]))
    (((continuous_norm_mgradient (Φ.contMDiff.of_le (by simp))).comp_continuousOn
      hψV).aestronglyMeasurable measurableSet_ball) hpt

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure] in
/-- A smooth function `χ` on `M` supported in the chart image of the coordinate ball of radius
`r / 4` around `y₀ = L (φ p)`, read in the chart, extends to a smooth function on `F` supported in
the closed ball of radius `r / 2`, provided the inverse chart is defined on the ball of radius
`r`. -/
private theorem exists_contDiff_eq_comp (L : E ≃L[ℝ] F) (p : M) {r : ℝ} (hr : 0 < r)
    (hrt : ∀ y ∈ ball (L (extChartAt I p p)) r, L.symm y ∈ (extChartAt I p).target)
    {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hχN : tsupport χ ⊆ (extChartAt I p).source ∩
      extChartAt I p ⁻¹' (L.symm '' ball (L (extChartAt I p p)) (r / 4))) :
    ∃ χF : F → ℝ, ContDiff ℝ ∞ χF ∧ HasCompactSupport χF ∧
      tsupport χF ⊆ closedBall (L (extChartAt I p p)) (r / 2) ∧
      ∀ y ∈ ball (L (extChartAt I p p)) r, χF y = χ ((extChartAt I p).symm (L.symm y)) := by
  set φ := extChartAt I p
  set y₀ := L (φ p)
  -- Cut `χ ∘ φ⁻¹ ∘ L⁻¹` off with a bump equal to `1` on the ball of radius `r / 4`.
  let b : ContDiffBump y₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbr : closedBall y₀ (r / 2) ⊆ ball y₀ r := closedBall_subset_ball (by linarith)
  -- Read in `E`, the bump `b ∘ L` is supported in the chart target.
  have hbt : tsupport (fun z ↦ b (L z)) ⊆ φ.target := by
    refine (closure_minimal (t := L ⁻¹' closedBall y₀ (r / 2)) (fun z hz ↦ ?_)
      (isClosed_closedBall.preimage L.continuous)).trans fun z hz ↦ ?_
    · exact b.tsupport_eq.subset (subset_tsupport _ hz)
    · simpa using hrt (L z) (hbr hz)
  refine ⟨fun y ↦ b y * χ (φ.symm (L.symm y)), ?_, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans b.tsupport_eq.subset, fun y hy ↦ ?_⟩
  · convert ((b.contDiff.comp L.contDiff).mul_comp_extChartAt_symm hbt hχ).comp
      L.symm.contDiff using 1
    ext y
    simp only [Function.comp_apply, L.apply_symm_apply, φ]
  · by_cases hyb : y ∈ closedBall y₀ (r / 4)
    · simp only [b.one_of_mem_closedBall hyb, one_mul]
    · -- Off the ball of radius `r / 4`, the point `φ⁻¹ (L⁻¹ y)` is outside the support of `χ`.
      have h0 : χ (φ.symm (L.symm y)) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h ↦ hyb ?_
        obtain ⟨-, z, hz, hzy⟩ := hχN h
        rw [φ.right_inv (hrt y hy)] at hzy
        rw [← L.symm.injective hzy]
        exact ball_subset_closedBall hz
      simp only [h0, mul_zero]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
/-- A test function supported in a compact subset `S` of the coordinate ball of radius `r` around
`L (φ p)`, on which the inverse chart is defined, transplanted to `M`: a smooth function vanishing
outside the chart image of `S` which agrees with the test function in the chart on the ball. -/
private theorem exists_contMDiff_eq_testFunction (L : E ≃L[ℝ] F) (p : M) {r : ℝ}
    (hrt : ∀ y ∈ ball (L (extChartAt I p p)) r, L.symm y ∈ (extChartAt I p).target)
    {S : Set F} (hS : IsCompact S) (hSr : S ⊆ ball (L (extChartAt I p p)) r)
    (ϑ : 𝓓((⊤ : Opens F), ℝ)) (hϑS : tsupport (ϑ : F → ℝ) ⊆ S) :
    ∃ Φ : C^∞⟮I, M; ℝ⟯, (∀ x ∉ (extChartAt I p).symm '' (L.symm '' S), Φ x = 0) ∧
      ∀ y ∈ ball (L (extChartAt I p p)) r, Φ ((extChartAt I p).symm (L.symm y)) = ϑ y := by
  have hwts : tsupport (fun z ↦ ϑ (L z)) ⊆ L.symm '' S :=
    closure_minimal (fun z hz ↦ ⟨L z, hϑS (subset_tsupport _ hz), L.symm_apply_apply z⟩)
      (hS.image L.symm.continuous).isClosed
  have hwt : tsupport (fun z ↦ ϑ (L z)) ⊆ (extChartAt I p).target :=
    hwts.trans (image_subset_iff.2 fun y hy ↦ hrt y (hSr hy))
  obtain ⟨Φ₀, hΦ₀, -, hΦ₀supp, hΦ₀eq⟩ := exists_contMDiff_comp_extChartAt_symm_eq (I := I)
    (n := ∞) (c := p) (ϑ.contDiff.comp L.contDiff)
    (ϑ.hasCompactSupport.comp_homeomorph L.toHomeomorph) hwt
  refine ⟨⟨Φ₀, hΦ₀⟩, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · exact image_eq_zero_of_notMem_tsupport fun h ↦ hx (image_mono hwts (hΦ₀supp h))
  · rw [ContMDiffMap.coeFn_mk, hΦ₀eq _ (hrt y hy), Function.comp_apply, L.apply_symm_apply]

omit [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
/-- Inside every neighbourhood `Ω` of `L (φ p)` there is a coordinate ball around `L (φ p)` on
which the inverse chart is defined and the length of a gradient is at most a fixed multiple of
the length of the coordinate derivative. -/
private theorem exists_ball_subset_and_norm_mgradient_le (L : E ≃L[ℝ] F) (p : M) {Ω : Set F}
    (hΩ : Ω ∈ 𝓝 (L (extChartAt I p p))) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ r > 0, ball (L (extChartAt I p p)) r ⊆ Ω ∧
      (∀ y ∈ ball (L (extChartAt I p p)) r, L.symm y ∈ (extChartAt I p).target) ∧
      ∀ y ∈ ball (L (extChartAt I p p)) r, ∀ g : M → ℝ,
        DifferentiableAt ℝ (g ∘ (extChartAt I p).symm) (L.symm y) →
        ‖mgradient I g ((extChartAt I p).symm (L.symm y))‖ ≤
          C₂ * ‖fderiv ℝ (g ∘ (extChartAt I p).symm) (L.symm y)‖ := by
  set φ := extChartAt I p
  obtain ⟨C₂, hC₂, hgradp⟩ :=
    exists_eventually_norm_mgradient_le_mul_norm_fderiv_comp_extChartAt_symm (I := I) (M := M) p
  have hL : Tendsto L.symm (𝓝 (L (φ p))) (𝓝 (φ p)) := by
    simpa using L.symm.continuous.tendsto (L (φ p))
  have hψ : Tendsto (fun y ↦ φ.symm (L.symm y)) (𝓝 (L (φ p))) (𝓝 p) := by
    have h := continuousAt_extChartAt_symm (I := I) p
    rw [ContinuousAt, extChartAt_to_inv] at h
    exact h.comp hL
  obtain ⟨r, hr, hgood⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ y in 𝓝 (L (φ p)), y ∈ Ω from hΩ).and
      ((hL.eventually (extChartAt_target_mem_nhds (I := I) p)).and (hψ.eventually hgradp)))
  refine ⟨C₂, hC₂.le, r, hr, fun y hy ↦ (hgood y hy).1, fun y hy ↦ (hgood y hy).2.1,
    fun y hy g hg ↦ ?_⟩
  have h := (hgood y hy).2.2 g
  rw [φ.right_inv (hgood y hy).2.1] at h
  exact h hg

omit [I.Boundaryless] [T2Space M] in
/-- Let the `L²` norm of a function vanishing outside the chart neighbourhood `S_B` of a set `B`
of coordinates be at most `C` times the `L²(B)` norm of its reading in the chart. If a smooth `Φ`
and `g ∈ L²(M)` vanish outside `S_B`, and in the chart `Φ - g` agrees almost everywhere on `B`
with `ϑ - v` for a test function `ϑ` and `v ∈ W^{1,2}`, then `‖Φ - g‖_{L²(M)}` is at most
`C ‖ϑ - v‖_{W^{1,2}}`. -/
private theorem norm_toLp_ofSmooth_sub_le (L : E ≃L[ℝ] F) (p : M) {B : Set F} {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (hE2 : ∀ g : M → ℝ, AEStronglyMeasurable g (riemannianVolume I M) →
      (∀ᵐ x ∂riemannianVolume I M,
        x ∉ (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' B) → g x = 0) →
      eLpNorm g 2 (riemannianVolume I M) ≤
        C * eLpNorm (fun y ↦ g ((extChartAt I p).symm (L.symm y))) 2 (volume.restrict B))
    (Φ : C^∞⟮I, M; ℝ⟯) {g : M → ℝ} (hg : MemLp g 2 (riemannianVolume I M))
    (hvan : ∀ x ∉ (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' B), Φ x = 0 ∧ g x = 0)
    (ϑ : 𝓓((⊤ : Opens F), ℝ)) (v : W1p volume ⊤ 2)
    (hcoord : ∀ᵐ y ∂volume.restrict B, Φ ((extChartAt I p).symm (L.symm y)) -
      g ((extChartAt I p).symm (L.symm y)) = ϑ y - W1p.value v y) :
    ‖toLp (ofSmooth Φ) - hg.toLp g‖ ≤ C.toReal * ‖W1p.ofTestFunctionₗ volume ⊤ 2 ϑ - v‖ := by
  set u := W1p.ofTestFunctionₗ volume ⊤ 2 ϑ - v
  have heq : ⇑(toLp (ofSmooth Φ) - hg.toLp g) =ᵐ[riemannianVolume I M] fun x ↦ Φ x - g x := by
    filter_upwards [Lp.coeFn_sub (toLp (ofSmooth Φ)) (hg.toLp g), toLp_ofSmooth_ae_eq Φ,
      hg.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hu : (W1p.value u : F → ℝ) =ᵐ[volume] fun y ↦ ϑ y - W1p.value v y := by
    filter_upwards [(ae_restrict_iff' (⊤ : Opens F).isOpen.measurableSet).1
        (W1p.value_sub_ae (W1p.ofTestFunctionₗ volume ⊤ 2 ϑ) v),
      W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) ϑ] with y h1 h2
    rw [h1 (by simp), Pi.sub_apply, h2]
  rw [Lp.norm_def, eLpNorm_congr_ae heq]
  refine (toReal_eLpNorm_le_mul_norm hC ((hE2 (fun x ↦ Φ x - g x)
    ((map_continuous Φ).aestronglyMeasurable.sub hg.aestronglyMeasurable)
    (Eventually.of_forall fun x hx ↦ by rw [(hvan x hx).1, (hvan x hx).2, sub_zero])).trans
      ?_)).trans (by gcongr; exact W1p.norm_value_le _)
  rw [eLpNorm_congr_ae hcoord]
  gcongr
  exact eLpNorm_restrict_le_of_ae_eq hu B

omit [I.Boundaryless] in
/-- **A limit of transplanted test functions lies in `H¹(M)`.** Let `r > 0` be such that on the
coordinate ball of radius `r` around `y₀ = L (φ p)` the inverse chart is defined and the length of
a gradient is at most `C₂` times the length of the coordinate derivative. Let test functions `ϑₙ`,
supported in a fixed compact subset `S` of the ball `B` of radius `3r/4`, converge in `W^{1,2}` to
`v`. If `g ∈ L²(M)` vanishes outside the chart image of `B` and reads `v` in the chart on `B`, then
`g` is the value of an element of `H¹(M)`: the limit of the test functions transplanted to `M`. -/
private theorem exists_toLp_ae_eq_of_tendsto_ofTestFunctionₗ (L : E ≃L[ℝ] F) (p : M)
    {r C₂ : ℝ} (hr : 0 < r) (hC₂ : 0 ≤ C₂)
    (hrt : ∀ y ∈ ball (L (extChartAt I p p)) r, L.symm y ∈ (extChartAt I p).target)
    (hgrad : ∀ y ∈ ball (L (extChartAt I p p)) r, ∀ f : M → ℝ,
      DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) (L.symm y) →
      ‖mgradient I f ((extChartAt I p).symm (L.symm y))‖ ≤
        C₂ * ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (L.symm y)‖)
    {S : Set F} (hSc : IsCompact S) (hSB : S ⊆ ball (L (extChartAt I p p)) (3 * r / 4))
    {ϑ : ℕ → 𝓓((⊤ : Opens F), ℝ)} (hϑS : ∀ n, tsupport (ϑ n : F → ℝ) ⊆ S)
    {v : W1p volume ⊤ 2} (hϑ : Tendsto (fun n ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (ϑ n)) atTop (𝓝 v))
    {g : M → ℝ} (hg : MemLp g 2 (riemannianVolume I M))
    (hg0 : ∀ x ∉ (extChartAt I p).source ∩
      extChartAt I p ⁻¹' (L.symm '' ball (L (extChartAt I p p)) (3 * r / 4)), g x = 0)
    (hgv : ∀ᵐ y ∂volume.restrict (ball (L (extChartAt I p p)) (3 * r / 4)),
      g ((extChartAt I p).symm (L.symm y)) = W1p.value v y) :
    ∃ w : SobolevH1 I M, toLp w =ᵐ[riemannianVolume I M] g := by
  set φ := extChartAt I p
  set y₀ := L (φ p)
  have hBr : ball y₀ (3 * r / 4) ⊆ ball y₀ r := ball_subset_ball (by linarith)
  obtain ⟨A, hA, hE1⟩ := exists_norm_ofSmooth_le (I := I) L p hC₂ hrt hgrad
    (by linarith : 3 * r / 4 < r) hSc hSB
  obtain ⟨C, hC, hE2⟩ := exists_eLpNorm_le_mul_eLpNorm_comp (I := I) L p
    (V := ball y₀ (3 * r / 4)) isOpen_ball (isCompact_closedBall y₀ (3 * r / 4))
    ball_subset_closedBall fun y hy ↦ hrt y (closedBall_subset_ball (by linarith) hy)
  -- The test functions `ϑ n`, transplanted to `M`.
  have hlift (n : ℕ) := exists_contMDiff_eq_testFunction L p hrt hSc (hSB.trans hBr) (ϑ n) (hϑS n)
  choose Φs hΦs0 hΦsϑ using hlift
  -- They form a Cauchy sequence in `H¹(M)`, since `‖Φ‖_{H¹} ≤ A ‖ϑ‖_{W^{1,2}}`.
  have hcauchy : CauchySeq fun n ↦ ofSmooth (Φs n) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hϑ.cauchySeq (ε / (A + 1)) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm, ← map_sub]
    calc ‖ofSmooth (Φs m - Φs n)‖ ≤ A * dist (W1p.ofTestFunctionₗ volume ⊤ 2 (ϑ m))
          (W1p.ofTestFunctionₗ volume ⊤ 2 (ϑ n)) := by
          rw [dist_eq_norm, ← map_sub]
          refine hE1 _ _ (fun x hx ↦ ?_) (fun y hy ↦ ?_)
          · rw [ContMDiffMap.coe_sub, Pi.sub_apply, hΦs0 m x hx, hΦs0 n x hx, sub_zero]
          · rw [ContMDiffMap.coe_sub, Pi.sub_apply, IsSubApply.sub_apply, hΦsϑ m y hy,
              hΦsϑ n y hy]
      _ ≤ A * (ε / (A + 1)) := by gcongr; exact (hN m hm n hn).le
      _ = ε * (A / (A + 1)) := by ring
      _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (by linarith))
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- Their values converge to `g` in `L²(M)`, since `‖Φ - g‖_{L²} ≤ C ‖ϑ - v‖_{W^{1,2}}`.
  have hQS := image_symm_subset_source_inter_preimage L p hSB fun y hy ↦ hrt y (hBr hy)
  have hconv : Tendsto (fun n ↦ toLp (ofSmooth (Φs n))) atTop (𝓝 (hg.toLp g)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ norm_toLp_ofSmooth_sub_le L p hC hE2
      (Φs n) hg (fun x hx ↦ ⟨hΦs0 n x fun h ↦ hx (hQS h), hg0 x hx⟩) (ϑ n) v ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_ball, hgv] with y hy hgy
      rw [hΦsϑ n y (hBr hy), hgy]
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hϑ).const_mul C.toReal
  refine ⟨w, ?_⟩
  rw [tendsto_nhds_unique ((toLp.continuous.tendsto w).comp hw) hconv]
  exact hg.coeFn_toLp

/-- **Localizations of a function which is `W^{1,2}` in a chart lie in `H¹(M)`.** If the reading
of `f ∈ L²(M)` in the chart `L ∘ extChartAt I p` agrees on an open set `Ω` of coordinates around
the image of `p` with an element of `W^{1,2}(Ω)`, then there is an open neighbourhood `N` of `p`
such that `χ f` is the value of an element of `H¹(M)` for every smooth `χ` supported in `N`. -/
private theorem exists_isOpen_forall_exists_toLp_ae_eq_mul (L : E ≃L[ℝ] F)
    (f : Lp ℝ 2 (riemannianVolume I M)) {p : M} {Ω : Opens F} (hpΩ : L (extChartAt I p p) ∈ Ω)
    (U : W1p volume Ω 2)
    (hU : W1p.value U =ᵐ[volume.restrict (Ω : Set F)]
      fun y ↦ f ((extChartAt I p).symm (L.symm y))) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ ∀ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ → tsupport χ ⊆ N →
      ∃ w : SobolevH1 I M, toLp w =ᵐ[riemannianVolume I M] fun x ↦ χ x * f x := by
  set φ := extChartAt I p
  set y₀ := L (φ p)
  -- A coordinate ball of radius `r` inside `Ω` on which the inverse chart is defined and
  -- gradients are controlled by coordinate derivatives.
  obtain ⟨C₂, hC₂, r, hr, hrΩ, hrt, hgrad⟩ :=
    exists_ball_subset_and_norm_mgradient_le (I := I) L p (Ω.isOpen.mem_nhds hpΩ)
  refine ⟨φ.source ∩ φ ⁻¹' (L.symm '' ball y₀ (r / 4)),
    isOpen_extChartAt_preimage' p (L.symm.toHomeomorph.isOpenMap _ isOpen_ball),
    ⟨mem_extChartAt_source p, y₀, mem_ball_self (by positivity), by simp [y₀]⟩,
    fun χ hχ hχN ↦ ?_⟩
  -- The cutoff `χ` read in the chart, as a compactly supported smooth function on `F`.
  obtain ⟨χF, hχFs, hχFc, htsχF, hχF_eq⟩ := exists_contDiff_eq_comp L p hr hrt hχ hχN
  have hχFΩ : tsupport χF ⊆ Ω := fun y hy ↦
    hrΩ (closedBall_subset_ball (by linarith) (htsχF hy))
  -- `χ f` read in the chart is an element `v` of `W^{1,2}(F)` supported in `tsupport χF`.
  obtain ⟨v, hv, -⟩ := W1p.exists_top_value_gradient_ae_eq_mul_sub_const (mu := volume)
    (p := 2) ENNReal.ofNat_ne_top U hχFs hχFc hχFΩ 0
  simp only [sub_zero] at hv
  have hvK : ∀ᵐ y ∂volume, y ∉ tsupport χF → W1p.value v y = 0 := by
    filter_upwards [hv] with y hy hyK
    rw [hy, image_eq_zero_of_notMem_tsupport hyK, zero_mul]
  -- Test functions `ϑ n`, supported in a fixed compact set `S`, converging to `v`.
  obtain ⟨S, hSc, hSB, ϑ, hϑS, hϑ⟩ := W1p.exists_isCompact_tendsto_ofTestFunctionₗ
    ENNReal.ofNat_ne_top v hχFc.isCompact (isOpen_ball (x := y₀) (ε := 3 * r / 4))
    (htsχF.trans (closedBall_subset_ball (by linarith))) hvK
  -- `χ f` is the limit in `H¹(M)` of the transplanted test functions.
  have hBΩ : ball y₀ (3 * r / 4) ⊆ Ω := (ball_subset_ball (by linarith)).trans hrΩ
  have hNS : φ.source ∩ φ ⁻¹' (L.symm '' ball y₀ (r / 4)) ⊆
      φ.source ∩ φ ⁻¹' (L.symm '' ball y₀ (3 * r / 4)) :=
    inter_subset_inter_right _ (preimage_mono (image_mono (ball_subset_ball (by linarith))))
  refine exists_toLp_ae_eq_of_tendsto_ofTestFunctionₗ L p hr hC₂ hrt hgrad hSc hSB hϑS hϑ
    ((hχ.continuous.memLp_top_of_hasCompactSupport (.of_compactSpace χ) _).fun_mul
      (Lp.memLp f))
    (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hNS (hχN h))]) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae_restrict_of_subset hBΩ hU,
    ae_restrict_of_ae hv] with y hy hUy hvy
  rw [hvy, hUy, hχF_eq y (ball_subset_ball (by linarith) hy)]

/-- **Functions that are `W^{1,2}` in charts lie in `H¹(M)`.** Let `M` be a closed smooth manifold
with a continuous Riemannian metric and `L` a continuous linear equivalence from the model space to
a finite-dimensional inner product space `F` with a Haar measure. If near every point `p` the
reading of `f ∈ L²(M)` in the chart `L ∘ extChartAt I p` agrees almost everywhere, on an open set
`Ω` of coordinates around the image of `p`, with an element of `W^{1,2}(Ω)`, then `f` is the value
of an element of `H¹(M)`. -/
theorem exists_toLp_eq_of_forall_exists_w1p (L : E ≃L[ℝ] F) (f : Lp ℝ 2 (riemannianVolume I M))
    (hf : ∀ p : M, ∃ Ω : Opens F, L (extChartAt I p p) ∈ Ω ∧ ∃ U : W1p volume Ω 2,
      W1p.value U =ᵐ[volume.restrict (Ω : Set F)]
        fun y ↦ f ((extChartAt I p).symm (L.symm y))) :
    ∃ w : SobolevH1 I M, toLp w = f := by
  have hloc (p : M) : ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ ∀ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ →
      tsupport χ ⊆ N → ∃ w : SobolevH1 I M, toLp w =ᵐ[riemannianVolume I M] fun x ↦ χ x * f x := by
    obtain ⟨Ω, hpΩ, U, hU⟩ := hf p
    exact exists_isOpen_forall_exists_toLp_ae_eq_mul (I := I) L f hpΩ U hU
  choose N hNo hpN hN using hloc
  -- A smooth partition of unity subordinate to the neighbourhoods `N p`.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ N hNo
    fun x _ ↦ mem_iUnion.2 ⟨x, hpN x⟩
  choose w hw using fun i ↦ hN i (ρ i) (ρ i).contMDiff (hρ i)
  -- Only finitely many of its functions are nonzero, since `M` is compact.
  set s := (ρ.locallyFinite.finite_nonempty_inter_compact isCompact_univ).toFinset
  have hsum (x : M) : ∑ i ∈ s, ρ i x = 1 := by
    rw [← ρ.sum_eq_one (mem_univ x)]
    refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).symm
    simp only [s, Set.Finite.coe_toFinset, mem_ofPred_eq, inter_univ]
    exact ⟨x, hi⟩
  refine ⟨∑ i ∈ s, w i, Lp.ext ?_⟩
  rw [map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum s fun i ↦ toLp (w i),
    (eventually_all_finset s).2 fun i _ ↦ hw i] with x hx hwx
  rw [hx, Finset.sum_congr rfl hwx, ← Finset.sum_mul, hsum, one_mul]

/-- **`H¹(M)` is the space of functions that are `W^{1,2}` in charts.** Let `M` be a closed smooth
manifold with a continuous Riemannian metric and `L` a continuous linear equivalence from the model
space to a finite-dimensional inner product space `F` with a Haar measure. A function `f ∈ L²(M)`
is the value of an element of the completion `H¹(M)` of the smooth functions exactly when, near
every point `p`, its reading in the chart `L ∘ extChartAt I p` agrees almost everywhere, on an open
set `Ω` of coordinates around the image of `p`, with an element of `W^{1,2}(Ω)`. -/
theorem exists_toLp_eq_iff_forall_exists_w1p (L : E ≃L[ℝ] F)
    (f : Lp ℝ 2 (riemannianVolume I M)) :
    (∃ w : SobolevH1 I M, toLp w = f) ↔ ∀ p : M, ∃ Ω : Opens F, L (extChartAt I p p) ∈ Ω ∧
      ∃ U : W1p volume Ω 2, W1p.value U =ᵐ[volume.restrict (Ω : Set F)]
        fun y ↦ f ((extChartAt I p).symm (L.symm y)) := by
  refine ⟨?_, exists_toLp_eq_of_forall_exists_w1p L f⟩
  rintro ⟨w, rfl⟩ p
  obtain ⟨Ω, hpΩ, -, T, -, hT⟩ := exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p L
  exact ⟨Ω, hpΩ, T w, hT w⟩

end TauCeti.Manifold.SobolevH1
