/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Family
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import Mathlib.Topology.Instances.Matrix
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of scalar Schrödinger forms under changes of metric

The scalar form `∫ (|∇φ|² + P φ²) dV_g` uses the native gradient and volume on the copy
`WithMetric g`. For a common compactly supported test, this form depends continuously on
jointly continuous families of metrics and potentials. The gradient term in local coordinates
is the contraction of the differential with the inverse Gram matrix. The volume can be
compared with that of a fixed reference metric by the actual relative volume density.
-/

public noncomputable section

open Bundle Filter Manifold MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {A : Type*} [TopologicalSpace A]

private theorem continuous_relativeVolumeDensity_family
    (r : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g : A → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hg : Continuous (fun p : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2))) :
    Continuous (fun p : A × M ↦ r.relativeVolumeDensity (g p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let U := (trivializationAt E (TangentSpace I) p.2).baseSet
  have hp : p ∈ (univ : Set A) ×ˢ U := ⟨mem_univ _,
    mem_baseSet_trivializationAt E (TangentSpace I) p.2⟩
  let G (q : A × M) := chartGramMatrix (I := I)
    (WithMetric.toWithMetric (g q.1) p.2) (WithMetric.toWithMetric (g q.1) q.2)
  let R (q : A × M) := chartGramMatrix (I := I)
    (WithMetric.toWithMetric r p.2) (WithMetric.toWithMetric r q.2)
  have hGram {k : A → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
      (hk : Continuous (fun q : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        q.2 ((k q.1).inner q.2))) :
      ContinuousOn (fun q : A × M ↦ chartGramMatrix (I := I)
        (WithMetric.toWithMetric (k q.1) p.2) (WithMetric.toWithMetric (k q.1) q.2))
        (univ ×ˢ U) := by
    refine continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ ?_
    refine (continuousOn_chartGramMatrix_family
      (fun a ↦ (k a).toContinuousRiemannianMetric) (S := univ ×ˢ U) hk.continuousOn p.2
      (fun _ hq ↦ hq.2) i j).congr fun q _ ↦ ?_
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(k q.1).toRiemannianMetric⟩
    change chartGramMatrix (I := I) (WithMetric.toWithMetric (k q.1) p.2)
      (WithMetric.toWithMetric (k q.1) q.2) i j = chartGramMatrix (I := I) p.2 q.2 i j
    rw [ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric, Matrix.of_apply,
      chartGramMatrix_apply]
    rfl
  have hG : ContinuousOn G (univ ×ˢ U) := hGram hg
  have hR : ContinuousOn R (univ ×ˢ U) := hGram (k := fun _ ↦ r)
    (r.contMDiff.continuous.comp continuous_snd)
  have hopen : IsOpen ((univ : Set A) ×ˢ U) :=
    isOpen_univ.prod (trivializationAt E (TangentSpace I) p.2).open_baseSet
  have hRne (q : A × M) (hq : q ∈ (univ : Set A) ×ˢ U) : (R q).det ≠ 0 :=
    (chartGramMatrix_det_pos _ (by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (WithMetric.mem_chartAt_source_iff _ _).2 (by
        simpa only [U, TangentBundle.trivializationAt_baseSet] using hq.2))).ne'
  have hratio := ((continuous_id.matrix_det.comp_continuousOn hG).div
    (continuous_id.matrix_det.comp_continuousOn hR) hRne).sqrt
  refine (hratio.congr (fun q hq ↦ ?_)).continuousAt (hopen.mem_nhds hp)
  exact r.relativeVolumeDensity_eq_sqrt_div_chartGramMatrix (g q.1) (by
    simpa only [U, TangentBundle.trivializationAt_baseSet] using hq.2)

private theorem norm_sq_mgradient_comp_ofWithMetric
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (φ : M → ℝ) (x : WithMetric g) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ‖mgradient I (φ ∘ WithMetric.ofWithMetric) x‖ ^ 2 =
      ‖mgradient I φ x.ofWithMetric‖ ^ 2 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let D := mfderiv I I (WithMetric.ofWithMetric : WithMetric g → M) x
  let v := mgradient I (φ ∘ WithMetric.ofWithMetric) x
  have hv : D v = mgradient I φ x.ofWithMetric := by
    apply eq_mgradient_iff.mpr
    intro w
    let u := mfderiv I I (WithMetric.toWithMetric g) x.ofWithMetric w
    have hu : D u = w := WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric x.ofWithMetric w
    have h := inner_mgradient (f := φ ∘ WithMetric.ofWithMetric) (x := x) u
    rw [WithMetric.inner_def, WithMetric.mvfderiv_comp_ofWithMetric_apply] at h
    change g.inner x.ofWithMetric (D v) (D u) = mvfderiv I φ x.ofWithMetric (D u) at h
    rw [hu] at h
    exact h
  change ‖v‖ ^ 2 = ‖mgradient I φ x.ofWithMetric‖ ^ 2
  rw [← real_inner_self_eq_norm_sq, WithMetric.inner_def, ← hv, ← real_inner_self_eq_norm_sq]
  rfl

section Scalar

variable [LindelofSpace M]

/-- The quadratic form of `-Δ_g + P`. The potential and the test are functions on the underlying
manifold. -/
@[expose] def scalarSchrodingerQuadraticForm
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P φ : M → ℝ) : ℝ :=
  ∫ x : WithMetric g, (‖mgradient I (φ ∘ WithMetric.ofWithMetric) x‖ ^ 2 +
    P x.ofWithMetric * φ x.ofWithMetric ^ 2) ∂riemannianVolume I (WithMetric g)

/-- The native scalar quadratic form on a compactly supported `C¹` test is continuous under
jointly continuous changes of the metric tensor and the potential. The volume of `r` serves as
a fixed reference measure, and each varying volume has its actual relative density. -/
theorem continuous_scalarSchrodingerQuadraticForm
    (r : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g : A → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hg : Continuous (fun p : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2)))
    {P : A → M → ℝ} (hP : Continuous (fun p : A × M ↦ P p.1 p.2))
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hc : HasCompactSupport φ) :
    Continuous (fun a ↦ scalarSchrodingerQuadraticForm (g a) (P a) φ) := by
  let D (p : A × M) :=
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
    ‖mgradient I φ p.2‖ ^ 2
  let S (p : A × M) := r.relativeVolumeDensity (g p.1) p.2 * (D p + P p.1 p.2 * φ p.2 ^ 2)
  have hD : Continuous D := by
    rw [← continuousOn_univ, ← univ_prod_univ]
    exact continuousOn_norm_sq_mgradient_family (fun a ↦ (g a).toContinuousRiemannianMetric)
      hg.continuousOn isOpen_univ hφ.contMDiffOn
  have hS : Continuous S := (continuous_relativeVolumeDensity_family r g hg).mul
    (hD.add (hP.mul ((hφ.continuous.comp continuous_snd).pow 2)))
  let K := (WithMetric.ofWithMetric : WithMetric r → M) ⁻¹' tsupport φ
  have hK : IsCompact K := by
    simpa only [K, ← WithMetric.coe_homeomorph] using
      (WithMetric.homeomorph r).isCompact_preimage.mpr hc
  have hzero (a : A) (x : WithMetric r) (hx : x ∉ K) : S (a, x.ofWithMetric) = 0 := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g a).toRiemannianMetric⟩
    have hφx : φ x.ofWithMetric = 0 := image_eq_zero_of_notMem_tsupport hx
    have hd : mgradient I φ x.ofWithMetric = 0 := mgradient_eq_zero_iff.mpr
      ((notMem_tsupport_iff_eventuallyEq.mp hx).mvfderiv_eq.trans mvfderiv_zero)
    change r.relativeVolumeDensity (g a) x.ofWithMetric *
      (‖mgradient I φ x.ofWithMetric‖ ^ 2 + P a x.ofWithMetric * φ x.ofWithMetric ^ 2) = 0
    simp [hd, hφx]
  convert continuous_integral_of_compact_support
    (F := fun a (x : WithMetric r) ↦ S (a, x.ofWithMetric)) (riemannianVolume I (WithMetric r))
    hK (hS.comp (continuous_fst.prodMk (WithMetric.continuous_ofWithMetric.comp continuous_snd)))
    (fun a x ↦ not_imp_comm.mp (hzero a x)) using 1
  funext a
  unfold scalarSchrodingerQuadraticForm
  simp_rw [norm_sq_mgradient_comp_ofWithMetric]
  simpa only [S, D, Function.comp_apply, smul_eq_mul] using
    r.integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul (g a)
      (fun x ↦ D (a, x) + P a x * φ x ^ 2)

end Scalar

section ChartTopology

open ContMDiffRiemannianMetric

variable [I.Boundaryless]

local notation "Metrics" => ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

private theorem continuous_metricTensor_chartC0 :
    letI := chartCkTopology (I := I) (M := M) 0
    Continuous (fun p : Metrics × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      p.2 (p.1.inner p.2)) := by
  let _ := chartCkTopology (I := I) (M := M) 0
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have := FiniteDimensional.proper ℝ E
  refine continuous_iff_continuousAt.mpr fun p ↦
    (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr ⟨continuous_snd.continuousAt, ?_⟩
  have h := continuousAt_iteratedFDeriv_chartMetric (I := I) (k := 0) p.2
    (m := 0) le_rfl p.1 (mem_extChartAt_target p.2)
  have hchart : ContinuousAt (fun q : Metrics × E ↦
      q.1.toNondegenerateMetric.chartMetric p.2 q.2) (p.1, extChartAt I p.2 p.2) := by
    have heval : Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E)
        (E →L[ℝ] E →L[ℝ] ℝ) ↦ L 0) :=
      continuous_eval_const (0 : Fin 0 → E)
    simpa only [iteratedFDeriv_zero_apply] using heval.continuousAt.comp' h
  have hp := continuous_fst.continuousAt (x := p) |>.prodMk
    ((continuousAt_extChartAt (I := I) p.2).comp continuous_snd.continuousAt)
  have hlocal : ContinuousAt (fun q : Metrics × M ↦
      q.1.toNondegenerateMetric.chartMetric p.2 (extChartAt I p.2 q.2)) p :=
    hchart.comp' (f := fun q : Metrics × M ↦ (q.1, extChartAt I p.2 q.2)) hp
  refine hlocal.congr ?_
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := I) p.2)] with q hq
  rw [ContMDiffNondegenerateMetric.chartMetric_def, (extChartAt I p.2).left_inv hq,
    ContMDiffNondegenerateMetric.inCoordinates_eq_tangentBilinFormInCoordinates,
    tangentBilinFormInCoordinates_def]
  congr 1
  ext v w
  exact toNondegenerateMetric_apply _ _ _ _

variable [LindelofSpace M]

/-- Compact convergence of the metric coefficients and potentials implies convergence of the
native scalar Schrödinger forms on every compactly supported `C¹` test. -/
theorem tendsto_scalarSchrodingerQuadraticForm
    {ι : Type*} {l : Filter ι} {g : ι → Metrics} {g₀ : Metrics}
    {P : ι → C(M, ℝ)} {P₀ : C(M, ℝ)}
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hc : HasCompactSupport φ) :
    letI := chartCkTopology (I := I) (M := M) 0
    Tendsto g l (𝓝 g₀) → Tendsto P l (𝓝 P₀) →
      Tendsto (fun i ↦ scalarSchrodingerQuadraticForm (g i) (P i) φ) l
        (𝓝 (scalarSchrodingerQuadraticForm g₀ P₀ φ)) := by
  let _ := chartCkTopology (I := I) (M := M) 0
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  intro hg hP
  have hPot : Continuous (fun q : (Metrics × C(M, ℝ)) × M ↦ q.1.2 q.2) :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous (fun q : Metrics × C(M, ℝ) ↦
      scalarSchrodingerQuadraticForm q.1 q.2 φ) :=
    continuous_scalarSchrodingerQuadraticForm g₀ Prod.fst
      (continuous_metricTensor_chartC0.comp ((continuous_fst.comp continuous_fst).prodMk
        continuous_snd)) hPot hφ hc
  exact hcont.continuousAt.tendsto.comp (hg.prodMk_nhds hP)

end ChartTopology

end TauCeti.Manifold
