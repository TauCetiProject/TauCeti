/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Family
public import TauCeti.Geometry.Manifold.Riemannian.Schrodinger.Relative
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.DensityFamily
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of scalar Schrödinger forms under changes of metric

The scalar form `∫ (|∇φ|² + P φ²) dV_g` uses the native gradient and volume on the copy
`WithMetric g`. For a common compactly supported test, this form depends continuously on
jointly continuous families of metrics and potentials. The theorem
`tendsto_scalarSchrodingerForm` gives convergence under chart C⁰ convergence of metrics and
compact-open convergence of potentials. Consequently, nonnegativity of the form on a fixed
compactly supported `C¹` test passes to such limits.
-/

public noncomputable section

open Bundle Filter Manifold MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {A : Type*} [TopologicalSpace A]

namespace TauCeti.Manifold

open Bundle.ContMDiffRiemannianMetric

variable [LindelofSpace M]

/-- The native scalar form on a compactly supported `C¹` test is continuous under
jointly continuous changes of the metric tensor and the potential. -/
theorem continuous_scalarSchrodingerForm
    (g : A → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hg : Continuous (fun p : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2)))
    {P : A → M → ℝ} (hP : Continuous (fun p : A × M ↦ P p.1 p.2))
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hc : HasCompactSupport φ) :
    Continuous (fun a ↦ scalarSchrodingerForm (g a) (P a) φ) := by
  rw [continuous_iff_continuousAt]
  intro a₀
  let r := g a₀
  apply Continuous.continuousAt
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
    have hd : mgradient I φ x.ofWithMetric = 0 := mgradient_eq_zero_of_notMem_tsupport hx
    simp [S, D, hd, hφx]
  convert continuous_integral_of_compact_support
    (F := fun a (x : WithMetric r) ↦ S (a, x.ofWithMetric)) (riemannianVolume I (WithMetric r))
    hK (hS.comp (continuous_fst.prodMk (WithMetric.continuous_ofWithMetric.comp continuous_snd)))
    (fun a x ↦ not_imp_comm.mp (hzero a x)) using 1
  funext a
  simpa only [S, D] using
    scalarSchrodingerForm_eq_integral_relativeVolumeDensity r (g a) (P a)
      (hφ.mdifferentiable one_ne_zero)

section ChartTopology

open ContMDiffRiemannianMetric

variable [I.Boundaryless]

local notation "Metrics" => ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

/-- Compact convergence of the metric coefficients and potentials implies convergence of the
native scalar Schrödinger forms on every compactly supported `C¹` test. -/
theorem tendsto_scalarSchrodingerForm
    {ι : Type*} {l : Filter ι} {g : ι → Metrics} {g₀ : Metrics}
    {P : ι → C(M, ℝ)} {P₀ : C(M, ℝ)}
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hc : HasCompactSupport φ) :
    letI := chartCkTopology (I := I) (M := M) 0
    Tendsto g l (𝓝 g₀) → Tendsto P l (𝓝 P₀) →
      Tendsto (fun i ↦ scalarSchrodingerForm (g i) (P i) φ) l
        (𝓝 (scalarSchrodingerForm g₀ P₀ φ)) := by
  let _ := chartCkTopology (I := I) (M := M) 0
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  intro hg hP
  have hPot : Continuous (fun q : (Metrics × C(M, ℝ)) × M ↦ q.1.2 q.2) :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous (fun q : Metrics × C(M, ℝ) ↦
      scalarSchrodingerForm q.1 q.2 φ) :=
    continuous_scalarSchrodingerForm Prod.fst
      ((continuous_metricTensor_chartCk 0).comp ((continuous_fst.comp continuous_fst).prodMk
        continuous_snd)) hPot hφ hc
  exact hcont.continuousAt.tendsto.comp (hg.prodMk_nhds hP)

end ChartTopology

end TauCeti.Manifold
