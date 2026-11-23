/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables

/-!
# Riemannian volume on normal domains via Euclidean coordinates

Through any linear isometry `A : F ≃ₗᵢ[ℝ] TangentSpace I p` from a finite-dimensional real inner
product Borel space `F`, the Riemannian exponential map on a normal domain `U ⊆ T_p M` pushes
Lebesgue measure on `A ⁻¹' U` weighted by the geometric Jacobian
`LinearMap.normDet (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap`
forward to the Riemannian volume on the normal neighbourhood `exp_p '' U`.

Consequently, integrating any `ℝ≥0∞`-valued function over `exp_p '' (A '' s)` for a
measurable subset `s ⊆ A ⁻¹' U` reduces to a Euclidean integral over `s` weighted by
`normDet (d(exp_p)_{A x})`. Specializing to the constant integrand `1` gives the Riemannian volume
of `exp_p '' (A '' s)`, and on a boundaryless Riemannian metric manifold Gauss's lemma identifies
the exponential image of `Metric.ball 0 r ⊆ U` with `Metric.ball p r`, expressing the volume of a
normal geodesic ball as a Euclidean ball integral.

## Main results

* `TauCeti.Manifold.IsNormalDomain.map_withDensity_normDet`: pushforward of Jacobian-weighted
  Lebesgue measure on `A ⁻¹' U` along `exp_p ∘ A` equals the Riemannian volume on `exp_p '' U`.
* `TauCeti.Manifold.IsNormalDomain.setLIntegral_riemannianVolume_image_eq_setLIntegral_normDet`:
  change of variables for Lebesgue integrals of arbitrary nonnegative functions over measurable
  subsets of a normal domain.
* `TauCeti.Manifold.IsNormalDomain.riemannianVolume_image_eq_setLIntegral_normDet`: Riemannian
  volume of the exponential image of a measurable subset of a normal domain.
* `TauCeti.Manifold.IsNormalDomain.riemannianVolume_ball_eq_setLIntegral_normDet`: Riemannian
  volume of a normal geodesic ball `Metric.ball p r` as a Euclidean ball integral of
  `normDet (d exp_p)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 2, 5, and 6.
-/

public section

open Bundle MeasureTheory Metric Set
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.Manifold.IsNormalDomain

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/-- Local helper packaging the `C¹` partial diffeomorphism `exp_p ∘ A` on `A ⁻¹' U` together with
the identity expressing its Riemannian Jacobian in `stdOrthonormalBasis ℝ F` as
`normDet (d(exp_p)_{A x})`. -/
private theorem exists_partialDiffeomorph_riemannianExp_comp_isometry
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1,
      Φ.source = A ⁻¹' U ∧ Φ.target = riemannianExp I M p '' U ∧
      ⇑Φ = riemannianExp I M p ∘ A ∧
      ∀ x ∈ A ⁻¹' U,
        TauCeti.riemannianJacobian (I := I) (stdOrthonormalBasis ℝ F).toBasis
            (riemannianExp I M p ∘ A) x =
          LinearMap.normDet (U := TangentSpace I p)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap := by
  let b := stdOrthonormalBasis ℝ F
  have hopen : IsOpen (A ⁻¹' U) := h.isOpen.preimage A.continuous
  obtain ⟨Φ, hsource, hcoe⟩ :=
    h.exists_partialDiffeomorph_riemannianExp_comp A.toContinuousLinearEquiv hopen
      (mapsTo_preimage A U)
  have hcoeA : (riemannianExp I M p ∘ A.toContinuousLinearEquiv) = riemannianExp I M p ∘ A := by
    ext x
    simp [A.coe_toContinuousLinearEquiv]
  have htarget : Φ.target = riemannianExp I M p '' U := by
    rw [← Φ.toPartialEquiv.image_source_eq_target, hsource, hcoe, hcoeA, image_comp,
      image_preimage_eq U A.surjective]
  refine ⟨Φ.ofLE (m := 1) (by simp), ?_, ?_, ?_, fun x hx ↦ ?_⟩
  · simpa only [PartialDiffeomorph.ofLE_toPartialEquiv] using hsource
  · simpa only [PartialDiffeomorph.ofLE_toPartialEquiv] using htarget
  · simpa only [PartialDiffeomorph.ofLE_toPartialEquiv, hcoeA] using hcoe
  · have hf : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
        (A.toContinuousLinearEquiv x) := by
      simpa only [A.coe_toContinuousLinearEquiv] using
        (h.isLocalDiffeomorphOn ⟨A x, hx⟩).contMDiffAt.mdifferentiableAt (by simp)
    have hmap_basis : b.toBasis.map A.toContinuousLinearEquiv.toLinearEquiv = (b.map A).toBasis :=
      (b.toBasis_map A).symm
    rw [← hcoeA,
      TauCeti.riemannianJacobian_comp_continuousLinearEquiv A.toContinuousLinearEquiv b.toBasis hf,
      hmap_basis, A.coe_toContinuousLinearEquiv]
    exact TauCeti.riemannianJacobian_eq_normDet (b.map A) _ (A x)

/-- **Normal-domain pushforward of Jacobian-weighted Lebesgue measure.** For any linear isometry
equivalence `A : F ≃ₗᵢ[ℝ] TangentSpace I p` and normal domain `U` at `p`, pushing Lebesgue measure
on `A ⁻¹' U` weighted by `normDet (d(exp_p)_{A x})` forward along `exp_p ∘ A` yields the
Riemannian volume restricted to `exp_p '' U`. -/
theorem map_withDensity_normDet
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) :
    Measure.map (riemannianExp I M p ∘ A)
        ((volume.restrict (A ⁻¹' U)).withDensity fun x ↦ ENNReal.ofReal
          (LinearMap.normDet (U := TangentSpace I p)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap)) =
      (riemannianVolume I M).restrict (riemannianExp I M p '' U) := by
  let b := stdOrthonormalBasis ℝ F
  have hopen : IsOpen (A ⁻¹' U) := h.isOpen.preimage A.continuous
  obtain ⟨Φ, hsource, htarget, hcoe, hJ⟩ :=
    exists_partialDiffeomorph_riemannianExp_comp_isometry h A
  have hmap := Φ.map_withDensity_riemannianJacobian one_ne_zero b.toBasis
  rw [hcoe, hsource, htarget, b.addHaar_eq_volume] at hmap
  refine Eq.trans ?_ hmap
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  exact congrArg ENNReal.ofReal (hJ x hx).symm

/-- **Change of variables on measurable subsets of a normal domain.** For any linear isometry
equivalence `A : F ≃ₗᵢ[ℝ] TangentSpace I p`, measurable set `s ⊆ F` mapped into a normal domain
`U`, and any function `φ : M → ℝ≥0∞`, integrating `φ` over `exp_p '' (A '' s)` against the
Riemannian volume equals integrating `(φ ∘ exp_p ∘ A)` weighted by `normDet (d(exp_p)_{A x})` over
`s` against Lebesgue measure. -/
theorem setLIntegral_riemannianVolume_image_eq_setLIntegral_normDet
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) {s : Set F} (hs : MeasurableSet s) (hmap : MapsTo A s U)
    (φ : M → ℝ≥0∞) :
    ∫⁻ y in riemannianExp I M p '' (A '' s), φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap) *
        φ (riemannianExp I M p (A x)) := by
  let T : Set M := riemannianExp I M p '' (A '' s)
  let ρ : F → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap)
  let b := stdOrthonormalBasis ℝ F
  have hopen : IsOpen (A ⁻¹' U) := h.isOpen.preimage A.continuous
  obtain ⟨Φ, hsource, htarget, hcoe, hJ⟩ :=
    exists_partialDiffeomorph_riemannianExp_comp_isometry h A
  have hTsub : T ⊆ riemannianExp I M p '' U := image_mono hmap.image_subset
  have hTeq : T = (riemannianExp I M p '' U) ∩ (A.symm ∘ riemannianLog I M p U) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨mem_image_of_mem _ (hmap hx), by
        simp [Function.comp_apply, h.riemannianLog_riemannianExp (hmap hx), hx]⟩
    · rintro ⟨hyU, hys⟩
      exact ⟨riemannianLog I M p U y, ⟨A.symm (riemannianLog I M p U y), hys, by simp⟩,
        riemannianExp_riemannianLog hyU⟩
  have hTmeas : MeasurableSet T := by
    rw [hTeq, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtypeVal h.isOpen_image.measurableSet).measurableSet_image.mpr
      ((A.symm.continuous.comp_continuousOn h.continuousOn_riemannianLog).domRestrict.measurable hs)
  have hcov := Φ.setLIntegral_riemannianVolume_eq one_ne_zero b.toBasis (T.indicator φ)
  rw [hcoe, hsource, htarget, b.addHaar_eq_volume] at hcov
  simp only [Function.comp_apply] at hcov
  have hind : ∀ x ∈ A ⁻¹' U,
      ENNReal.ofReal (TauCeti.riemannianJacobian (I := I) b.toBasis (riemannianExp I M p ∘ A) x) *
          T.indicator φ (riemannianExp I M p (A x)) =
        s.indicator (fun x ↦ ρ x * φ (riemannianExp I M p (A x))) x := by
    intro x hxU
    rw [hJ x hxU]
    by_cases hx : x ∈ s
    · have hmem : riemannianExp I M p (A x) ∈ T := mem_image_of_mem _ (mem_image_of_mem _ hx)
      simp [ρ, hx, hmem]
    · have hnmem : riemannianExp I M p (A x) ∉ T := by
        rintro ⟨_, ⟨x', hx', rfl⟩, heq⟩
        exact hx (A.injective (h.injOn (hmap hx') hxU heq) ▸ hx')
      simp [ρ, hx, hnmem]
  calc ∫⁻ y in T, φ y ∂riemannianVolume I M
      = ∫⁻ y in T, φ y ∂(riemannianVolume I M).restrict (riemannianExp I M p '' U) := by
        rw [Measure.restrict_restrict_of_subset hTsub]
    _ = ∫⁻ y in riemannianExp I M p '' U, T.indicator φ y ∂riemannianVolume I M :=
        (lintegral_indicator hTmeas _).symm
    _ = ∫⁻ x in A ⁻¹' U, ENNReal.ofReal
          (TauCeti.riemannianJacobian (I := I) b.toBasis (riemannianExp I M p ∘ A) x) *
          T.indicator φ (riemannianExp I M p (A x)) := hcov
    _ = ∫⁻ x in A ⁻¹' U, s.indicator (fun x ↦ ρ x * φ (riemannianExp I M p (A x))) x :=
        setLIntegral_congr_fun hopen.measurableSet hind
    _ = ∫⁻ x in s, ρ x * φ (riemannianExp I M p (A x)) ∂volume.restrict (A ⁻¹' U) :=
        lintegral_indicator hs _
    _ = ∫⁻ x in s, ρ x * φ (riemannianExp I M p (A x)) := by
        rw [Measure.restrict_restrict_of_subset hmap]

/-- **Volume of an exponential image inside a normal domain.** For any linear isometry equivalence
`A : F ≃ₗᵢ[ℝ] TangentSpace I p` mapping a measurable set `s ⊆ F` into a normal domain `U`, the
Riemannian volume of `exp_p '' (A '' s)` is the Lebesgue integral over `s` of the geometric
Jacobian `normDet (d(exp_p)_{A x})`. -/
theorem riemannianVolume_image_eq_setLIntegral_normDet
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) {s : Set F} (hs : MeasurableSet s) (hmap : MapsTo A s U) :
    riemannianVolume I M (riemannianExp I M p '' (A '' s)) =
      ∫⁻ x in s, ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap) := by
  simpa only [setLIntegral_one, mul_one] using
    h.setLIntegral_riemannianVolume_image_eq_setLIntegral_normDet A hs hmap
      (fun _ ↦ 1)

/-- **Volume of a normal geodesic ball.** When `Metric.ball 0 r` lies in a normal domain `U` at `p`
on a boundaryless Riemannian metric manifold, the Riemannian volume of `Metric.ball p r` is the
integral over `Metric.ball (0 : F) r` of `normDet (d(exp_p)_{A x})`. -/
theorem riemannianVolume_ball_eq_setLIntegral_normDet [I.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} {r : ℝ} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) (hU : Metric.ball 0 r ⊆ U) :
    riemannianVolume I M (Metric.ball p r) =
      ∫⁻ x in Metric.ball (0 : F) r, ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap) := by
  have him : A '' Metric.ball (0 : F) r = Metric.ball 0 r := by simp
  have hmap : MapsTo A (Metric.ball (0 : F) r) U := fun x hx ↦ hU (him ▸ mem_image_of_mem A hx)
  rw [← h.image_riemannianExp_ball_eq_ball hU, ← him]
  exact h.riemannianVolume_image_eq_setLIntegral_normDet A measurableSet_ball hmap

end TauCeti.Manifold.IsNormalDomain
