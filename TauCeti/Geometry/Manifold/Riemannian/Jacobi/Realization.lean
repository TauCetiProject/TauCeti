/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Realizing Jacobi fields by geodesic variations

Every Jacobi field along a maximal geodesic, on a preconnected parameter set containing
zero, is the variation field of a family obtained by varying the initial position and
velocity. Around each compact subset of the parameter set, this family is jointly smooth
on one product of open sets and all its curves are geodesics on the same time domain.
No completeness is required: the common domain comes from openness of the actual geodesic
flow domain and compactness of the chosen time set.

The variation realizes the given field and therefore its covariant velocity. Endpoint
values are prescribed only to first order by the field; the nearby geodesics need not
have fixed endpoints.

The initial-state construction uses smooth section extensions and the short geodesic flow.
It follows `CovariantDerivative.exists_contMDiffAt_tangentCurve_initialData`, strengthening
its pointwise smoothness to smoothness throughout a fixed neighbourhood. We then use
the geodesic-flow variation and its initial-value formulas in `Jacobi.Flow`, and
`IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (realization of Jacobi fields by variations through geodesics).
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p} {s : Set ℝ}
  {J : ∀ t, TangentSpace I (maximalGeodesic I M p v t)}

/-- Use a short geodesic and globally smooth extensions to obtain initial states smooth
on one fixed neighbourhood, with prescribed position and covariant velocities. -/
private theorem exists_smooth_initialData (u w : TangentSpace I p) :
    ∃ σ : ℝ → TangentBundle I M,
      σ 0 = TotalSpace.mk' E p v ∧
      (∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ σ q) ∧
      curveVelocity I (fun q ↦ (σ q).proj) 0 = u ∧
      alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj)
        (fun q ↦ (σ q).2) 0 = w := by
  let γ := maximalGeodesic I M p u
  let S := geodesicInterval I M p u
  have hS : S ∈ 𝓝 0 := isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ S :=
    (contMDiffOn_maximalGeodesic (I := I) (M := M)).comp
      ((contMDiff_const (c := TotalSpace.mk' E p u)).prodMk contMDiff_id).contMDiffOn
      (fun _ ht ↦ ht)
  have hγ0 : γ 0 = p := maximalGeodesic_zero p u
  have hγvel : curveVelocity I γ 0 = u := by
    rw [← curveVelocityWithin_of_mem_nhds hS]
    exact eq_of_heq (isGeodesicCurveOnFrom_maximalGeodesic p u).velocity_heq
  -- Keep the correction in the fibre over γ 0 until the final initial-state equality.
  let v₀ : TangentSpace I (γ 0) := v
  let w₀ : TangentSpace I (γ 0) := w
  obtain ⟨A, hA, hAv⟩ := exists_contMDiff_section_eq I E ∞ v₀
  obtain ⟨B, hB, hBw⟩ := exists_contMDiff_section_eq I E ∞
    (w₀ - leviCivitaConnection I M A (γ 0) (curveVelocity I γ 0))
  let V : ∀ q, TangentSpace I (γ q) := fun q ↦ A (γ q) + q • B (γ q)
  have hAp : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (A (γ q))) S := hA.comp_contMDiffOn hγ
  have hBp : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (B (γ q))) S := hB.comp_contMDiffOn hγ
  have hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (V q)) S := fun q hq ↦
    (hAp q hq).add_sectionAlong
      ((contMDiff_id q).contMDiffWithinAt.smul_totalSpace (hBp q hq))
  refine ⟨fun q ↦ TotalSpace.mk' E (γ q) (V q), ?_, ?_, hγvel, ?_⟩
  · apply TotalSpace.ext hγ0
    simp only [V, zero_smul, add_zero]
    exact heq_of_eq hAv
  · filter_upwards [hS] with q hq
    exact hV.contMDiffAt (isOpen_geodesicInterval.mem_nhds hq)
  · have hcoordA := differentiableWithinAt_sectionCoord (s := Set.univ) γ (fun q ↦ A (γ q))
      ((hAp.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0))
    have hcoordB := differentiableWithinAt_sectionCoord (s := Set.univ) γ (fun q ↦ B (γ q))
      ((hBp.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0))
    -- The initial-state curve was constructed as the pair (γ, V); expose its two projections.
    change alongCurve (leviCivitaConnection I M) γ V 0 = w₀
    dsimp only [V]
    rw [← alongCurveWithin_univ, alongCurveWithin_add _ _ _ _ Set.univ hcoordA
      (by rw [sectionCoord_smul]; exact differentiableWithinAt_id.fun_smul hcoordB),
      alongCurveWithin_smul _ _ _ (fun q : ℝ ↦ q) Set.univ
        differentiableWithinAt_id hcoordB,
      alongCurveWithin_pullback_curveVelocityWithin _ _ _ uniqueDiffWithinAt_univ
        ((hγ.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
        (hA.mdifferentiableAt (by simp))]
    simp [derivWithin_id', hBw, curveVelocityWithin_univ]


/-- Choose varying initial states whose geodesic variation realizes the prescribed field. -/
private theorem IsJacobiFieldOn.exists_initialData_variation
    (hJ : IsJacobiFieldOn I (maximalGeodesic I M p v) J s)
    (hs : IsPreconnected s) (h0 : 0 ∈ s)
    (hsub : s ⊆ geodesicInterval I M p v) :
    ∃ σ : ℝ → TangentBundle I M,
      σ 0 = TotalSpace.mk' E p v ∧
      (∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ σ q) ∧
      ∀ t ∈ s, variationField I
        (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2) t = J t := by
  obtain ⟨σ, hσ0, hσ, hpos, hvel⟩ :=
    exists_smooth_initialData (v := v)
      (J 0) (alongCurveWithin (leviCivitaConnection I M)
        (maximalGeodesic I M p v) J s 0)
  have hF := isJacobiFieldOn_variationField_maximalGeodesic (hσ.self_of_nhds.of_le (by simp))
  have hF0 := variationField_maximalGeodesic_zero (I := I) (σ := σ)
  have hDF0 := alongCurveWithin_variationField_maximalGeodesic_zero
    (hσ.self_of_nhds.of_le (by simp))
  have hbase : maximalGeodesic I M (σ 0).proj (σ 0).2 = maximalGeodesic I M p v := by
    exact congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.2) hσ0
  have hinterval : geodesicInterval I M (σ 0).proj (σ 0).2 =
      geodesicInterval I M p v :=
    congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.2) hσ0
  rw [hbase, hinterval] at hF hDF0
  have hFs := hF.mono hJ.uniqueDiffOn hsub
  refine ⟨σ, hσ0, hσ, fun t ht ↦ ?_⟩
  exact hFs.eq_of_eq_of_alongCurveWithin_eq hJ hs h0 (hF0.trans hpos)
    (by rw [hF.alongCurveWithin_subset (hJ.uniqueDiffOn 0 h0) hsub h0, hDF0, hvel]) ht

/-- A Jacobi field along a maximal geodesic is realized by a smooth geodesic variation
on a common open time domain around every prescribed compact subset. The central curve
and variation field agree with the original ones throughout `s`, not only on the compact
subset. The nearby curves are not asserted to have fixed endpoints. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_of_isCompact
    (hJ : IsJacobiFieldOn I (maximalGeodesic I M p v) J s)
    (hs : IsPreconnected s) (h0 : 0 ∈ s)
    (hsub : s ⊆ geodesicInterval I M p v)
    {K : Set ℝ} (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ (F : ℝ → ℝ → M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ K ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F q) V) ∧
      F 0 = maximalGeodesic I M p v ∧
      (∀ t ∈ s, variationField I F t = J t) := by
  obtain ⟨σ, hσ0, hσ, hfield⟩ := hJ.exists_initialData_variation hs h0 hsub
  have hdom : K ⊆ geodesicInterval I M (σ 0).proj (σ 0).2 := by
    rw [congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.2) hσ0]
    exact hKs.trans hsub
  obtain ⟨U, V, hU, hV, h0U, hKV, hF, hgeod⟩ :=
    exists_contMDiffOn_maximalGeodesic_comp_of_isCompact (n := ⊤) hσ hK hdom
  exact ⟨fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2,
    U, V, hU, hV, h0U, hKV, hF, hgeod,
    congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.2) hσ0, hfield⟩

end TauCeti.Manifold
