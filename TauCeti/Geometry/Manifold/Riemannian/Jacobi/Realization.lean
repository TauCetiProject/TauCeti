/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InitialData

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

The initial-state construction uses `TangentSpace.exists_smooth_initialData`. We then use
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
    TangentSpace.exists_smooth_initialData (v := v)
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
