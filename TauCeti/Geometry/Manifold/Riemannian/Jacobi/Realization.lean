/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InitialData
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Reparametrization
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness

/-!
# Realizing Jacobi fields by geodesic variations

Every Jacobi field along a geodesic on a preconnected parameter set is the variation field of a
smooth family of geodesics obtained by varying the initial position and velocity at a chosen base
parameter. Around each compact subset of the parameter set, this family is jointly smooth on a
product of open sets and all its curves are geodesics on a common open time domain. When the
parameter set itself is compact (for instance a closed interval `[a, b]`), a single smooth geodesic
variation covers the entire parameter set. No completeness is required: the common domain comes
from openness of the natural geodesic-flow domain and compactness of the chosen time set.

The variation realizes the given field and therefore its covariant velocity. Endpoint values are
prescribed only to first order by the field; the nearby geodesics need not have fixed endpoints.

The initial-state construction uses `TangentSpace.exists_smooth_initialData`. Along a maximal
geodesic containing zero, this directly feeds into the geodesic-flow variation in `Jacobi.Flow` and
initial-data uniqueness (`IsJacobiFieldOn.eq_of_eq_of_alongCurveWithin_eq`). Along an arbitrary
geodesic on a preconnected set, `IsGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected`
identifies the central curve on the parameter set with a time-translated maximal geodesic.

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.exists_geodesicVariation_maximalGeodesic_of_isCompact`:
  realization of a Jacobi field along `maximalGeodesic I M p v` around a compact subset, with
  `F 0 = maximalGeodesic I M p v` globally on `ℝ`.
* `TauCeti.Manifold.IsJacobiFieldOn.exists_geodesicVariation_of_isCompact`: realization of a Jacobi
  field along any geodesic on a preconnected parameter set around any compact subset.
* `TauCeti.Manifold.IsJacobiFieldOn.exists_geodesicVariation`: realization of a Jacobi field along
  any geodesic on a compact preconnected parameter set on an open neighbourhood of the whole set.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10,
  Theorem 10.4 (realization of Jacobi fields by variations through geodesics).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 5, Proposition 2.4.
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

section Maximal

variable {p : M} {v : TangentSpace I p} {s : Set ℝ}
  {J : ∀ t, TangentSpace I (maximalGeodesic I M p v t)}

/-- Choose varying initial states whose geodesic variation realizes the prescribed field along a
maximal geodesic. -/
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
  have hbase : maximalGeodesic I M (σ 0).proj (σ 0).2 = maximalGeodesic I M p v :=
    congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.2) hσ0
  have hinterval : geodesicInterval I M (σ 0).proj (σ 0).2 =
      geodesicInterval I M p v :=
    congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.2) hσ0
  rw [hbase, hinterval] at hF hDF0
  have hFs := hF.mono hJ.uniqueDiffOn hsub
  refine ⟨σ, hσ0, hσ, fun t ht ↦ ?_⟩
  exact hFs.eq_of_eq_of_alongCurveWithin_eq hJ hs h0 (hF0.trans hpos)
    (by rw [hF.alongCurveWithin_subset (hJ.uniqueDiffOn 0 h0) hsub h0, hDF0, hvel]) ht

/-- A Jacobi field along a maximal geodesic is realized by a smooth geodesic variation on a common
open time domain around every prescribed compact subset, with central curve equal globally on `ℝ`
to `maximalGeodesic I M p v`. The nearby curves are not asserted to have fixed endpoints. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_maximalGeodesic_of_isCompact
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

end Maximal

section General

/-- **Realization of Jacobi fields by geodesic variations.** Every Jacobi field along a geodesic on
a preconnected parameter set `s` is realized by a smooth geodesic variation on a common open time
domain `V` around any compact subset `K ⊆ s`. On all of `s`, the central curve `F 0` agrees with `γ`
and the tangent-bundle lift of `variationField I F` agrees with that of `J`. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_of_isCompact
    {γ : ℝ → M} {s : Set ℝ} {J : ∀ t, TangentSpace I (γ t)}
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s)
    {K : Set ℝ} (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ (F : ℝ → ℝ → M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ K ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F q) V) ∧
      EqOn (F 0) γ s ∧
      (∀ t ∈ s, TotalSpace.mk' E (F 0 t) (variationField I F t) =
        TotalSpace.mk' E (γ t) (J t)) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · refine ⟨fun _ ↦ γ, univ, ∅, isOpen_univ, isOpen_empty, mem_univ 0, hKs, ?_,
      fun _ _ ↦ hJ.isGeodesicCurveOn, eqOn_empty _ _, fun _ ht ↦ False.elim ht⟩
    rw [prod_empty]
    exact contMDiffOn_empty
  · let cov := leviCivitaConnection I M
    let p := γ a
    let v := curveVelocityWithin I γ s a
    let φ : ℝ → ℝ := fun t ↦ 1 * t + (-a)
    obtain ⟨σ, hσ0, hσ, hpos, hvel⟩ :=
      TangentSpace.exists_smooth_initialData (v := v) (J a) (alongCurveWithin cov γ J s a)
    let F₀ : ℝ → ℝ → M := fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2
    let F : ℝ → ℝ → M := fun q t ↦ F₀ q (φ t)
    have hbase : maximalGeodesic I M (σ 0).proj (σ 0).2 = maximalGeodesic I M p v :=
      congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.2) hσ0
    have hinterval : geodesicInterval I M (σ 0).proj (σ 0).2 = geodesicInterval I M p v :=
      congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.2) hσ0
    have hmaps : MapsTo φ s (geodesicInterval I M p v) := fun t ht ↦ by
      simpa only [φ, one_mul, ← sub_eq_add_neg] using
        hJ.isGeodesicCurveOn.sub_mem_geodesicInterval_of_isPreconnected hs ha ht
    have hK₀ : IsCompact (φ '' K) := hK.image (by fun_prop)
    have hdom : φ '' K ⊆ geodesicInterval I M (σ 0).proj (σ 0).2 := by
      rintro _ ⟨t, ht, rfl⟩
      rw [hinterval]
      exact hmaps (hKs ht)
    obtain ⟨U, V₀, hU, hV₀, h0U, hK₀V₀, hF₀, hgeod₀⟩ :=
      exists_contMDiffOn_maximalGeodesic_comp_of_isCompact (n := ⊤) hσ hK₀ hdom
    let V : Set ℝ := φ ⁻¹' V₀
    have hV : IsOpen V := hV₀.preimage (by fun_prop)
    have hKV : K ⊆ V := fun t ht ↦ hK₀V₀ (mem_image_of_mem φ ht)
    have hF_smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) :=
      hF₀.comp (contMDiff_iff_contDiff.mpr
        (by fun_prop : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ (z.1, φ z.2))).contMDiffOn
        fun _ hz ↦ ⟨hz.1, hz.2⟩
    have hF_geod : ∀ q ∈ U, IsGeodesicCurveOn I (F q) V := fun q hq ↦
      (hgeod₀ q hq).comp_affine 1 (-a) hV.uniqueDiffOn fun _ hr ↦ hr
    have hcurve_max : EqOn γ (maximalGeodesic I M p v ∘ φ) s := fun t ht ↦ by
      simpa only [Function.comp_apply, φ, one_mul, ← sub_eq_add_neg] using
        (hJ.isGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected hs ha ht).symm
    have hF0_eq : EqOn (F 0) γ s := fun t ht ↦
      (congrFun hbase (φ t)).trans (hcurve_max ht).symm
    -- Identify the pullback of `variationField I F₀` along `φ` with `J` by initial-data uniqueness.
    have hW₀ := isJacobiFieldOn_variationField_maximalGeodesic (hσ.self_of_nhds.of_le (by simp))
    have hW₀_0 := variationField_maximalGeodesic_zero (I := I) (σ := σ)
    have hDW₀_0 := alongCurveWithin_variationField_maximalGeodesic_zero
      (hσ.self_of_nhds.of_le (by simp))
    rw [hbase, hinterval] at hW₀ hDW₀_0
    have hW := hW₀.comp_affine 1 (-a) hJ.uniqueDiffOn hmaps
    let X : ∀ t, TangentSpace I (γ t) := fun t ↦
      tangentSpaceCast I (maximalGeodesic I M p v (φ t)) (γ t) (variationField I F₀ (φ t))
    have hEq (t : ℝ) (ht : t ∈ s) :
        TotalSpace.mk' E (γ t) (X t) =
          TotalSpace.mk' E (maximalGeodesic I M p v (φ t)) (variationField I F₀ (φ t)) :=
      TotalSpace.ext (hcurve_max ht) (TauCeti.heq_tangentSpaceCast (hcurve_max ht).symm _)
    have hX : IsJacobiFieldOn I γ X s := hW.congr_totalSpace hEq
    have hzero : φ a = 0 := by simp [φ]
    have hXa : X a = J a := by
      have h1 : HEq (X a) (variationField I F₀ (φ a)) := (TotalSpace.ext_iff.mp (hEq a ha)).2
      have h2 : HEq (variationField I F₀ (φ a)) (J a) := by
        rw [hzero]
        exact heq_of_eq (hW₀_0.trans hpos)
      exact eq_of_heq (h1.trans h2)
    have hDXa : alongCurveWithin cov γ X s a = alongCurveWithin cov γ J s a := by
      have hheq : ∀ t ∈ s, HEq (X t) (variationField I F₀ (φ t)) :=
        fun t ht ↦ (TotalSpace.ext_iff.mp (hEq t ht)).2
      have hD1 : HEq (alongCurveWithin cov γ X s a)
          (alongCurveWithin cov (maximalGeodesic I M p v ∘ φ)
            (fun r ↦ variationField I F₀ (φ r)) s a) :=
        alongCurveWithin_congr_heq cov X (hcurve_max.eventuallyEq_of_mem self_mem_nhdsWithin)
          (hcurve_max ha) (mem_of_superset self_mem_nhdsWithin hheq) (hheq a ha)
      rw [hW₀.alongCurveWithin_comp_affine 1 (-a) hJ.uniqueDiffOn hmaps ha, one_smul] at hD1
      have hD2 : HEq (alongCurveWithin cov (maximalGeodesic I M p v) (variationField I F₀)
          (geodesicInterval I M p v) (φ a)) (alongCurveWithin cov γ J s a) := by
        rw [hzero]
        exact heq_of_eq (hDW₀_0.trans hvel)
      exact eq_of_heq (hD1.trans hD2)
    have hXJ : ∀ t ∈ s, X t = J t := fun _ ht ↦
      hX.eq_of_eq_of_alongCurveWithin_eq hJ hs ha hXa hDXa ht
    refine ⟨F, U, V, hU, hV, h0U, hKV, hF_smooth, hF_geod, hF0_eq, fun t ht ↦ ?_⟩
    have hvar : variationField I F t = variationField I F₀ (φ t) := by
      rw [variationField_def, variationField_def]
    rw [← hXJ t ht, hEq t ht]
    exact TotalSpace.ext (congrFun hbase (φ t)) (heq_of_eq hvar)

/-- Every Jacobi field along a geodesic on a compact preconnected parameter set `s` (such as a
closed interval `[a, b]`) is realized by a single smooth geodesic variation defined on a product of
open sets `U ×ˢ V` with `0 ∈ U` and `s ⊆ V`. -/
theorem IsJacobiFieldOn.exists_geodesicVariation
    {γ : ℝ → M} {s : Set ℝ} {J : ∀ t, TangentSpace I (γ t)}
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) (hK : IsCompact s) :
    ∃ (F : ℝ → ℝ → M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ s ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F q) V) ∧
      EqOn (F 0) γ s ∧
      (∀ t ∈ s, TotalSpace.mk' E (F 0 t) (variationField I F t) =
        TotalSpace.mk' E (γ t) (J t)) :=
  hJ.exists_geodesicVariation_of_isCompact hs hK Subset.rfl

end General

end TauCeti.Manifold
