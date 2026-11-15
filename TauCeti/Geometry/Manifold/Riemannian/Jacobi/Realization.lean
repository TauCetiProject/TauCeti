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

* `IsJacobiFieldOn.exists_geodesicVariation_maximalGeodesic_of_isCompact_of_subset`:
  realization of a Jacobi field along `maximalGeodesic I M p v` around a compact subset, with
  `F 0 = maximalGeodesic I M p v` globally on `ℝ`.
* `IsJacobiFieldOn.exists_geodesicVariation_of_isCompact_of_subset`: realization of a Jacobi field
  along any geodesic on a preconnected parameter set around any compact subset.
* `IsJacobiFieldOn.exists_geodesicVariation_of_isCompact`: realization of a Jacobi field along any
  geodesic on a compact preconnected parameter set on an open neighbourhood of the whole set.

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

/-- Construct a smooth geodesic variation of `maximalGeodesic I M p v` around a compact subset of
its natural interval whose variation field on `geodesicInterval I M p v` has prescribed initial
value `u` and initial covariant derivative `w`. -/
private theorem exists_geodesicVariation_maximalGeodesic_initialData
    (p : M) (v u w : TangentSpace I p) {K₀ : Set ℝ} (hK₀ : IsCompact K₀)
    (hdom : K₀ ⊆ geodesicInterval I M p v) :
    ∃ (F₀ : ℝ → ℝ → M) (U V₀ : Set ℝ),
      IsOpen U ∧ IsOpen V₀ ∧ 0 ∈ U ∧ K₀ ⊆ V₀ ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F₀ z.1 z.2) (U ×ˢ V₀) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F₀ q) V₀) ∧
      F₀ 0 = maximalGeodesic I M p v ∧
      IsJacobiFieldOn I (maximalGeodesic I M p v) (variationField I F₀)
        (geodesicInterval I M p v) ∧
      variationField I F₀ 0 = u ∧
      alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v)
        (variationField I F₀) (geodesicInterval I M p v) 0 = w := by
  obtain ⟨σ, hσ0, hσ, hpos, hvel⟩ := TangentSpace.exists_smooth_initialData (v := v) u w
  let F₀ : ℝ → ℝ → M := fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2
  have hbase : F₀ 0 = maximalGeodesic I M p v :=
    congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.2) hσ0
  have hinterval : geodesicInterval I M (σ 0).proj (σ 0).2 = geodesicInterval I M p v :=
    congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.2) hσ0
  obtain ⟨U, V₀, hU, hV₀, h0U, hK₀V₀, hF₀, hgeod₀⟩ :=
    exists_contMDiffOn_maximalGeodesic_comp_of_isCompact (n := ⊤) hσ hK₀
      (hinterval.symm ▸ hdom)
  have hW₀ := isJacobiFieldOn_variationField_maximalGeodesic (hσ.self_of_nhds.of_le (by simp))
  have hW₀_0 := (variationField_maximalGeodesic_zero (I := I) (σ := σ)).trans hpos
  have hDW₀_0 := (alongCurveWithin_variationField_maximalGeodesic_zero
    (hσ.self_of_nhds.of_le (by simp))).trans hvel
  -- Every `TangentSpace I _` reduces to the model space `E`, so rewriting `σ 0` along `hσ0` keeps
  -- `variationField I F₀` typed as a section along `maximalGeodesic I M p v`.
  rw [hσ0] at hW₀ hDW₀_0
  exact ⟨F₀, U, V₀, hU, hV₀, h0U, hK₀V₀, hF₀, hgeod₀, hbase, hW₀, hW₀_0, hDW₀_0⟩

section Maximal

variable {p : M} {v : TangentSpace I p} {s : Set ℝ}
  {J : ∀ t, TangentSpace I (maximalGeodesic I M p v t)}

/-- A Jacobi field along a maximal geodesic is realized by a smooth geodesic variation on a common
open time domain around every prescribed compact subset, with central curve equal globally on `ℝ`
to `maximalGeodesic I M p v`. The nearby curves are not asserted to have fixed endpoints. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_maximalGeodesic_of_isCompact_of_subset
    (hJ : IsJacobiFieldOn I (maximalGeodesic I M p v) J s)
    (hs : IsPreconnected s) (h0 : 0 ∈ s)
    {K : Set ℝ} (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ (F : ℝ → ℝ → M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ K ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F q) V) ∧
      F 0 = maximalGeodesic I M p v ∧
      (∀ t ∈ s, variationField I F t = J t) := by
  have hsub : s ⊆ geodesicInterval I M p v :=
    hJ.isGeodesicCurveOn.subset_geodesicInterval_of_maximalGeodesic hs h0
  obtain ⟨F, U, V, hU, hV, h0U, hKV, hF, hgeod, hF0, hW, hW0, hDW0⟩ :=
    exists_geodesicVariation_maximalGeodesic_initialData p v (J 0)
      (alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v) J s 0)
      hK (hKs.trans hsub)
  refine ⟨F, U, V, hU, hV, h0U, hKV, hF, hgeod, hF0, fun t ht ↦ ?_⟩
  refine (hW.mono hJ.uniqueDiffOn hsub).eq_of_eq_of_alongCurveWithin_eq hJ hs h0 hW0 ?_ ht
  rw [hW.alongCurveWithin_subset (hJ.uniqueDiffOn 0 h0) hsub h0, hDW0]

end Maximal

section General

/-- **Realization of Jacobi fields by geodesic variations.** Every Jacobi field along a geodesic on
a preconnected parameter set `s` is realized by a smooth geodesic variation on a common open time
domain `V` around any compact subset `K ⊆ s`. On all of `s`, the central curve `F 0` agrees with `γ`
and the tangent-bundle lift of `variationField I F` agrees with that of `J`. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_of_isCompact_of_subset
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
    let φ : ℝ → ℝ := fun t ↦ t - a
    have hmaps : MapsTo φ s (geodesicInterval I M p v) :=
      fun _ ht ↦ hJ.isGeodesicCurveOn.sub_mem_geodesicInterval_of_isPreconnected hs ha ht
    have hK₀ : IsCompact (φ '' K) := hK.image (by fun_prop)
    have hdom : φ '' K ⊆ geodesicInterval I M p v :=
      image_subset_iff.mpr (hKs.trans hmaps)
    obtain ⟨F₀, U, V₀, hU, hV₀, h0U, hK₀V₀, hF₀, hgeod₀, hbase, hW₀, hW₀_0, hDW₀_0⟩ :=
      exists_geodesicVariation_maximalGeodesic_initialData p v (J a)
        (alongCurveWithin cov γ J s a) hK₀ hdom
    let F : ℝ → ℝ → M := fun q t ↦ F₀ q (φ t)
    let V : Set ℝ := φ ⁻¹' V₀
    have hV : IsOpen V := hV₀.preimage (by fun_prop)
    have hKV : K ⊆ V := image_subset_iff.mp hK₀V₀
    have hF_smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) :=
      hF₀.comp (contMDiff_iff_contDiff.mpr
        (by fun_prop : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ (z.1, φ z.2))).contMDiffOn
        fun _ hz ↦ ⟨hz.1, hz.2⟩
    have hF_geod : ∀ q ∈ U, IsGeodesicCurveOn I (F q) V := fun q hq ↦ by
      simpa only [F, φ, Function.comp_def, one_mul, ← sub_eq_add_neg] using
        (hgeod₀ q hq).comp_affine 1 (-a) hV.uniqueDiffOn
          fun _ hr ↦ by simpa only [V, φ, mem_preimage, one_mul, ← sub_eq_add_neg] using hr
    have hcurve_max : EqOn γ (fun t ↦ maximalGeodesic I M p v (φ t)) s :=
      fun _ ht ↦ (hJ.isGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected hs ha ht).symm
    have hF0_eq : EqOn (F 0) γ s := fun t ht ↦
      (congrFun hbase (φ t)).trans (hcurve_max ht).symm
    -- Pull `variationField I F₀` back along `φ` via `tangentSpaceCast` and match initial data at
    -- `a`; note `variationField I F₀ (φ t)` lives in `TangentSpace I (F₀ 0 (φ t))`, which reduces
    -- to the same model space `E` as `TangentSpace I (maximalGeodesic I M p v (φ t))`.
    let X : ∀ t, TangentSpace I (γ t) := fun t ↦
      tangentSpaceCast I (maximalGeodesic I M p v (φ t)) (γ t) (variationField I F₀ (φ t))
    obtain ⟨hXa, hDXa⟩ := Prod.mk.inj
      (hW₀.prodMk_alongCurveWithin_comp_sub_const_eq_of_eqOn_of_heq
        hJ.uniqueDiffOn hmaps hcurve_max ha (heq_of_eq hW₀_0) (heq_of_eq hDW₀_0))
    have hXJ : ∀ t ∈ s, X t = J t := fun _ ht ↦
      (hW₀.comp_sub_const_of_eqOn a hJ.uniqueDiffOn hmaps
        hcurve_max).eq_of_eq_of_alongCurveWithin_eq hJ hs ha hXa hDXa ht
    refine ⟨F, U, V, hU, hV, h0U, hKV, hF_smooth, hF_geod, hF0_eq, fun t ht ↦ ?_⟩
    have hvar : variationField I F t = variationField I F₀ (φ t) := by
      rw [variationField_def, variationField_def]
    rw [← hXJ t ht]
    exact TotalSpace.ext (hF0_eq ht)
      ((heq_of_eq hvar).trans (TauCeti.heq_tangentSpaceCast (hcurve_max ht).symm _).symm)

/-- Every Jacobi field along a geodesic on a compact preconnected parameter set `s` (such as a
closed interval `[a, b]`) is realized by a single smooth geodesic variation defined on a product of
open sets `U ×ˢ V` with `0 ∈ U` and `s ⊆ V`. -/
theorem IsJacobiFieldOn.exists_geodesicVariation_of_isCompact
    {γ : ℝ → M} {s : Set ℝ} {J : ∀ t, TangentSpace I (γ t)}
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) (hK : IsCompact s) :
    ∃ (F : ℝ → ℝ → M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ s ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) ∧
      (∀ q ∈ U, IsGeodesicCurveOn I (F q) V) ∧
      EqOn (F 0) γ s ∧
      (∀ t ∈ s, TotalSpace.mk' E (F 0 t) (variationField I F t) =
        TotalSpace.mk' E (γ t) (J t)) :=
  hJ.exists_geodesicVariation_of_isCompact_of_subset hs hK Subset.rfl

end General

end TauCeti.Manifold
