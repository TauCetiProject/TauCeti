/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Space
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.InitialData
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Jacobi fields with prescribed initial data

Every pair of initial value and covariant velocity is realized by a Jacobi field on the entire
natural interval of a maximal geodesic. The construction differentiates the geodesic flow in a
curve of initial tangent vectors, using
`CovariantDerivative.exists_contMDiffAt_tangentCurve_initialData` and the initial-data formulas
for the geodesic-flow variation field.

On any nonempty preconnected parameter subset having unique derivatives, the existing initial-data
map at any parameter is therefore a linear equivalence. Its domain is the existing space of
canonically zero-extended interval sections, so the dimension is exactly twice the manifold
dimension. There are no arbitrary values outside the interval. Neither completeness nor a curvature
bound is needed.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (existence and uniqueness of Jacobi fields, and realization by geodesic variations).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Arbitrary initial value and covariant velocity are realized on the whole natural interval
of a maximal geodesic, without assuming completeness of the metric. -/
private theorem exists_isJacobiFieldOn_maximalGeodesic_initialData
    (p : M) (v u w : TangentSpace I p) :
    ∃ V : ∀ t, TangentSpace I (maximalGeodesic I M p v t),
      IsJacobiFieldOn I (maximalGeodesic I M p v) V (geodesicInterval I M p v) ∧
      V 0 = u ∧
      alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v) V
        (geodesicInterval I M p v) 0 = w := by
  obtain ⟨σ, hσ₀, hσ, hu, hw⟩ :=
    (leviCivitaConnection I M).exists_contMDiffAt_tangentCurve_initialData p v u w 0
  have hJ := isJacobiFieldOn_variationField_maximalGeodesic (hσ.of_le (by norm_num))
  have hD := alongCurveWithin_variationField_maximalGeodesic_zero (hσ.of_le (by norm_num))
  rw [hw] at hD
  rw [hσ₀] at hJ hD
  refine ⟨variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2), hJ, ?_, hD⟩
  rw [variationField_maximalGeodesic_zero, hu]

/-- Surjectivity at zero on the full natural interval is the starting point for changing the
initial time by finite-dimensional linear algebra. -/
private theorem jacobiInitialData_surjective_maximalGeodesic_zero
    (p : M) (v : TangentSpace I p) :
    Function.Surjective (jacobiInitialData
      (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
      zero_mem_geodesicInterval) := by
  rintro ⟨u, w⟩
  obtain ⟨V, hV, hu, hw⟩ := exists_isJacobiFieldOn_maximalGeodesic_initialData p v u w
  refine ⟨hV.toJacobiFieldSpace, ?_⟩
  rw [jacobiInitialData_apply, hV.toJacobiFieldSpace_apply zero_mem_geodesicInterval,
    hV.alongCurveWithin_toJacobiFieldSpace zero_mem_geodesicInterval, hu, hw]

/-- The full natural interval has the expected dimension, before choosing any initial time. -/
private theorem finrank_jacobiFieldSpace_maximalGeodesic_full
    (p : M) (v : TangentSpace I p) :
    Module.finrank ℝ (jacobiFieldSpace
      (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn) =
        2 * Module.finrank ℝ E := by
  let e := LinearEquiv.ofBijective (jacobiInitialData
    (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn zero_mem_geodesicInterval)
    ⟨jacobiInitialData_injective _ isPreconnected_geodesicInterval zero_mem_geodesicInterval,
      jacobiInitialData_surjective_maximalGeodesic_zero p v⟩
  simpa [Module.finrank_prod, TauCeti.finrank_tangentSpace, two_mul] using e.finrank_eq

/-- At every initial time, arbitrary Jacobi data are realized on any subset of the maximal
geodesic interval having unique derivatives. The subset need not contain time zero or be
preconnected: restrict the solution from the full natural interval. -/
theorem jacobiInitialData_surjective_maximalGeodesic
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s) :
    Function.Surjective (jacobiInitialData
      ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono hs hsub) ha) := by
  let hγ := (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
  let := finiteDimensional_jacobiFieldSpace hγ isPreconnected_geodesicInterval
    zero_mem_geodesicInterval
  have hdim : Module.finrank ℝ (jacobiFieldSpace hγ) =
      Module.finrank ℝ (TangentSpace I (maximalGeodesic I M p v a) ×
        TangentSpace I (maximalGeodesic I M p v a)) := by
    rw [finrank_jacobiFieldSpace_maximalGeodesic_full, Module.finrank_prod,
      TauCeti.finrank_tangentSpace, two_mul]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (jacobiInitialData_injective hγ isPreconnected_geodesicInterval (hsub ha))
  rintro ⟨u, w⟩
  obtain ⟨V, hV⟩ := hsurj (u, w)
  have hJ := isJacobiFieldOn_of_mem_jacobiFieldSpace V
  have hJs := hJ.mono hs hsub
  refine ⟨hJs.toJacobiFieldSpace, ?_⟩
  rw [jacobiInitialData_apply, hJs.toJacobiFieldSpace_apply ha,
    hJs.alongCurveWithin_toJacobiFieldSpace ha, hJ.alongCurveWithin_subset (hs a ha) hsub ha]
  simpa only [jacobiInitialData_apply] using hV

/-- Initial value and covariant velocity at any parameter identify the space of Jacobi fields
on a preconnected subset of a maximal geodesic interval with two copies of that tangent space. -/
def maximalGeodesicJacobiInitialDataEquiv
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hconn : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s) :
    jacobiFieldSpace
        ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono hs hsub) ≃ₗ[ℝ]
      TangentSpace I (maximalGeodesic I M p v a) ×
        TangentSpace I (maximalGeodesic I M p v a) :=
  LinearEquiv.ofBijective (jacobiInitialData _ ha)
    ⟨jacobiInitialData_injective _ hconn ha,
      jacobiInitialData_surjective_maximalGeodesic p v hs hsub ha⟩

/-- The initial-data equivalence evaluates to the value and covariant velocity of the field. -/
@[simp]
theorem maximalGeodesicJacobiInitialDataEquiv_apply
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hconn : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s)
    (V : jacobiFieldSpace
      ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono hs hsub)) :
    maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha V =
      (V.val a, alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v)
        V.val s a) :=
  jacobiInitialData_apply _ ha V

/-- The inverse initial-data equivalence has the prescribed value at the initial parameter. -/
@[simp]
theorem maximalGeodesicJacobiInitialDataEquiv_symm_apply_value
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hconn : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s)
    (u w : TangentSpace I (maximalGeodesic I M p v a)) :
    ((maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha).symm (u, w)).val a = u := by
  have h := (maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha).apply_symm_apply (u, w)
  rw [maximalGeodesicJacobiInitialDataEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The inverse initial-data equivalence has the prescribed covariant velocity. -/
@[simp]
theorem alongCurveWithin_maximalGeodesicJacobiInitialDataEquiv_symm
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hconn : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s)
    (u w : TangentSpace I (maximalGeodesic I M p v a)) :
    alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v)
      ((maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha).symm (u, w)).val s a = w := by
  have h := (maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha).apply_symm_apply (u, w)
  rw [maximalGeodesicJacobiInitialDataEquiv_apply] at h
  exact congrArg Prod.snd h

/-- The dimension of Jacobi fields on a nonempty preconnected portion of a maximal geodesic
is exactly twice the manifold dimension, including zero-dimensional and constant geodesics. -/
theorem finrank_jacobiFieldSpace_maximalGeodesic
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hconn : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s) :
    Module.finrank ℝ (jacobiFieldSpace
      ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono hs hsub)) =
        2 * Module.finrank ℝ E := by
  simpa [Module.finrank_prod, TauCeti.finrank_tangentSpace, two_mul] using
    (maximalGeodesicJacobiInitialDataEquiv p v hs hconn hsub ha).finrank_eq

end TauCeti.Manifold
