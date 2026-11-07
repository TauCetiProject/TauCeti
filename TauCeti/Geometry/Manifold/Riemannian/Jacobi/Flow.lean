/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Flow
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Variation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# Jacobi fields from the geodesic flow

A smooth curve `σ` in the tangent bundle specifies varying initial positions and velocities.
The family `F(q,t) = maximalGeodesic (σ q).proj (σ q).2 t` is a geodesic variation on a common
neighbourhood of every compact subset of the central geodesic's maximal interval. Its variation
field is Jacobi on that entire maximal interval. At time zero its value is the velocity of the
initial-position curve and its covariant derivative is the covariant derivative of the
initial-velocity section along that curve.

These results allow the base point to vary, unlike radial exponential variations. They provide
the initial-data calculation needed to construct Jacobi fields from geodesic variations, without
requiring completeness of the metric or an all-time geodesic flow. The family is the actual
maximal geodesic flow, and no assertion is made outside its natural domain.

The construction uses `contMDiffOn_maximalGeodesic` and
`isJacobiFieldOn_variationField`; the initial derivative follows from the torsion-free symmetry
of the mixed covariant derivatives.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (Jacobi fields and geodesic variations).
-/

public section

open Bundle CovariantDerivative Filter Set
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
  {σ : ℝ → TangentBundle I M}

/-- Varying initial positions and velocities by a smooth tangent-bundle curve gives a Jacobi
field on the entire maximal interval of the central geodesic. -/
theorem isJacobiFieldOn_variationField_maximalGeodesic
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 σ 0) :
    IsJacobiFieldOn I (maximalGeodesic I M (σ 0).proj (σ 0).2)
      (variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2))
      (geodesicInterval I M (σ 0).proj (σ 0).2) := by
  refine isJacobiFieldOn_variationField
    (F := fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2) isOpen_geodesicInterval
    (fun _ ht ↦ contMDiffAt_maximalGeodesic_comp hσ ht) ?_
  intro t ht
  have hdom : ∀ᶠ q in 𝓝 0, t ∈ geodesicInterval I M (σ q).proj (σ q).2 :=
    (hσ.continuousAt.prodMk continuousAt_const).preimage_mem_nhds
      (isOpen_setOfPred_mem_geodesicInterval.mem_nhds ht)
  exact hdom.mono fun q hq ↦ acceleration_maximalGeodesic_eq_zero hq

/-- The initial value of the geodesic-flow variation field is the velocity of the
initial-position curve. No regularity hypothesis is needed for this identity. -/
@[simp]
theorem variationField_maximalGeodesic_zero :
    variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2) 0 =
      curveVelocity I (fun q ↦ (σ q).proj) 0 := by
  rw [variationField_apply,
    funext fun q ↦ maximalGeodesic_zero (I := I) (σ q).proj (σ q).2]

/-- The initial covariant velocity of the geodesic-flow variation field is the covariant
derivative of the initial-velocity section along the initial-position curve. -/
@[simp]
theorem alongCurveWithin_variationField_maximalGeodesic_zero
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 σ 0) :
    alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M (σ 0).proj (σ 0).2)
      (variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2))
      (geodesicInterval I M (σ 0).proj (σ 0).2) 0 =
        alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [alongCurveWithin_of_mem_nhds _ _ _
    (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval), variationField_def,
    alongCurve_curveVelocity_comm (leviCivitaConnection I M)
      ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
      (f := fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2) (u := 0) (v := 0)
      ((contMDiffAt_maximalGeodesic_comp hσ zero_mem_geodesicInterval).of_le
        (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))]
  have hvel (q : ℝ) :
      curveVelocity I (maximalGeodesic I M (σ q).proj (σ q).2) 0 = (σ q).2 := by
    rw [← curveVelocityWithin_of_mem_nhds
      (isOpen_geodesicInterval.mem_nhds (zero_mem_geodesicInterval (p := (σ q).proj)
        (v := (σ q).2)))]
    exact eq_of_heq (isGeodesicCurveOnFrom_maximalGeodesic (σ q).proj (σ q).2).velocity_heq
  -- The transverse base curve agrees literally with the initial-position curve; tangent fibres
  -- are the same model space, so rewriting the curve also transports its velocity section.
  rw [funext fun q ↦ maximalGeodesic_zero (I := I) (σ q).proj (σ q).2]
  exact alongCurve_congr _ _ _ (.of_forall hvel)

end TauCeti.Manifold
