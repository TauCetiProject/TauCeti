/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Smooth Jacobi propagation from infinitesimal geodesic initial states

The derivative of the geodesic flow with respect to its initial state sends a tangent
vector to `TM` to a Jacobi field. The operator `geodesicJacobiPropagator` gives its value
at each time. Its tangent-bundle lift is jointly smooth in the initial state, its tangent
vector, and time on the natural geodesic-flow domain. Thus this construction also applies
to incomplete metrics and to compact segments containing their endpoints.

The initial tangent vector is intrinsic data in `T(TM)`. Every differentiable
initial-state curve with that velocity gives the same
field. At time zero the propagator is the differential of the bundle projection.

The construction differentiates `contMDiffOn_maximalGeodesic` using Mathlib's tangent-map
and product-tangent-bundle APIs. Its Jacobi equation follows from
`isJacobiFieldOn_variationField_maximalGeodesic`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (Jacobi fields and the differential of the geodesic flow).
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TangentBundle

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The linear map taking an infinitesimal geodesic initial state to the Jacobi field's
value at time `t`. Its geometric properties hold on the natural maximal geodesic interval. -/
def geodesicJacobiPropagator (z : TangentBundle I M) (t : ℝ) :
    TangentSpace I.tangent z →L[ℝ] TangentSpace I (maximalGeodesic I M z.proj z.2 t) :=
  mfderiv I.tangent I (fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 t) z

omit [I.Boundaryless] [T2Space M] in
/-- The defining differential of Jacobi propagation in the initial state. -/
theorem geodesicJacobiPropagator_def (z : TangentBundle I M) (t : ℝ) :
    geodesicJacobiPropagator z t =
      mfderiv I.tangent I (fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 t) z :=
  (rfl)

/-- The full differential of the geodesic evaluation map, applied with zero time component,
is the Jacobi propagator. -/
theorem geodesicJacobiPropagator_apply (z : TangentBundle I M) {t : ℝ}
    (ht : t ∈ geodesicInterval I M z.proj z.2) (ξ : TangentSpace I.tangent z) :
    geodesicJacobiPropagator z t ξ =
      mfderiv (I.tangent.prod 𝓘(ℝ, ℝ)) I
        (fun q : TangentBundle I M × ℝ ↦ maximalGeodesic I M q.1.proj q.1.2 q.2)
        (z, t) (ξ, 0) := by
  have hF := (contMDiffOn_maximalGeodesic (I := I) (M := M)).contMDiffAt
    (isOpen_setOfPred_mem_geodesicInterval.mem_nhds (x := (z, t)) ht)
  rw [geodesicJacobiPropagator_def]
  have h := mfderiv_comp (f := fun w : TangentBundle I M ↦ (w, t))
    (g := fun q : TangentBundle I M × ℝ ↦ maximalGeodesic I M q.1.proj q.1.2 q.2)
    z (hF.mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_left] at h
  exact congrArg (fun L ↦ L ξ) h

/-- Jacobi propagation is jointly smooth in the initial state, its infinitesimal variation,
and time. The domain is the inverse image of the actual maximal-flow domain. -/
theorem contMDiffOn_geodesicJacobiPropagator :
    ContMDiffOn (I.tangent.tangent.prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : TangentBundle I.tangent (TangentBundle I M) × ℝ ↦
        TotalSpace.mk' E (maximalGeodesic I M q.1.proj.proj q.1.proj.2 q.2)
          (geodesicJacobiPropagator q.1.proj q.2 q.1.2))
      {q | q.2 ∈ geodesicInterval I M q.1.proj.proj q.1.proj.2} := by
  let ι : TangentBundle I.tangent (TangentBundle I M) × ℝ →
      TangentBundle (I.tangent.prod 𝓘(ℝ, ℝ)) (TangentBundle I M × ℝ) :=
    fun q ↦ (equivTangentBundleProd I.tangent (TangentBundle I M) 𝓘(ℝ, ℝ) ℝ).symm
      (q.1, TotalSpace.mk' ℝ q.2 0)
  have hι : ContMDiff (I.tangent.tangent.prod 𝓘(ℝ, ℝ))
      (I.tangent.prod 𝓘(ℝ, ℝ)).tangent ∞ ι :=
    contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_fst.prodMk (contMDiff_tangentBundle_mk_zero contMDiff_snd))
  intro q hq
  have hF := (contMDiffOn_maximalGeodesic (I := I) (M := M)).contMDiffAt
    (isOpen_setOfPred_mem_geodesicInterval.mem_nhds (x := (q.1.proj, q.2)) hq)
  have h := (hF.contMDiffAt_tangentMap (X := ι q) (m := ∞) (by simp)).comp q (hι q)
  have hdom : ∀ᶠ r : TangentBundle I.tangent (TangentBundle I M) × ℝ in 𝓝 q,
      r.2 ∈ geodesicInterval I M r.1.proj.proj r.1.proj.2 :=
    (((FiberBundle.continuous_proj (E × E) (TangentSpace I.tangent)).comp
      continuous_fst).prodMk continuous_snd).continuousAt.preimage_mem_nhds
      (isOpen_setOfPred_mem_geodesicInterval.mem_nhds (x := (q.1.proj, q.2)) hq)
  refine (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hdom] with r hr
  simp only [Function.comp_apply, tangentMap, ι, equivTangentBundleProd]
  exact congrArg (TotalSpace.mk' E _) (geodesicJacobiPropagator_apply r.1.proj hr r.1.2)

/-- Differentiating any initial-state curve gives the propagator applied to that curve's
velocity. Thus the resulting field depends only on the infinitesimal initial state. -/
theorem variationField_maximalGeodesic_eq_geodesicJacobiPropagator
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    {t : ℝ} (ht : t ∈ geodesicInterval I M (σ 0).proj (σ 0).2) :
    variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2) t =
      geodesicJacobiPropagator (σ 0) t (curveVelocity I.tangent σ 0) := by
  have hF := (contMDiffOn_maximalGeodesic (I := I) (M := M)).contMDiffAt
    (isOpen_setOfPred_mem_geodesicInterval.mem_nhds (x := (σ 0, t)) ht)
  have hs := (hF.comp (σ 0) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
    (by simp)
  have h := mfderiv_comp (f := σ)
    (g := fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 t) 0 hs hσ
  rw [variationField_apply, curveVelocity_apply, geodesicJacobiPropagator_def,
    curveVelocity_apply]
  simpa only [Function.comp_def, ContinuousLinearMap.coe_comp, Function.comp_apply] using
    congrArg (fun L ↦ L (1 : ℝ)) h

/-- Every infinitesimal initial state gives a Jacobi field on the entire natural maximal
interval. No completeness or nonzero-velocity hypothesis is imposed. -/
theorem isJacobiFieldOn_geodesicJacobiPropagator (z : TangentBundle I M)
    (ξ : TangentSpace I.tangent z) :
    IsJacobiFieldOn I (maximalGeodesic I M z.proj z.2)
      (fun t ↦ geodesicJacobiPropagator z t ξ) (geodesicInterval I M z.proj z.2) := by
  obtain ⟨σ, rfl, hσ, hξ⟩ := exists_contMDiffAt_curveVelocity_eq (I := I.tangent)
    (n := ∞) (by simp) z ξ (0 : ℝ)
  apply (isJacobiFieldOn_variationField_maximalGeodesic (hσ.of_le (by simp))).congr
  intro t ht
  rw [variationField_maximalGeodesic_eq_geodesicJacobiPropagator
    (hσ.mdifferentiableAt (by simp)) ht, hξ]

omit [I.Boundaryless] [T2Space M] in
/-- At time zero the Jacobi field is the base component of its infinitesimal initial state.
The heterogeneous equality transports the target fibre along `maximalGeodesic_zero`. -/
@[simp]
theorem geodesicJacobiPropagator_zero (z : TangentBundle I M) (ξ : TangentSpace I.tangent z) :
    HEq (geodesicJacobiPropagator z 0 ξ)
      (mfderiv I.tangent I (π E (TangentSpace I)) z ξ) := by
  have hfun : (fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 0) =
      π E (TangentSpace I) := funext fun w ↦ maximalGeodesic_zero w.proj w.2
  have h := congrArg (fun f : TangentBundle I M → M ↦
    tangentMap I.tangent I f (TotalSpace.mk' (E × E) z ξ)) hfun
  exact (TotalSpace.ext_iff.mp h).2

/-- The initial covariant derivative of Jacobi propagation agrees with the covariant velocity
of any curve differentiable at `0` representing its infinitesimal initial state. -/
@[simp]
theorem alongCurveWithin_geodesicJacobiPropagator_zero
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0) :
    CovariantDerivative.alongCurveWithin (CovariantDerivative.leviCivitaConnection I M)
      (maximalGeodesic I M (σ 0).proj (σ 0).2)
      (fun t ↦ geodesicJacobiPropagator (σ 0) t (curveVelocity I.tangent σ 0))
      (geodesicInterval I M (σ 0).proj (σ 0).2) 0 =
        CovariantDerivative.alongCurve (CovariantDerivative.leviCivitaConnection I M)
          (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
  let cov := CovariantDerivative.leviCivitaConnection I M
  -- Every `TangentSpace I.tangent z` reduces to the model product `E × E`; `split` records that
  -- identification explicitly so projections stay well-typed under `rw`.
  let split (z : TangentBundle I M) (ξ : TangentSpace I.tangent z) : E × E := ξ
  have halong {τ : ℝ → TangentBundle I M} (hτ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent τ 0) :
      cov.alongCurve (fun q ↦ (τ q).proj) (fun q ↦ (τ q).2) 0 =
        (trivializationAt E (TangentSpace I) (τ 0).proj).symmL ℝ (τ 0).proj
          ((split (τ 0) (curveVelocity I.tangent τ 0)).2 +
            christoffelMap (Module.finBasis ℝ E)
              (cov.isCovariantDerivativeOn
                (s := (trivializationAt E (TangentSpace I) (τ 0).proj).baseSet))
              (τ 0).proj
              (trivializationAt E (TangentSpace I) (τ 0).proj (τ 0)).2
              (split (τ 0) (curveVelocity I.tangent τ 0)).1) := by
    let x₀ := (τ 0).proj
    let e := trivializationAt E (TangentSpace I) x₀
    let ξ := split (τ 0) (curveVelocity I.tangent τ 0)
    obtain ⟨hcont, hbase, hfib⟩ := (hasMFDerivAt_totalSpace_curve_iff
      (z := τ) (t := 0) (a := ξ.1) (b := ξ.2)).mp (hasMFDerivAt_curveVelocity hτ)
    have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), (τ r).proj ∈ e.baseSet :=
      ((FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hcont).preimage_mem_nhds
        (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
    have hsec : sectionCoord (F := E) (fun q ↦ (τ q).proj) (fun q ↦ (τ q).2) x₀ =ᶠ[𝓝 0]
        fun r ↦ (e (τ r)).2 := by
      filter_upwards [hmem] with r hr
      rw [sectionCoord_apply]
      exact e.continuousLinearMapAt_apply_of_mem ℝ hr (τ r).2
    have hsec0 : sectionCoord (F := E) (fun q ↦ (τ q).proj) (fun q ↦ (τ q).2) x₀ 0 =
        (e (τ 0)).2 := by
      rw [sectionCoord_apply]
      exact e.continuousLinearMapAt_apply_of_mem ℝ
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀) (τ 0).2
    rw [CovariantDerivative.alongCurve_apply, CovariantDerivative.alongCurveInChartWithin_apply,
      derivWithin_univ, derivWithin_univ, Function.comp_def,
      (hfib.congr_of_eventuallyEq hsec).deriv, hbase.deriv, hsec0]
  have hprop (z : TangentBundle I M) (ξ : TangentSpace I.tangent z) :
      cov.alongCurveWithin (maximalGeodesic I M z.proj z.2)
        (fun t ↦ geodesicJacobiPropagator z t ξ) (geodesicInterval I M z.proj z.2) 0 =
          (trivializationAt E (TangentSpace I) z.proj).symmL ℝ z.proj
            ((split z ξ).2 +
              christoffelMap (Module.finBasis ℝ E)
                (cov.isCovariantDerivativeOn
                  (s := (trivializationAt E (TangentSpace I) z.proj).baseSet))
                z.proj (trivializationAt E (TangentSpace I) z.proj z).2 (split z ξ).1) := by
    obtain ⟨τ, rfl, hτ, rfl⟩ :=
      exists_contMDiffAt_curveVelocity_eq (I := I.tangent) (n := 2) (by norm_num) z ξ 0
    rw [← halong (hτ.mdifferentiableAt (by norm_num)),
      ← alongCurveWithin_variationField_maximalGeodesic_zero hτ]
    apply CovariantDerivative.alongCurveWithin_congr
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (variationField_maximalGeodesic_eq_geodesicJacobiPropagator
        (hτ.mdifferentiableAt (by norm_num)) ht).symm
    · exact (variationField_maximalGeodesic_eq_geodesicJacobiPropagator
        (hτ.mdifferentiableAt (by norm_num)) zero_mem_geodesicInterval).symm
  exact (hprop (σ 0) (curveVelocity I.tangent σ 0)).trans (halong hσ).symm

/-- A compact portion of a maximal geodesic has a common open time domain for all nearby
initial states, on which Jacobi propagation is smooth for every infinitesimal initial state.
In particular, closed segment endpoints do not require one-sided parameter derivatives. -/
theorem exists_contMDiffOn_geodesicJacobiPropagator_of_isCompact
    (z : TangentBundle I M) {K : Set ℝ} (hK : IsCompact K)
    (hsub : K ⊆ geodesicInterval I M z.proj z.2) :
    ∃ (U : Set (TangentBundle I M)) (V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ K ⊆ V ∧
        (∀ w ∈ U, V ⊆ geodesicInterval I M w.proj w.2) ∧
        ContMDiffOn (I.tangent.tangent.prod 𝓘(ℝ, ℝ)) I.tangent ∞
          (fun q : TangentBundle I.tangent (TangentBundle I M) × ℝ ↦
            TotalSpace.mk' E (maximalGeodesic I M q.1.proj.proj q.1.proj.2 q.2)
              (geodesicJacobiPropagator q.1.proj q.2 q.1.2))
          ((π (E × E) (TangentSpace I.tangent) ⁻¹' U) ×ˢ V) := by
  obtain ⟨U, V, hU, hV, hz, hKV, hdom, _⟩ :=
    z.exists_contMDiffOn_maximalGeodesic_of_isCompact hK hsub
  exact ⟨U, V, hU, hV, hz, hKV, hdom,
    contMDiffOn_geodesicJacobiPropagator.mono fun q hq ↦ hdom q.1.proj hq.1 hq.2⟩

end TangentBundle
