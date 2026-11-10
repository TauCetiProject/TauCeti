/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Topology.FiberBundle.Separation

/-!
# The geodesic equation at the endpoints of a closed interval

A curve which is `C²` within a nondegenerate closed interval `[a, b]` and satisfies the geodesic
equation on the open interval `(a, b)` satisfies it on `[a, b]`, with the derivatives at `a` and
`b` taken within `[a, b]`. Indeed, the covariant acceleration within `[a, b]` is continuous on
`[a, b]` as a curve in the tangent bundle, and it agrees with the zero section on the dense subset
`(a, b)`.

Only a `C¹` metric is needed, and the manifold may have boundary or corners. Nothing is assumed
about the curve outside `[a, b]`.

## Main results

* `TauCeti.Manifold.isGeodesicCurveOn_Icc_of_isGeodesicCurveOn_Ioo`: a `C²` curve on `[a, b]`
  which is a geodesic on `(a, b)` is a geodesic on `[a, b]`.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {a b : ℝ}

/-- **The geodesic equation extends to the endpoints.** If `a < b` and `γ` is `C²` within `[a, b]`
and a geodesic on `(a, b)`, then `γ` is a geodesic on `[a, b]`. -/
theorem isGeodesicCurveOn_Icc_of_isGeodesicCurveOn_Ioo (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ (Icc a b)) (hgeo : IsGeodesicCurveOn I γ (Ioo a b)) :
    IsGeodesicCurveOn I γ (Icc a b) := by
  let cov := leviCivitaConnection I M
  have : IsManifold I (0 + 1) M := by
    simpa using (IsManifold.of_le (I := I) (M := M) (m := 1) (n := 2) (by norm_num))
  have : ContMDiffVectorBundle (0 + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I)
  have hvel := hγ.contMDiffOn_curveVelocityLiftWithin (m := 1) (by norm_num)
    (uniqueDiffOn_Icc hab).uniqueMDiffOn
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun t ↦ TotalSpace.mk' E (γ t) (accelerationWithin cov γ (Icc a b) t)) (Icc a b) := by
    have h := cov.contMDiffOn_alongCurveWithin (n := 0) γ
      (curveVelocityWithin I γ (Icc a b))
      (fun x ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection
        (m := 2) (k := 1) (trivializationAt E (TangentSpace I) x).open_baseSet
        (by norm_num) (by norm_num))
      (uniqueDiffOn_Icc hab)
      (by simpa only [← curveVelocityLiftWithin_apply, zero_add] using hvel)
    simpa only [accelerationWithin_def] using h
  have hzero : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun t ↦ TotalSpace.mk' E (γ t) (0 : TangentSpace I (γ t))) (Icc a b) :=
    (contMDiff_zeroSection ℝ (TangentSpace I) (n := 0)).comp_contMDiffOn (hγ.of_le (by norm_num))
  have he : EqOn
      (fun t ↦ TotalSpace.mk' E (γ t) (accelerationWithin cov γ (Icc a b) t))
      (fun t ↦ TotalSpace.mk' E (γ t) (0 : TangentSpace I (γ t))) (Ioo a b) := by
    intro t ht
    have h := hgeo.accelerationWithin_eq_zero t ht
    rw [accelerationWithin_of_mem_nhds _ _ (Ioo_mem_nhds ht.1 ht.2)] at h
    apply TotalSpace.mk_inj.2
    rw [accelerationWithin_of_mem_nhds cov γ (Icc_mem_nhds ht.1 ht.2)]
    exact h
  have he' := he.of_subset_closure hA.continuousOn hzero.continuousOn
    Ioo_subset_Icc_self (closure_Ioo hab.ne).symm.subset
  exact ⟨uniqueDiffOn_Icc hab, hγ, fun t ht ↦ TotalSpace.mk_inj.1 (he' ht)⟩

end TauCeti.Manifold
