/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Domain
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic

/-!
# The Levi-Civita connection in revolution coordinates

The inherited charts on an open parameter domain read the native induced metric as the
computed first fundamental form. This identifies its Levi-Civita Christoffel map with the
explicit angular and meridional coefficients.
-/

public noncomputable section

open Bundle FiberBundle Filter Manifold Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti.SurfaceOfRevolution

open TauCeti.Manifold

local notation "P" => ℝ × ℝ
local notation "IP" => 𝓘(ℝ, P)

/-- Every inherited chart on an open coordinate domain reads off the ambient coordinates. -/
theorem extChartAt_apply (U : Opens P) (p q : U) : extChartAt IP p q = q.val := by
  simp [extChartAt, Opens.chartAt_eq]

section NativeMetric

variable {f g : ℝ → ℝ} {U : Opens P}
  [RiemannianBundle (fun p : U ↦ TangentSpace IP p)]
  [IsContMDiffRiemannianBundle IP ∞ P (fun p : U ↦ TangentSpace IP p)]

local instance (priority := 10000) :
    IsContMDiffRiemannianBundle IP 1 P (fun p : U ↦ TangentSpace IP p) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by norm_num)

private theorem chartMetric_eventuallyEq
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      metric f g p.val
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)))
    (p : U) :
    (Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle IP U).chartMetric p =ᶠ[𝓝 p.val]
      metric f g := by
  let c := extChartAt IP p
  have hsource : p ∈ c.source := mem_extChartAt_source p
  have htarget : p.val ∈ c.target := by
    simpa only [c, extChartAt_apply] using c.map_source hsource
  have hinv : Tendsto c.symm (𝓝 p.val) (𝓝 p) := by
    have ht := ((contMDiffOn_extChartAt_symm (n := ∞) p p.val htarget).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)).continuousAt
    have hval : (extChartAt IP p).symm p.val = p := by
      rw [← extChartAt_apply U p p]
      exact c.left_inv hsource
    simpa only [hval] using ht.tendsto
  filter_upwards [hinv.eventually
    (Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := IP) p),
    (isOpen_extChartAt_target p).mem_nhds htarget] with z hframe hz
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro q
  rw [Manifold.ContMDiffNondegenerateMetric.chartMetric_apply
      (Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle IP U) hz,
    Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle_apply, hmetric]
  have hzval : ((c.symm z : U) : P) = z := by
    simpa only [c, extChartAt_apply] using c.right_inv hz
  have hb : c.symm z ∈ (trivializationAt P (TangentSpace IP : U → Type _) p).baseSet := by
    simpa only [c, extChartAt_source, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  rw [← (trivializationAt P (TangentSpace IP : U → Type _) p).symmL_apply
      (R := ℝ) hb w,
    ← (trivializationAt P (TangentSpace IP : U → Type _) p).symmL_apply
      (R := ℝ) hb q,
    hframe w, hframe q]
  have hid (a b r : P) : NormedSpace.fromTangentSpace b
      ((trivializationAt P (TangentSpace IP) a).symmL ℝ b r) = r := by
    rw [TangentBundle.symmL_model_space]
    rfl
  rw [hid, hid, hzval]

/-- The Christoffel map of the native Levi-Civita connection is the Christoffel map of the
computed first fundamental form, with the connection's field/direction argument convention. -/
theorem christoffelMap_eq
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      metric f g p.val
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)))
    (p : U) (w z : P) :
    christoffelMap (Module.finBasis ℝ P)
        ((CovariantDerivative.leviCivitaConnection IP U).isCovariantDerivativeOn
          (s := (trivializationAt P (TangentSpace IP) p).baseSet)) p w z =
      Manifold.christoffelSecondKind (metric f g) p.val z w := by
  have hLC :=
    ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection IP U
  rw [hLC.christoffelMap_apply_eq_christoffelSecondKind (Module.finBasis ℝ P)
    (mem_extChartAt_source p) (by simp) w z, extChartAt_apply]
  have heq := chartMetric_eventuallyEq hmetric p
  rw [Manifold.christoffelSecondKind_def, Manifold.christoffelSecondKind_def,
    heq.eq_of_nhds, heq.fderiv_eq]

/-- On an open time domain, the native geodesic equation is the ordinary second-order
coordinate equation for the computed metric. -/
theorem isGeodesicCurveOn_iff_coordinateEquation
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      metric f g p.val
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)))
    {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s) :
    Manifold.IsGeodesicCurveOn IP γ s ↔
      ContMDiffOn 𝓘(ℝ) IP 2 γ s ∧ ∀ t ∈ s,
        deriv (deriv (fun r ↦ (γ r).val)) t +
          Manifold.christoffelSecondKind (metric f g) (γ t).val
            (deriv (fun r ↦ (γ r).val) t) (deriv (fun r ↦ (γ r).val) t) = 0 := by
  rw [Manifold.isGeodesicCurveOn_iff_chart hs.uniqueDiffOn]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t ht
  have hchart : (extChartAt IP (γ t) ∘ γ) = fun r ↦ (γ r).val :=
    funext fun r ↦ extChartAt_apply U (γ t) (γ r)
  have hd : derivWithin (fun r ↦ (γ r).val) s =ᶠ[𝓝 t]
      deriv (fun r ↦ (γ r).val) := by
    filter_upwards [hs.mem_nhds ht] with r hr using derivWithin_of_isOpen hs hr
  rw [hchart, derivWithin_of_isOpen hs ht, hd.deriv_eq,
    derivWithin_of_isOpen hs ht, christoffelMap_eq hmetric]

end NativeMetric

end TauCeti.SurfaceOfRevolution
