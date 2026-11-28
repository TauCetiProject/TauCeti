/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Native round-sphere connection in stereographic coordinates

The preferred chart at a sphere point projects from its antipode. Its metric is the
scale-two stereographic metric. The native Levi-Civita Christoffel map is therefore the
explicit bilinear formula of this metric.
-/

public noncomputable section

open Bundle FiberBundle Manifold Metric Set
open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold.SphereStereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

local notation "S" => sphere (0 : E) 1
local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The actual native round metric in the preferred chart is the scale-two coordinate
metric on the whole stereographic target. This identifies the chart metric used by the native
Levi-Civita connection with the metric of the coordinate Christoffel formula. -/
theorem chartMetric_eq (p : S) :
    (ContMDiffNondegenerateMetric.ofRiemannianBundle (𝓡 n) S).chartMetric p =
      metric (E := V) 2 := by
  funext y
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have ht : y ∈ (extChartAt (𝓡 n) p).target := by
    rw [extChartAt_target, chartAt_sphere]
    simp
  have hs := (extChartAt (𝓡 n) p).map_target ht
  have hc : (extChartAt (𝓡 n) p).symm y ∈ (chartAt V p).source := by
    simpa only [extChartAt_source] using hs
  have hinv (w : V) :
      (trivializationAt V (TangentSpace (𝓡 n)) p).symm ((extChartAt (𝓡 n) p).symm y) w =
        mfderivWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (range (𝓡 n))
          (extChartAt (𝓡 n) p ((extChartAt (𝓡 n) p).symm y)) w := by
    rw [← (trivializationAt V (TangentSpace (𝓡 n)) p).symmL_apply (R := ℝ) hc w]
    exact congrArg (fun f ↦ f w) (TangentBundle.symmL_trivializationAt (I := 𝓡 n) hc)
  rw [ContMDiffNondegenerateMetric.chartMetric_apply _ ht,
    ContMDiffNondegenerateMetric.ofRiemannianBundle_apply]
  simp only [hinv]
  have hr : range (𝓡 n) = (univ : Set V) := by simp
  rw [(extChartAt (𝓡 n) p).right_inv ht, hr, mfderivWithin_univ, extChartAt_sphere,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm]
  exact (metric_two_apply_eq_inner_mfderiv (-p) y u v).symm

/-- The native Levi-Civita Christoffel map in the preferred stereographic chart, for any
finite basis of the model space.
The field argument precedes the direction argument. At the projection pole the formula gives
the zero value of the extended Christoffel map. -/
theorem christoffelMap_eq {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (p q : S) (u v : V) :
    christoffelMap b
      ((CovariantDerivative.leviCivitaConnection (𝓡 n) S).isCovariantDerivativeOn
        (s := (trivializationAt V (TangentSpace (𝓡 n)) p).baseSet)) q u v =
      (-2 / (4 + ‖extChartAt (𝓡 n) p q‖ ^ 2)) •
        (inner ℝ (extChartAt (𝓡 n) p q) u • v +
          inner ℝ (extChartAt (𝓡 n) p q) v • u - inner ℝ v u • extChartAt (𝓡 n) p q) := by
  by_cases hq : q = -p
  · subst q
    have hs : -p ∉ (trivializationAt V (TangentSpace (𝓡 n)) p).baseSet := by
      simp [TangentBundle.trivializationAt_baseSet, chartAt_sphere]
    rw [christoffelMap_of_notMem b _ hs, extChartAt_sphere_apply_neg]
    simp
  have hs : q ∈ (extChartAt (𝓡 n) p).source := by
    rw [extChartAt_source, chartAt_sphere]
    simpa only [stereographic'_source, mem_compl_iff, mem_singleton_iff] using hq
  have hLC :=
    ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
      (𝓡 n) S
  rw [hLC.christoffelMap_apply_eq_christoffelSecondKind
    b hs (by simp) u v, chartMetric_eq,
    christoffelSecondKind_metric_apply two_ne_zero]
  norm_num

end TauCeti.Manifold.SphereStereographic
