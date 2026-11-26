/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# The Riemannian volume measure on a manifold boundary

Let `M` be a manifold with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), `n ≥ 0`,
equipped with a continuous Riemannian metric. The induced Riemannian metric
`TauCeti.halfSpaceBoundaryMetric` defines the induced boundary volume measure
`TauCeti.halfSpaceBoundaryVolume`. For `n = 0`, this is counting measure on the boundary.

## Main definitions

* `TauCeti.halfSpaceBoundaryVolume`: Riemannian volume measure of the induced boundary metric.

## Main results

* `TauCeti.halfSpaceBoundaryVolume_eq_riemannianVolume`: unfolds `TauCeti.halfSpaceBoundaryVolume`
  as `TauCeti.riemannianVolume` on the boundary.
* `TauCeti.halfSpaceBoundaryVolume_zero_eq_count`,
  `TauCeti.halfSpaceBoundaryVolume_zero_singleton`: for `n = 0`, counting measure on `∂M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33 and Chapter 16 (induced boundary volume).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the Riemannian density on submanifolds and boundaries).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold

namespace TauCeti

/-! ### The induced Riemannian volume measure on the boundary -/

section BoundaryVolume

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The **Riemannian boundary volume measure** on `(𝓡∂ (n + 1)).boundary M`, i.e.
`TauCeti.riemannianVolume` of `TauCeti.halfSpaceBoundaryMetric` (`LindelofSpace` descends). -/
noncomputable def halfSpaceBoundaryVolume : Measure ((𝓡∂ (n + 1)).boundary M) :=
  let _ := isManifold_boundary (n := n) (k := 1) M
  riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M)

/-- Unfold `TauCeti.halfSpaceBoundaryVolume` as `TauCeti.riemannianVolume` on the boundary. -/
theorem halfSpaceBoundaryVolume_eq_riemannianVolume
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] :
    halfSpaceBoundaryVolume (n := n) (M := M) =
      riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) := by rfl

/-- The Riemannian boundary volume measure is locally finite. -/
instance isLocallyFiniteMeasure_halfSpaceBoundaryVolume :
    IsLocallyFiniteMeasure (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  let _ := isManifold_boundary (n := n) (k := 1) M
  rw [halfSpaceBoundaryVolume_eq_riemannianVolume]; infer_instance

end BoundaryVolume

/-! ### Zero-dimensional boundary volume (`n = 0`) -/

section ZeroDimBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) 1 M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1)) (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]

/-- For `n = 0`, the induced boundary measure is counting measure on the boundary. -/
theorem halfSpaceBoundaryVolume_zero_eq_count :
    halfSpaceBoundaryVolume (n := 0) (M := M) = Measure.count := by
  let _ := isManifold_boundary (n := 0) (k := 1) M
  exact riemannianVolume_eq_count_of_subsingleton

/-- Each boundary point of a one-dimensional Riemannian manifold with boundary has measure `1`. -/
@[simp]
theorem halfSpaceBoundaryVolume_zero_singleton (x : (𝓡∂ 1).boundary M) :
    halfSpaceBoundaryVolume (n := 0) (M := M) {x} = 1 := by
  have _ : T1Space ((𝓡∂ 1).boundary M) := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin 0)) _
  rw [halfSpaceBoundaryVolume_zero_eq_count, Measure.count_singleton' (measurableSet_singleton x)]

end ZeroDimBoundary

end TauCeti
