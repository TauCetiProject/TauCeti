/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# Universe-lifting recharting onto Euclidean space
Recharts a manifold `M : Type w` modelled on a finite-dimensional real normed space `E : Type v`
onto `EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E))) : Type w` via `Homeomorph.chartedSpace` and
`ChartedSpace.comp`, decoupling model-space and manifold universes in local homology and
fundamental-class results.
-/
public noncomputable section
open Module
universe w v
namespace TauCeti
/-- The Euclidean model space in `Type w` of the same real dimension as `E : Type v`. -/
abbrev EuclideanModel (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E)))
/-- `TauCeti.EuclideanModel.{w} E` has real dimension `finrank ℝ E`. -/
theorem finrank_euclideanModel (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    finrank ℝ (EuclideanModel.{w} E) = finrank ℝ E := by
  rw [finrank_euclideanSpace, Fintype.card_ulift, Fintype.card_fin]
/-- Rechart `M` modelled on `E : Type v` onto `TauCeti.EuclideanModel.{w} E : Type w`. -/
@[instance_reducible] def chartedSpaceEuclideanULift (M : Type*) (E : Type v) [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] :
    ChartedSpace (EuclideanModel.{w} E) M :=
  let e := (ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanModel.{w} E)).toHomeomorph
  letI : ChartedSpace (EuclideanModel.{w} E) E := e.chartedSpace
  ChartedSpace.comp (EuclideanModel.{w} E) E M
end TauCeti
