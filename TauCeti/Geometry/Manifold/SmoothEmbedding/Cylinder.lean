/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# The ends of a cylinder

For a manifold `Y` modelled on `I`, the cylinder `Y × [a, b]` is a manifold modelled on
`I.prod (𝓡∂ 1)`. This file packages its bottom and top slices `y ↦ (y, a)` and `y ↦ (y, b)` as
bundled smooth embeddings, and identifies their underlying continuous maps with the slice homotopy
equivalences `Y ≃ₕ Y × [a, b]`.

## Main definitions

* `TauCeti.SmoothEmbedding.cylinderBot`, `TauCeti.SmoothEmbedding.cylinderTop`: the inclusions
  `y ↦ (y, a)` and `y ↦ (y, b)` of a manifold as the ends of the cylinder `Y × [a, b]`.

## Main results

* `TauCeti.SmoothEmbedding.toContinuousMap_cylinderBot`,
  `TauCeti.SmoothEmbedding.toContinuousMap_cylinderTop`: the ends are the slice homotopy
  equivalences `ContinuousMap.HomotopyEquiv.prodIcc` at `a` and `b`.
-/

public section

noncomputable section

open Manifold Set Fact.Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
  (a b : ℝ) [Fact (a < b)] (Y : Type*) [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I n Y]

/-- The inclusion `y ↦ (y, a)` of a manifold as the bottom end of the cylinder `Y × [a, b]`. -/
def SmoothEmbedding.cylinderBot : SmoothEmbedding I (I.prod (𝓡∂ 1)) n Y (Y × Icc a b) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero extChartAt_Icc_bot)

/-- The inclusion `y ↦ (y, b)` of a manifold as the top end of the cylinder `Y × [a, b]`. -/
def SmoothEmbedding.cylinderTop : SmoothEmbedding I (I.prod (𝓡∂ 1)) n Y (Y × Icc a b) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero extChartAt_Icc_top)

variable {I n a b Y}

/-- The bottom end of a cylinder sends `y` to `(y, a)`. -/
@[simp]
theorem SmoothEmbedding.cylinderBot_apply (y : Y) :
    SmoothEmbedding.cylinderBot I n a b Y y = (y, ⊥) := by
  simp [SmoothEmbedding.cylinderBot]

/-- The top end of a cylinder sends `y` to `(y, b)`. -/
@[simp]
theorem SmoothEmbedding.cylinderTop_apply (y : Y) :
    SmoothEmbedding.cylinderTop I n a b Y y = (y, ⊤) := by
  simp [SmoothEmbedding.cylinderTop]

/-- The bottom end of a cylinder is the slice homotopy equivalence `Y ≃ₕ Y × [a, b]` at `a`. -/
theorem SmoothEmbedding.toContinuousMap_cylinderBot :
    (SmoothEmbedding.cylinderBot I n a b Y).toContinuousMap =
      (ContinuousMap.HomotopyEquiv.prodIcc ⊥).toFun := by
  ext1 y
  simp

/-- The top end of a cylinder is the slice homotopy equivalence `Y ≃ₕ Y × [a, b]` at `b`. -/
theorem SmoothEmbedding.toContinuousMap_cylinderTop :
    (SmoothEmbedding.cylinderTop I n a b Y).toContinuousMap =
      (ContinuousMap.HomotopyEquiv.prodIcc ⊤).toFun := by
  ext1 y
  simp

end TauCeti
