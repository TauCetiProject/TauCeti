/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Boundary and interior of a closed interval

For `a < b`, a point of the manifold `[a, b]` is a boundary point exactly when it is one of the
two endpoints (`TauCeti.Icc_isBoundaryPoint_iff`), and an interior point exactly when it lies
strictly between them (`TauCeti.Icc_isInteriorPoint_iff`).

Boundary constructions on an `(n + 1)`-dimensional manifold, such as boundary defining functions,
specialize at `n = 0` to the model `𝓡∂ (0 + 1)`. Mathlib's interval charts are stated for the model
`𝓡∂ 1`, which instance search does not identify with `𝓡∂ (0 + 1)`, so this file also provides the
same charts and manifold structure at the model dimension `0 + 1`
(`TauCeti.instChartedSpaceIccZeroAddOne`, `TauCeti.instIsManifoldIccZeroAddOne`). For these charts
the manifold boundary of the unit interval is `{0, 1}` (`TauCeti.boundary_unitInterval`).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {a b : ℝ} [Fact (a < b)]

/-- The interval charts of `[a, b]`, with the model dimension written as the successor `0 + 1`
used by boundary constructions on `(n + 1)`-dimensional manifolds. -/
instance instChartedSpaceIccZeroAddOne : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc a b) :=
  instIccChartedSpace a b

/-- The interval `[a, b]` is an analytic manifold for the charts
`instChartedSpaceIccZeroAddOne`. -/
instance instIsManifoldIccZeroAddOne {k : ℕ∞ω} : IsManifold (𝓡∂ (0 + 1)) k (Icc a b) :=
  instIsManifoldIcc a b

/-- The manifold boundary of the unit interval `[0, 1]`, for its interval charts at the model
dimension `0 + 1` (`TauCeti.instChartedSpaceIccZeroAddOne`), is `{0, 1}`. -/
theorem boundary_unitInterval : (𝓡∂ (0 + 1)).boundary unitInterval = {0, 1} :=
  boundary_Icc

/-- A point of `[a, b]` is a manifold boundary point exactly when it is one of the endpoints. -/
@[simp]
theorem Icc_isBoundaryPoint_iff (x : Icc a b) :
    (𝓡∂ 1).IsBoundaryPoint x ↔ (x : ℝ) = a ∨ (x : ℝ) = b :=
  (Set.ext_iff.1 boundary_Icc x).trans <| by simp [Subtype.ext_iff]

/-- A point of `[a, b]` is a manifold interior point exactly when it lies strictly between the
endpoints. -/
@[simp]
theorem Icc_isInteriorPoint_iff (x : Icc a b) :
    (𝓡∂ 1).IsInteriorPoint x ↔ a < (x : ℝ) ∧ (x : ℝ) < b := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, Icc_isBoundaryPoint_iff]
  obtain ⟨ha, hb⟩ := x.property
  constructor
  · intro h
    push Not at h
    exact ⟨ha.lt_of_ne' h.1, hb.lt_of_ne h.2⟩
  · rintro ⟨ha', hb'⟩ (h | h) <;> linarith

end TauCeti
