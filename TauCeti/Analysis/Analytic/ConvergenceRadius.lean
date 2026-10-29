/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius

/-! # Partial sums and continuous linear maps

Taking partial sums of a formal multilinear series commutes with continuous linear maps.
This allows coefficientwise linear operations to pass through finite approximations.
-/

public section

variable {𝕜 E F G : Type*} [Semiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]
  [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]

/-- A partial sum of the composed series is the image of the original partial sum. -/
@[simp]
theorem ContinuousLinearMap.compFormalMultilinearSeries_partialSum (f : F →L[𝕜] G)
    (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) :
    (f.compFormalMultilinearSeries p).partialSum n x = f (p.partialSum n x) := by
  simp [FormalMultilinearSeries.partialSum]
