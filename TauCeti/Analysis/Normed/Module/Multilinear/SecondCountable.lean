/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Second countability of spaces of continuous multilinear maps

Over a complete field, continuous multilinear maps in `m` variables from a finite-dimensional
normed space into a second-countable normed space form a second-countable space for the operator
norm. This is the multilinear companion of Mathlib's instance for continuous linear maps
`E →L[𝕜] F`, from which it follows by currying one variable at a time
(`continuousMultilinearCurryLeftEquiv`).

These spaces hold the iterated derivatives of maps out of a finite-dimensional space, so the
instance is what makes spaces of jets, and hence spaces of `C^k` maps on a σ-compact manifold,
second countable.
-/

public section

open TopologicalSpace

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SecondCountableTopology F]

/-- Continuous multilinear maps in `m` variables from a finite-dimensional normed space into a
second-countable normed space form a second-countable space. -/
instance ContinuousMultilinearMap.instSecondCountableTopologyFin (m : ℕ) :
    SecondCountableTopology (E [×m]→L[𝕜] F) := by
  induction m with
  | zero => exact (continuousMultilinearCurryFin0 𝕜 E F).toHomeomorph.secondCountableTopology
  | succ m ih =>
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ E) F).toHomeomorph
      |>.secondCountableTopology
