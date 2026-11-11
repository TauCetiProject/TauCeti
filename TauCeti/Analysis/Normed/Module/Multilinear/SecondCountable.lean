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

If `E` is finite-dimensional over a complete field and `F` is second countable, then the space
of continuous multilinear maps from finitely many copies of `E` to `F` is second countable. For
continuous linear maps this is the Mathlib instance in
`Mathlib.Analysis.Normed.Module.FiniteDimension`; the multilinear case follows by currying one
variable at a time, since `E [×(m + 1)]→L[𝕜] F` is isometric to `E →L[𝕜] (E [×m]→L[𝕜] F)`.

These are the spaces in which the iterated derivatives of a map `E → F` take their values, so
this is what makes spaces of continuous derivative fields on second countable locally compact
sets second countable.

## Main results

* `ContinuousMultilinearMap.secondCountableTopology`: the instance for an arbitrary finite index
  type.
-/

public section

open Topology

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopology F]

/-- The continuous multilinear maps in `m` variables from a finite-dimensional space to a second
countable space form a second countable space. -/
private theorem secondCountableTopology_fin (m : ℕ) : SecondCountableTopology (E [×m]→L[𝕜] F) := by
  induction m with
  | zero => exact (continuousMultilinearCurryFin0 𝕜 E F).toHomeomorph.secondCountableTopology
  | succ m ih =>
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ E)
      F).toHomeomorph.secondCountableTopology

/-- The continuous multilinear maps on finitely many copies of a finite-dimensional space, with
values in a second countable space, form a second countable space. -/
instance secondCountableTopology {ι : Type*} [Finite ι] :
    SecondCountableTopology (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) := by
  have := Fintype.ofFinite ι
  have := secondCountableTopology_fin (𝕜 := 𝕜) (E := E) (F := F) (Fintype.card ι)
  exact (domDomCongrₗᵢ 𝕜 E F (Fintype.equivFin ι)).toHomeomorph.secondCountableTopology

end ContinuousMultilinearMap
