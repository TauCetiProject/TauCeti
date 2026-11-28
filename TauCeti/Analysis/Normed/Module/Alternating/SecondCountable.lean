/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Analysis.Normed.Module.Multilinear.SecondCountable

/-!
# Second countability of spaces of continuous alternating maps

If `E` is finite-dimensional over a complete field `𝕜`, `F` is second countable, and `ι` is
finite, then the space `E [⋀^ι]→L[𝕜] F` of continuous alternating maps is second countable. It
inherits second countability from `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F`
(`ContinuousMultilinearMap.secondCountableTopology`) via its isometric embedding
`ContinuousAlternatingMap.toContinuousMultilinearMapLI`.

## Main results

* `ContinuousAlternatingMap.secondCountableTopology`: the instance for finitely many copies of a
  finite-dimensional space over a complete field.
-/

public section

open Topology

namespace ContinuousAlternatingMap

/-- The continuous alternating maps on finitely many copies of a finite-dimensional space over a
complete field, with values in a second countable space, form a second countable space. -/
instance secondCountableTopology {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopology F] [Finite ι] :
    SecondCountableTopology (E [⋀^ι]→L[𝕜] F) := by
  classical
  have := Fintype.ofFinite ι
  exact (toContinuousMultilinearMapLI (𝕜 := 𝕜) (E := E) (F := F)
    (ι := ι)).isometry.isEmbedding.secondCountableTopology

end ContinuousAlternatingMap
