/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Finite dimensionality of spaces of continuous alternating maps

Over a field, the continuous alternating maps in finitely many arguments between
finite-dimensional spaces form a finite-dimensional space: forgetting continuity and the
alternating property embeds them linearly into the multilinear maps, which are
finite-dimensional by `Module.Finite.multilinearMap`. For instance, the covectors
`E [⋀^Fin 1]→L[𝕜] 𝕜` of a finite-dimensional space form a finite-dimensional space.

## Main declarations

* `ContinuousAlternatingMap.instFiniteDimensional`: continuous alternating maps in finitely many
  arguments between finite-dimensional spaces form a finite-dimensional space.
-/

public section

namespace ContinuousAlternatingMap

/-- Continuous alternating maps in finitely many arguments between finite-dimensional spaces form
a finite-dimensional space. -/
instance instFiniteDimensional {𝕜 E F ι : Type*} [Field 𝕜] [Finite ι]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→L[𝕜] F) :=
  Module.Finite.of_injective
    (AlternatingMap.toMultilinearMapLM ∘ₗ toAlternatingMapLinear (R := 𝕜))
    (AlternatingMap.coe_multilinearMap_injective.comp toAlternatingMap_injective)

end ContinuousAlternatingMap
