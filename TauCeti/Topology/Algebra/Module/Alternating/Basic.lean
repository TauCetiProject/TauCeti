/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Continuous alternating pullback and the underlying multilinear map

The underlying continuous multilinear map of an alternating pullback is the
multilinear pullback. This identity allows consumers to move between the two APIs
without unfolding their implementations.
-/

public section

namespace TauCeti

/-- Taking the underlying multilinear map commutes with continuous linear pullback. -/
@[simp] theorem _root_.ContinuousAlternatingMap.toContinuousMultilinearMap_compContinuousLinearMap
    {R E F G ι : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    (φ : F [⋀^ι]→L[R] G) (f : E →L[R] F) :
    (φ.compContinuousLinearMap f).toContinuousMultilinearMap =
      φ.toContinuousMultilinearMap.compContinuousLinearMap (fun _ ↦ f) := (rfl)

end TauCeti
