/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Underlying multilinear maps and continuous alternatization

The underlying continuous multilinear map of an alternating pullback is the
multilinear pullback. This identity allows consumers to move between the two APIs
without unfolding their implementations. Alternatization multiplies an already alternating map
by the arity factorial, which supplies the retraction used to transfer smoothness from multilinear
maps when the factorial is invertible.
-/

public section

namespace ContinuousAlternatingMap

/-- Taking the underlying multilinear map commutes with continuous linear pullback. -/
@[simp] theorem toContinuousMultilinearMap_compContinuousLinearMap
    {R E F G ι : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    (φ : F [⋀^ι]→L[R] G) (f : E →L[R] F) :
    (φ.compContinuousLinearMap f).toContinuousMultilinearMap =
      φ.toContinuousMultilinearMap.compContinuousLinearMap (fun _ ↦ f) := (rfl)

/-- Alternatization multiplies an alternating map by the factorial of its arity. -/
@[simp] theorem alternatization_toContinuousMultilinearMap
    {R E F ι : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Fintype ι] [DecidableEq ι] (f : E [⋀^ι]→L[R] F) :
    ContinuousMultilinearMap.alternatization f.toContinuousMultilinearMap =
      (Fintype.card ι).factorial • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simp only [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  exact AlternatingMap.coe_alternatization f.toAlternatingMap

end ContinuousAlternatingMap
