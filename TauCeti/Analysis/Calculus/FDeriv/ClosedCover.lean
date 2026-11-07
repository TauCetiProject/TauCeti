/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Derivatives from a cover by two closed sets

A map that has the same derivative within each of two closed sets covering the space, at those
of them that contain a point, has that derivative at the point: a derivative within a closed set
not containing the point holds vacuously, and Mathlib's `HasFDerivWithinAt.union` combines the
two pieces. This glues maps defined by cases on closed pieces, such as the two closed half-planes
on either side of a line (`TauCeti.Analysis.Complex.EvenReflection`).

The continuity counterpart is `TauCeti.continuousAt_of_isClosed_of_union_eq_univ`.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {f : E → F} {f' : E →L[𝕜] F} {s t : Set E} {x : E}

/-- A map with derivative `f'` within each of two closed sets covering the space, at those of
them that contain `x`, has derivative `f'` at `x`. -/
theorem hasFDerivAt_of_isClosed_of_union_eq_univ (hs : IsClosed s) (ht : IsClosed t)
    (hst : s ∪ t = univ) (h₁ : x ∈ s → HasFDerivWithinAt f f' s x)
    (h₂ : x ∈ t → HasFDerivWithinAt f f' t x) : HasFDerivAt f f' x := by
  have hs' : HasFDerivWithinAt f f' s x := by
    by_cases hx : x ∈ s
    · exact h₁ hx
    · exact .of_notMem_closure (by rwa [hs.closure_eq])
  have ht' : HasFDerivWithinAt f f' t x := by
    by_cases hx : x ∈ t
    · exact h₂ hx
    · exact .of_notMem_closure (by rwa [ht.closure_eq])
  rw [← hasFDerivWithinAt_univ, ← hst]
  exact hs'.union ht'

end TauCeti
