/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Continuity from a cover by two closed sets

A map that is continuous within each of two closed sets covering the space, at those of them
that contain a point, is continuous at that point: continuity within a closed set not containing
the point holds vacuously. This glues maps defined by cases on closed pieces, such as the two
closed half-planes on either side of a line
(`TauCeti.Analysis.Complex.EvenReflection`).

The derivative counterpart is `TauCeti.hasFDerivAt_of_isClosed_of_union_eq_univ`.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s t : Set X}
  {x : X}

/-- A map continuous within each of two closed sets covering the space, at those of them that
contain `x`, is continuous at `x`. -/
theorem continuousAt_of_isClosed_of_union_eq_univ (hs : IsClosed s) (ht : IsClosed t)
    (hst : s ∪ t = univ) (h₁ : x ∈ s → ContinuousWithinAt f s x)
    (h₂ : x ∈ t → ContinuousWithinAt f t x) : ContinuousAt f x := by
  have hs' : ContinuousWithinAt f s x := by
    by_cases hx : x ∈ s
    · exact h₁ hx
    · exact continuousWithinAt_of_notMem_closure (by rwa [hs.closure_eq])
  have ht' : ContinuousWithinAt f t x := by
    by_cases hx : x ∈ t
    · exact h₂ hx
    · exact continuousWithinAt_of_notMem_closure (by rwa [ht.closure_eq])
  rw [← continuousWithinAt_univ, ← hst]
  exact hs'.union ht'

end TauCeti
