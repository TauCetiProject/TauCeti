/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Restricting operators to a range

Equality after restriction to the range of a continuous linear map is equivalent to equality
after precomposition with that map. This identifies derivatives on parametrized tangent planes.
-/

public section

namespace ContinuousLinearMap

/-- Two operators agree on the range of `T` exactly when their composites with `T` agree. -/
theorem comp_subtypeL_range_eq_iff
    {R E G F : Type*} [Semiring R]
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    [TopologicalSpace G] [AddCommMonoid G] [Module R G]
    [TopologicalSpace F] [AddCommMonoid F] [Module R F]
    (T : E →L[R] G) (M₁ M₂ : G →L[R] F) :
    M₁.comp T.range.subtypeL = M₂.comp T.range.subtypeL ↔ M₁.comp T = M₂.comp T := by
  constructor
  · intro h
    ext x
    exact congrArg (fun D => D ⟨T x, LinearMap.mem_range_self _ x⟩) h
  · intro h
    ext ⟨v, hv⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
    exact congrArg (fun D => D x) h

end ContinuousLinearMap
