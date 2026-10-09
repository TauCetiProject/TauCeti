/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Subspaces admitting an orthogonal projection are closed

Mathlib asks for an orthogonal projection onto a subspace `U` of an inner product space through
the class `Submodule.HasOrthogonalProjection`, and provides it for every complete subspace
(`Submodule.HasOrthogonalProjection.ofCompleteSpace`). This file proves the converse: a subspace
admitting an orthogonal projection satisfies `Uᗮᗮ = U`, so it is closed, being an orthogonal
complement. Hence, inside a complete space, it is complete in its induced norm, and the three
conditions *has an orthogonal projection*, *is closed* and *is complete* coincide.

Completeness of `U` is what makes `U` a Hilbert space in its own right, so that operators
restricted to it have adjoints and a spectral theory; the theorems below supply it from the
`HasOrthogonalProjection` instance that a statement involving `U.starProjection` already carries.
`Submodule.completeSpace_coe_of_hasOrthogonalProjection` is deliberately not an instance: together
with `Submodule.HasOrthogonalProjection.ofCompleteSpace` it would make instance search loop.

## Main statements

* `Submodule.isClosed_of_hasOrthogonalProjection`: a subspace with an orthogonal projection is
  closed, in any inner product space.
* `Submodule.isComplete_coe_of_hasOrthogonalProjection`,
  `Submodule.completeSpace_coe_of_hasOrthogonalProjection`: in a complete space it is complete.
* `Submodule.hasOrthogonalProjection_iff_isClosed`,
  `Submodule.hasOrthogonalProjection_iff_completeSpace`: in a complete space, a subspace has an
  orthogonal projection exactly when it is closed, and exactly when it is complete.

## Source

`Submodule.isComplete_coe_of_hasOrthogonalProjection` also appears in
`ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean` of the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace admitting an orthogonal projection is closed: it is the orthogonal complement of
its orthogonal complement. No completeness of the ambient space is needed. -/
theorem isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsClosed (U : Set E) := by
  simpa only [orthogonal_orthogonal] using Uᗮ.isClosed_orthogonal

variable [CompleteSpace E]

/-- In a complete space, a subspace admitting an orthogonal projection is complete in its induced
norm. -/
theorem isComplete_coe_of_hasOrthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsComplete (U : Set E) :=
  U.isClosed_of_hasOrthogonalProjection.isComplete

/-- In a complete space, a subspace admitting an orthogonal projection is a complete space.

This is not an instance, since `HasOrthogonalProjection.ofCompleteSpace` goes the other way. -/
theorem completeSpace_coe_of_hasOrthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : CompleteSpace U :=
  U.isComplete_coe_of_hasOrthogonalProjection.completeSpace_coe

/-- In a complete space, a subspace has an orthogonal projection exactly when it is closed. -/
theorem hasOrthogonalProjection_iff_isClosed {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ IsClosed (U : Set E) :=
  ⟨fun _ ↦ U.isClosed_of_hasOrthogonalProjection, fun h ↦
    have := h.isComplete.completeSpace_coe
    .ofCompleteSpace U⟩

/-- In a complete space, a subspace has an orthogonal projection exactly when it is complete. -/
theorem hasOrthogonalProjection_iff_completeSpace {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ CompleteSpace U :=
  ⟨fun _ ↦ U.completeSpace_coe_of_hasOrthogonalProjection, fun _ ↦ .ofCompleteSpace U⟩

end Submodule
