/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Closedness and completeness of projected subspaces

A submodule `U` of an inner product space admitting an orthogonal projection is closed, with no
completeness hypothesis on the ambient space, because it is its own double orthogonal complement
`Uᗮᗮ`. When the ambient space is complete, `U` is therefore complete. This is a converse of
Mathlib's `HasOrthogonalProjection.ofCompleteSpace`.

## Main results

* `Submodule.isClosed_of_hasOrthogonalProjection`: a submodule admitting an orthogonal projection
  is closed.
* `Submodule.isComplete_coe_of_hasOrthogonalProjection`: in a complete space, a submodule admitting
  an orthogonal projection is a complete subset.
* `Submodule.completeSpace_of_hasOrthogonalProjection`: in a complete space, a submodule admitting
  an orthogonal projection is complete in its induced norm. This is a theorem rather than an
  instance, since an instance would form a cycle with `HasOrthogonalProjection.ofCompleteSpace`.
-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- A submodule admitting an orthogonal projection is closed: it is its own double orthogonal
complement. -/
theorem isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsClosed (U : Set E) := by
  rw [← U.orthogonal_orthogonal]
  exact Uᗮ.isClosed_orthogonal

/-- In a complete space, a submodule admitting an orthogonal projection is a complete subset. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsComplete (U : Set E) :=
  U.isClosed_of_hasOrthogonalProjection.isComplete

/-- In a complete space, a submodule admitting an orthogonal projection is complete in its
induced norm. -/
theorem completeSpace_of_hasOrthogonalProjection [CompleteSpace E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : CompleteSpace U :=
  U.isComplete_coe_of_hasOrthogonalProjection.completeSpace_coe

end Submodule
