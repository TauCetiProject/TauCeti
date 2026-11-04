/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# The inclusion of an open subset as a bundled smooth map

The inclusion `U → M` of an open subset of a manifold, with its induced manifold structure, is a
bundled `C^n` map `ContMDiffMap.subtypeVal U`, the smooth analogue of
`ContinuousMap.subtypeVal`. Precomposition with it restricts smooth functions to `U`, and
pulling a bundle back along it gives the restricted bundle over `U`, whose instances are stated
for bundled maps.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

-- The body is exposed so that the fibre of the restricted bundle `subtypeVal U *ᵖ V` over
-- `x : U` reduces to the fibre `V x`.
/-- The inclusion of an open subset `U` of `M` as a bundled `C^n` map. -/
@[expose] def subtypeVal (U : Opens M) : C^n⟮I, U; I, M⟯ :=
  ⟨Subtype.val, contMDiff_subtype_val⟩

@[simp]
theorem coe_subtypeVal (U : Opens M) : ⇑(subtypeVal U : C^n⟮I, U; I, M⟯) = Subtype.val :=
  (rfl)

end ContMDiffMap
