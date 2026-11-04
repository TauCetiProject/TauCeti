/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# The inclusion of an open subset as a `C^n` map

An open subset `U` of a manifold `M` is a manifold with the restricted charts, and its inclusion
`U → M` is `C^n` for every `n` (`contMDiff_subtype_val`). This file bundles the inclusion as an
element of `C^n⟮I, U; I, M⟯`, the smooth analogue of `ContinuousMap.subtypeVal`. Precomposing with
it restricts maps to `U`, and pulling back along it restricts bundles and their sections to `U`.
-/

public section

open TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

variable (I n) in
/-- The inclusion `U → M` of an open subset, as a `C^n` map. -/
-- Exposed so that the fibre `(subtypeVal I n U *ᵖ V) x` of a pulled-back bundle is recognised as
-- `V x`: the fibre type depends on this map definitionally, which no lemma can rewrite.
@[expose]
def subtypeVal (U : Opens M) : C^n⟮I, U; I, M⟯ :=
  ⟨Subtype.val, contMDiff_subtype_val⟩

@[simp]
theorem coe_subtypeVal (U : Opens M) : ⇑(subtypeVal I n U) = Subtype.val :=
  (rfl)

theorem subtypeVal_apply (U : Opens M) (x : U) : subtypeVal I n U x = x :=
  (rfl)

end ContMDiffMap
