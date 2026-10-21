/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Cochain

/-!
# Low-degree Lie algebra cochains

Complements to Mathlib's low-degree cochain complex `LieModule.Cohomology` of a Lie algebra `L`
with values in an `L`-module `M`.

* `LieModule.Cohomology.range_d₁₂_le_twoCocycle`: every coboundary is a 2-cocycle.
-/

public section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieModule.Cohomology

/-- Every coboundary is a 2-cocycle. -/
lemma range_d₁₂_le_twoCocycle : LinearMap.range (d₁₂ R L M) ≤ twoCocycle R L M := by
  rintro _ ⟨f, rfl⟩
  rw [mem_twoCocycle_iff, ← LinearMap.comp_apply, d₂₃_comp_d₁₂, LinearMap.zero_apply]

end LieModule.Cohomology
