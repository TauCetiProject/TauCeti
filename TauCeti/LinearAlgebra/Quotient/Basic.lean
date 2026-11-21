/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Surjectivity of induced maps on quotient modules

A surjective linear map `f : M → M₂` sending `p` into `q` induces a surjective map
`M ⧸ p → M₂ ⧸ q`.
-/

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [Ring R₂] [AddCommGroup M₂]
  [Module R₂ M₂] {τ₁₂ : R →+* R₂} (p : Submodule R M) (q : Submodule R₂ M₂)

/-- Surjectivity of a linear map implies surjectivity of the map it induces on quotients. -/
theorem mapQ_surjective (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) (hf : Function.Surjective f) :
    Function.Surjective (p.mapQ q f h) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, rfl⟩

end Submodule
