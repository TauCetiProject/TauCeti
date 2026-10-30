/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Composition of submodule inclusions

The inclusion maps `Submodule.inclusion` between nested submodules compose along the composite
inequality (`Submodule.inclusion_comp_inclusion`), as `Set.inclusion_comp_inclusion` does for sets.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Composing two inclusions of submodules gives the inclusion along the composite inequality. -/
@[simp]
theorem inclusion_comp_inclusion {p q r : Submodule R M} (h : p ≤ q) (h' : q ≤ r) :
    inclusion h' ∘ₗ inclusion h = inclusion (h.trans h') :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

end Submodule
