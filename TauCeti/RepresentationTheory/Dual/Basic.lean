/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Restricting the dual representation

The dual `ρ.dual` of a representation acts on functionals by `ψ ↦ ψ ∘ ρ g⁻¹`. Restricting a
representation along a group homomorphism `f : H →* G` and then dualizing gives the restriction of
the dual along `f` (`Representation.dual_comp`). This law needs only Mathlib's definition of the
dual representation; the invariants of the dual are in `TauCeti.RepresentationTheory.Dual`.
-/

public section

namespace Representation

/-- The dual of a representation restricted along `f` is the restriction of the dual along `f`. -/
@[simp]
theorem dual_comp {R G H V : Type*} [CommSemiring R] [Group G] [Group H] [AddCommMonoid V]
    [Module R V] (ρ : Representation R G V) (f : H →* G) :
    dual (ρ.comp f) = ρ.dual.comp f := by
  ext
  simp

end Representation
