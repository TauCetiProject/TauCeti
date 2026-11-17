/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Order.Hereditary

/-!
# Order-hereditary nonunital `⋆`-subalgebras

This file provides lattice closure properties of order heredity (`TauCeti.IsHereditary`) for
`NonUnitalStarSubalgebra`: `⊤` and `⊥` are hereditary, and the infimum `B₁ ⊓ B₂` of two hereditary
nonunital `⋆`-subalgebras is hereditary.
-/

public section

namespace NonUnitalStarSubalgebra

open TauCeti

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

/-- The top nonunital `⋆`-subalgebra is hereditary. -/
@[simp]
theorem isHereditary_top [LE A] : IsHereditary (⊤ : NonUnitalStarSubalgebra R A) :=
  isHereditary_def.mpr fun _ _ _ _ _ => trivial

/-- The bottom nonunital `⋆`-subalgebra is hereditary in any partially ordered ambient type. -/
@[simp]
theorem isHereditary_bot [PartialOrder A] : IsHereditary (⊥ : NonUnitalStarSubalgebra R A) := by
  rw [isHereditary_def]
  intro a b ha hab hb
  rw [NonUnitalStarAlgebra.mem_bot] at hb ⊢
  exact le_antisymm (hab.trans_eq hb) ha

/-- The intersection of two hereditary nonunital `⋆`-subalgebras is hereditary. -/
theorem isHereditary_inf [LE A] {B₁ B₂ : NonUnitalStarSubalgebra R A}
    (h₁ : IsHereditary B₁) (h₂ : IsHereditary B₂) : IsHereditary (B₁ ⊓ B₂) :=
  isHereditary_def.mpr fun _ _ ha hab hb => ⟨h₁.mem_of_le ha hab hb.1, h₂.mem_of_le ha hab hb.2⟩

end NonUnitalStarSubalgebra
