/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Order.Hereditary

/-!
# Direct `SMul` instance and order-hereditary nonunital `⋆`-subalgebras

Mathlib defines `NonUnitalStarSubalgebra.instModule` at default priority while leaving the direct
`SMul R S` instance to `SetLike.smul` at priority `50`. Consequently, synthesizing `SMul R S`
directly (as `StarAlgEquiv` does) traverses the module and action hierarchy instead of resolving on
`NonUnitalStarSubalgebra` immediately, which can time out on operator algebras over submodules. We
register `NonUnitalStarSubalgebra.instSMul := SetLike.smul S` at default priority, definitionally
equal to `S.instModule.toSMul`.

This file also provides lattice closure properties of order heredity (`TauCeti.IsHereditary`) for
`NonUnitalStarSubalgebra`: `⊤` and `⊥` are hereditary, and the infimum `B₁ ⊓ B₂` of two hereditary
nonunital `⋆`-subalgebras is hereditary.
-/

public section

namespace NonUnitalStarSubalgebra

/-- Direct `R`-scalar action on the carrier of a `NonUnitalStarSubalgebra R A`, definitionally equal
to `S.instModule.toSMul`. -/
instance instSMul {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : SMul R S :=
  SetLike.smul S

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
