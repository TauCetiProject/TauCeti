/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Integral linearity of nonunital ring homomorphisms

`NonUnitalRingHom.toIntNonUnitalAlgHom` regards a homomorphism of nonunital,
nonassociative rings as a homomorphism of nonunital `ℤ`-algebras, using their canonical
integer scalar actions.
-/

public section

namespace NonUnitalRingHom

variable {R A : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing A]

/-- Reinterpret a nonunital ring homomorphism as a nonunital `ℤ`-algebra homomorphism. -/
def toIntNonUnitalAlgHom (f : R →ₙ+* A) : R →ₙₐ[ℤ] A :=
  { f with map_smul' := fun z x ↦ f.map_zsmul z x }

@[simp]
theorem toIntNonUnitalAlgHom_apply (f : R →ₙ+* A) (x : R) :
    f.toIntNonUnitalAlgHom x = f x := by
  rfl

end NonUnitalRingHom
