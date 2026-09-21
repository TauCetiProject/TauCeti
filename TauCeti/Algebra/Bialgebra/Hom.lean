/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Ring homomorphisms underlying bialgebra morphisms

`BialgHom.id_toRingHom` identifies the direct ring-homomorphism coercion of the identity.
It complements Mathlib's `BialgHom.id_toAlgHom`, which concerns the algebra-homomorphism
coercion.
-/

public section

namespace BialgHom

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [CoalgebraStruct R A]

/-- The ring homomorphism underlying the identity bialgebra morphism is the identity. -/
@[simp]
theorem id_toRingHom : (BialgHom.id R A : A →+* A) = RingHom.id A := rfl

end BialgHom
