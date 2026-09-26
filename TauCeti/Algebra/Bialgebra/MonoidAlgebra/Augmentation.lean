/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# The monoid-algebra counit is the coefficient sum

This identifies the bialgebra counit with the augmentation used in the ideal-theoretic
exactness of monoid algebras.
-/

public section

namespace TauCeti.MonoidAlgebra

/-- The counit of a monoid algebra over its coefficient ring is its coefficient-sum
augmentation. -/
@[simp]
theorem counitAlgHom_toRingHom (R M : Type*) [CommRing R] [Monoid M] :
    (Bialgebra.counitAlgHom R (MonoidAlgebra R M) : MonoidAlgebra R M →+* R) =
      augmentation R M := by
  apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

end TauCeti.MonoidAlgebra
