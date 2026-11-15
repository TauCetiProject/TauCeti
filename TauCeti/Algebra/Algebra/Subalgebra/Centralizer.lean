/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Centralizers under algebra isomorphisms

An algebra isomorphism `e : A ≃ₐ[R] B` carries the centralizer of a set `s ⊆ A` onto the
centralizer of its image `e '' s` (`AlgEquiv.map_centralizer`). Together with
`AlgEquiv.subalgebraMap`, this transports centralizers, and in particular their dimensions,
between isomorphic algebras such as matrices and endomorphisms.
-/

public section

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- **Transport of centralizers.** An algebra isomorphism carries the centralizer of a set onto
the centralizer of its image. -/
theorem map_centralizer (e : A ≃ₐ[R] B) (s : Set A) :
    (Subalgebra.centralizer R s).map (e : A →ₐ[R] B) = Subalgebra.centralizer R (e '' s) := by
  ext b
  simp only [Subalgebra.mem_map, Subalgebra.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩ x hx
    simp [← map_mul, ha x hx]
  · intro h
    exact ⟨e.symm b, fun x hx => e.injective (by simpa using h hx), by simp⟩

end AlgEquiv
