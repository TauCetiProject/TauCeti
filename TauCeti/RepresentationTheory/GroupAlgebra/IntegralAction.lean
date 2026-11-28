/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsAlgebraHom

/-!
# Integral action of a monoid algebra

In a linear representation, a monoid algebra element acts by a linear combination of
translates. If the translates on its support lie in a submodule over a smaller scalar
semiring, and the coefficients lie in that semiring, then the result lies in the smaller
submodule. No stability under the other monoid elements is needed.
-/

public section

namespace Representation

/-- The action of an element of the monoid algebra lands in `L` if each translate on its
support belongs to `L` and the corresponding coefficient lies in the scalar subsemiring `S`. -/
theorem asAlgebraHom_mem_of_coeff_mem {A G V : Type*} [CommSemiring A] [Monoid G]
    [AddCommMonoid V] [Module A V] (ρ : Representation A G V) {S : Subsemiring A}
    (L : Submodule S V) {a : MonoidAlgebra A G} {v : V}
    (ha : ∀ g ∈ a.coeff.support, a.coeff g ∈ S)
    (hv : ∀ g ∈ a.coeff.support, ρ g v ∈ L) : ρ.asAlgebraHom a v ∈ L := by
  rw [ρ.asAlgebraHom_apply]
  exact L.sum_mem fun g hg ↦ L.smul_mem (⟨a.coeff g, ha g hg⟩ : S) (hv g hg)

end Representation
