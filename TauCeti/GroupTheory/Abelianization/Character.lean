/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import TauCeti.GroupTheory.FiniteAbelian.Duality

/-!
# Extending characters through a group homomorphism

A character extends along any group homomorphism exactly when it kills the inverse image of the
target's commutator subgroup, provided the target has finite abelianization and the coefficient
monoid has enough roots of unity for that abelianization. For subgroup inclusions, this says that
a character extends precisely when it kills the intersection with the ambient commutator
subgroup. This follows by applying `MonoidHom.exists_comp_eq_iff_ker_le_ker`, the extension
criterion along a homomorphism into a finite commutative group, to the composite with the
abelianization map. It is useful for describing the kernel of character transgression for
central extensions.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapter 2.
-/

public section

namespace MonoidHom

variable {B E R : Type*} [Group B] [CommMonoid R] [Group E] [Finite (Group.Abelianization E)]
  [HasEnoughRootsOfUnity R (Monoid.exponent (Group.Abelianization E))]

/-- A character extends along a group homomorphism exactly when it kills the inverse image
of the target's commutator subgroup. Only the target's abelianization needs to be finite. -/
theorem exists_comp_eq_iff_comap_commutator_le_ker (f : B →* E) (χ : B →* Rˣ) :
    (∃ ψ : E →* Rˣ, ψ.comp f = χ) ↔ (commutator E).comap f ≤ χ.ker := by
  constructor
  · rintro ⟨ψ, rfl⟩ x hx
    exact Group.Abelianization.commutator_le_ker ψ hx
  · intro hχ
    obtain ⟨ψ, hψ⟩ := (exists_comp_eq_iff_ker_le_ker (Group.Abelianization.of.comp f) χ).mpr
      (by rwa [← comap_ker, Group.Abelianization.ker_of])
    exact ⟨ψ.comp Group.Abelianization.of, hψ⟩

end MonoidHom
