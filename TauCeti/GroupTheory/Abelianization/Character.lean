/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Extending characters through a group homomorphism

A character on the source of a group homomorphism extends to its target exactly when it
kills the inverse image of the target's commutator subgroup, provided the target has finite
abelianization and the coefficient monoid has enough roots of unity for that abelianization.
For subgroup inclusions, this says that a character extends precisely when it kills the
intersection with the ambient commutator subgroup.

This combines the universal property of abelianization with Mathlib's extension theorem for
characters of subgroups of finite abelian groups. It is useful for describing the kernel of
character transgression for central extensions.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapter 2.
-/

public section

namespace MonoidHom

variable {B E R : Type*} [Group B] [Group E] [CommMonoid R]
  [Finite (Abelianization E)] [HasEnoughRootsOfUnity R (Monoid.exponent (Abelianization E))]

/-- A character extends along a group homomorphism exactly when it kills the inverse image
of the target's commutator subgroup. Only the target's abelianization needs to be finite. -/
theorem exists_comp_eq_iff_comap_commutator_le_ker (f : B →* E) (χ : B →* Rˣ) :
    (∃ ψ : E →* Rˣ, ψ.comp f = χ) ↔ (commutator E).comap f ≤ χ.ker := by
  constructor
  · rintro ⟨ψ, rfl⟩ x hx
    exact Abelianization.commutator_subset_ker ψ hx
  · intro hχ
    let q := (Abelianization.of.comp f).rangeRestrict
    have hq : q.ker ≤ χ.ker := by
      simpa only [q, ker_rangeRestrict, ← comap_ker, Abelianization.ker_of] using hχ
    obtain ⟨ψ, hψ⟩ := domRestrict_surjective (M := R) _
      (q.liftOfSurjective (Abelianization.of.comp f).rangeRestrict_surjective ⟨χ, hq⟩)
    refine ⟨ψ.comp Abelianization.of, MonoidHom.ext fun b ↦ ?_⟩
    simpa [q] using DFunLike.congr_fun hψ (q b)

end MonoidHom
