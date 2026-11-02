/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Ambiguity

/-!
# Torsion classes over group rings

The group-ring deck monomials give units in every algebra over the group ring.
`AddMonoidAlgebra.deckUnitsHom` supplies these units for the whole-ring torsion
quotient, independently of any Novikov completion. Equality of classes is precisely
multiplication by a signed group-ring monomial.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
-/

public section

noncomputable section

namespace AddMonoidAlgebra

variable (R : Type*) {H : Type*} [CommRing R] [AddCommGroup H]

/-- The group-ring deck monomials as units in an algebra over the group ring. -/
def deckUnitsHom (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] : Multiplicative H →* Q₀ˣ :=
  ((algebraMap (AddMonoidAlgebra R H) Q₀).toMonoidHom.comp
    (AddMonoidAlgebra.of R H)).toHomUnits

/-- The group-ring deck unit has the corresponding group-ring monomial as its value. -/
@[simp]
theorem coe_deckUnitsHom (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] (h : Multiplicative H) :
    (deckUnitsHom R (H := H) Q₀ h : Q₀) =
      algebraMap (AddMonoidAlgebra R H) Q₀ (AddMonoidAlgebra.single h.toAdd 1) := by
  simp [deckUnitsHom, AddMonoidAlgebra.of_apply]

/-- Equality in the group-ring torsion target is exactly signed deck-monomial ambiguity. -/
theorem torsionClass_mk_eq_mk_iff (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] {a b : Q₀} :
    TauCeti.TorsionClass.mk (deckUnitsHom R (H := H) Q₀) a =
      TauCeti.TorsionClass.mk (deckUnitsHom R (H := H) Q₀) b ↔
    ∃ h : H, a = algebraMap (AddMonoidAlgebra R H) Q₀ (AddMonoidAlgebra.single h 1) * b ∨
      a = -algebraMap (AddMonoidAlgebra R H) Q₀ (AddMonoidAlgebra.single h 1) * b := by
  simp only [TauCeti.TorsionClass.mk_eq_mk_iff, coe_deckUnitsHom]
  exact ⟨fun ⟨h, hh⟩ => ⟨h.toAdd, hh⟩, fun ⟨h, hh⟩ => ⟨Multiplicative.ofAdd h, hh⟩⟩

end AddMonoidAlgebra
