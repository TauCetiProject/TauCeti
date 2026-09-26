/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism

/-!
# The character criterion for diagonalizable group-scheme isogenies

For finitely generated commutative character groups, `groupSchemeMap` is a central
isogeny exactly when the character homomorphism is injective with finite cokernel.
This transports the coordinate-algebra criterion to the existing diagonalizable
group-scheme functor. In particular, the surjectivity assertion is scheme-theoretic,
and the kernel is central on points valued in every test scheme.

The sufficient direction holds over any commutative base ring; the converse needs a
nonzero base. No smoothness assumption or restriction on the characteristic is imposed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12, especially Theorem 12.9.
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u

variable (R : Type u) [CommRing R] {G H : FGCommGrpCat.{u}} (φ : G ⟶ H)

/-- An injective homomorphism of finitely generated character groups with finite cokernel
induces a central isogeny of diagonalizable group schemes over any commutative ring. -/
theorem isCentralIsogeny_groupSchemeMap_of_injective_of_finite_quotient
    (hφ : Function.Injective (FGCommGrpCat.toMonoidHom φ))
    [Finite (H ⧸ (FGCommGrpCat.toMonoidHom φ).range)] :
    GroupScheme.IsCentralIsogeny (groupSchemeMap R φ) := by
  rw [groupSchemeMap_def]
  simp only [GroupScheme.IsCentralIsogeny,
    (GroupScheme.centralIsogenies R).cancel_left_of_respectsIso,
    (GroupScheme.centralIsogenies R).cancel_right_of_respectsIso]
  apply (CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map _).mp
  exact isCentralIsogeny_mapDomainBialgHom_of_injective_of_finite_quotient R
    (FGCommGrpCat.toMonoidHom φ) hφ

/-- A morphism of diagonalizable group schemes over a nonzero commutative ring is a
central isogeny exactly when its character map is injective with finite cokernel. -/
@[simp]
theorem isCentralIsogeny_groupSchemeMap_iff [Nontrivial R] :
    GroupScheme.IsCentralIsogeny (groupSchemeMap R φ) ↔
      Function.Injective (FGCommGrpCat.toMonoidHom φ) ∧
        Finite (H ⧸ (FGCommGrpCat.toMonoidHom φ).range) := by
  rw [groupSchemeMap_def]
  simp only [GroupScheme.IsCentralIsogeny,
    (GroupScheme.centralIsogenies R).cancel_left_of_respectsIso,
    (GroupScheme.centralIsogenies R).cancel_right_of_respectsIso]
  exact (CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map
    (coordinateMap R φ).hom).symm.trans
      (isCentralIsogeny_mapDomainBialgHom_iff R (FGCommGrpCat.toMonoidHom φ))

end TauCeti.DiagonalizableGroup
