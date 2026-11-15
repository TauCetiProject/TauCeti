/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Lattice
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Permutation.Augmentation
public import TauCeti.RepresentationTheory.Augmentation.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Herbrand quotients of lattices spanning a sum-zero permutation representation

An integral representation spanning the sum-zero permutation representation over a
nontrivial `ℚ`-algebra has the same Herbrand quotient as the standard integral augmentation
lattice. For a finite cyclic group this is the product of the orbit-stabilizer orders divided
by the group order.

This is the representation-theoretic comparison used with logarithmic unit lattices: it
needs an equivariant scalar-extension map, not just equality of ranks. The standard comparison
map is `augmentationScalarMap`; Tate's lattice lemma handles the other lattice.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3, the Herbrand quotient of units.
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII.
-/

public noncomputable section

namespace TauCeti.TateCohomology

open _root_.MulAction

variable {G X : Type} [Group G] [Fintype G] [IsCyclic G] [MulAction G X] [Finite X]
  {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
  (M : Rep ℤ G) [Module.Free ℤ M] [Module.Finite ℤ M]

/-- An integral lattice spanning a sum-zero permutation representation has the Herbrand
quotient of the integral augmentation lattice. The comparison must respect the group action. -/
theorem _root_.Rep.herbrandQuotient_eq_augmentationSubrepresentation_of_isBaseChange
    (i : M →ₗ[ℤ] (augmentationSubrepresentation K G X).toSubmodule)
    (hi : IsBaseChange K i)
    (hiG : ∀ g x, i (M.ρ g x) =
      (augmentationSubrepresentation K G X).toRepresentation g (i x)) :
    herbrandQuotient M =
      herbrandQuotient (Rep.of (augmentationSubrepresentation ℤ G X).toRepresentation) := by
  have : Module.Free ℤ (augmentationSubrepresentation ℤ G X).toSubmodule :=
    Module.Free.of_basis
      ((augmentationSubrepresentation ℤ G X).toSubmodule.basisOfPid
        (MonoidAlgebra.basis X ℤ)).2
  exact herbrandQuotient_eq_of_isBaseChange
    (augmentationSubrepresentation K G X).toRepresentation hi
    (isBaseChange_augmentationScalarMap ℤ K G X) hiG
    (augmentationScalarMap_action ℤ K G X)

/-- The Herbrand quotient of a lattice spanning a nonempty finite sum-zero permutation
representation is the product of the orbit-stabilizer orders divided by the group order. -/
theorem _root_.Rep.herbrandQuotient_of_isBaseChange_augmentationSubrepresentation [Nonempty X]
    [Fintype (orbitRel.Quotient G X)]
    (i : M →ₗ[ℤ] (augmentationSubrepresentation K G X).toSubmodule)
    (hi : IsBaseChange K i)
    (hiG : ∀ g x, i (M.ρ g x) =
      (augmentationSubrepresentation K G X).toRepresentation g (i x)) :
    herbrandQuotient M =
      (∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G ω.out) : ℚ)) / Nat.card G := by
  rw [Rep.herbrandQuotient_eq_augmentationSubrepresentation_of_isBaseChange M i hi hiG,
    herbrandQuotient_augmentationSubrepresentation]

end TauCeti.TateCohomology
