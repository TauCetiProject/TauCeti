/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Orthogonal
public import TauCeti.Order.Atoms

/-!
# Polarizable pure Hodge structures are semisimple

A polarization splits off every rational Hodge substructure, so the lattice of rational Hodge
substructures of a polarizable pure Hodge structure is complemented. Over a finite-dimensional
rational space that lattice is also modular and satisfies the descending chain condition, and the
two properties together give the classical decomposition: a polarizable pure Hodge structure is
the direct sum of finitely many **simple** rational Hodge substructures — the atoms of the lattice
— pairwise independent and spanning.

The complement itself is the orthogonal complement
`TauCeti.Hodge.RationalHodgeSubstructure.orthogonal` for a polarizing form; the decomposition is
then the lattice-theoretic `TauCeti.exists_finset_isAtom_sup_eq`, which splits off one atom at a
time in any complemented modular lattice with the descending chain condition.
Only *some* polarizing form is used, never a chosen one, so the statements are about
`TauCeti.Hodge.IsPolarizable` structures: this is the semisimplicity of the polarizable Hodge
structures, for which the choice of a form is not part of the object.

Following Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink,
*Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure.complementedLattice_of_isPolarizable`: the lattice of
  rational Hodge substructures of a polarizable pure Hodge structure is complemented.
* `TauCeti.Hodge.RationalHodgeSubstructure.exists_finset_isAtom_sup_eq`: every rational Hodge
  substructure is the supremum of a finite independent family of simple substructures.
* `TauCeti.Hodge.exists_finset_isAtom_sup_eq_top`: **semisimplicity**, a polarizable pure Hodge
  structure is the direct sum of finitely many simple rational Hodge substructures.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n} [Module.Finite ℚ Vℚ]

namespace RationalHodgeSubstructure

/-- A polarization makes the lattice of rational Hodge substructures complemented: the orthogonal
complement for its form is a lattice complement. -/
theorem complementedLattice (P : Polarization hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  ⟨fun W ↦ ⟨orthogonal P W, isCompl_orthogonal P W⟩⟩

/-- **Every rational Hodge substructure of a polarizable pure Hodge structure is a direct
summand**: the lattice of rational Hodge substructures is complemented. -/
theorem complementedLattice_of_isPolarizable (h : IsPolarizable hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  let ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  complementedLattice P

/-- **Every rational Hodge substructure of a polarized pure Hodge structure is a finite direct sum
of simple substructures**: it is the supremum of a finite family of atoms of the lattice of
rational Hodge substructures, pairwise independent. -/
theorem exists_finset_isAtom_sup_eq (P : Polarization hℂ hs) (W : RationalHodgeSubstructure hℚ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = W :=
  have : ComplementedLattice (RationalHodgeSubstructure hℚ hs) := complementedLattice P
  _root_.TauCeti.exists_finset_isAtom_sup_eq W

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable pure Hodge structures.** A polarizable pure Hodge structure on
a finite-dimensional rational space is the direct sum of finitely many simple rational Hodge
substructures: there is a finite independent family of atoms of the lattice of rational Hodge
substructures whose supremum is everything. -/
theorem exists_finset_isAtom_sup_eq_top (hℚ : IsBaseChange ℚ ιℚ) (h : IsPolarizable hℂ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = ⊤ := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  exact RationalHodgeSubstructure.exists_finset_isAtom_sup_eq P ⊤

end TauCeti.Hodge
