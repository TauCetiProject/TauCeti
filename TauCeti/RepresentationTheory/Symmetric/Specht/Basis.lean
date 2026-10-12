/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex

/-!
# The Specht character basis

The characters of the complex Specht modules form a basis of the class functions of `Sₙ`.
This uses their irreducibility and pairwise distinctness, together with the correspondence
between partitions and conjugacy classes.
-/

public section

namespace TauCeti

open CategoryTheory

variable {n : ℕ}

private noncomputable instance : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private instance : ∀ μ : n.Partition,
    Representation.IsIrreducible (spechtModuleℂ μ).ρ := fun μ =>
  (FDRep.simple_iff_isIrreducible (spechtModuleℂ μ)).mp inferInstance

private theorem spechtRepresentation_pairwise :
    Pairwise fun μ ν : n.Partition =>
      IsEmpty (Representation.Equiv (spechtModuleℂ μ).ρ (spechtModuleℂ ν).ρ) := by
  intro μ ν hne
  rw [← not_nonempty_iff]
  intro h
  exact hne ((spechtModuleℂ_iso_iff μ ν).mp (nonempty_fdRepIso_iff.mpr h))

/-- The complex Specht characters give every class function on `Sₙ` a unique expansion. -/
noncomputable def spechtCharacterBasis (n : ℕ) :
    Module.Basis (n.Partition) ℂ (ClassFunction ℂ (Equiv.Perm (Fin n))) := by
  have hcard : Nat.card (n.Partition) = Nat.card (ConjClasses (Equiv.Perm (Fin n))) :=
    Nat.card_congr (partitionEquivConjClasses n)
  exact ClassFunction.basisOfIrreducibleCharacters
    (fun μ => (spechtModuleℂ μ).ρ) spechtRepresentation_pairwise hcard

/-- The `μ`-th vector in the class-function basis is the character of the complex Specht
module `S^μ`. -/
@[simp]
theorem spechtCharacterBasis_apply (μ : n.Partition) :
    spechtCharacterBasis n μ = ClassFunction.ofCharacter (spechtModuleℂ μ).ρ := by
  unfold spechtCharacterBasis
  exact ClassFunction.basisOfIrreducibleCharacters_apply _ _ _ μ

/-- The coordinate of a class function at a Specht character is its character pairing with
that character. -/
@[simp]
theorem spechtCharacterBasis_repr (f : ClassFunction ℂ (Equiv.Perm (Fin n)))
    (μ : n.Partition) :
    (spechtCharacterBasis n).repr f μ =
      ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f := by
  classical
  conv_rhs => rw [← (spechtCharacterBasis n).sum_repr f]
  rw [map_sum, Finset.sum_eq_single μ]
  · rw [map_smul, spechtCharacterBasis_apply,
      ClassFunction.characterPairing_ofCharacter_self, smul_eq_mul, mul_one]
  · intro ν _ hν
    rw [map_smul, spechtCharacterBasis_apply,
      ClassFunction.characterPairing_ofCharacter_eq_zero _ _
        (spechtRepresentation_pairwise hν), smul_zero]
  · intro hμ
    exact absurd (Finset.mem_univ μ) hμ

end TauCeti
