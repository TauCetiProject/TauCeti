/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The finite-variable Frobenius characteristic

For `d ≥ n`, the complex class functions of `Sₙ` and the symmetric homogeneous polynomials of
degree `n` in `d` variables have bases indexed by the partitions of `n`. The first basis consists
of the characters of the complex Specht modules; the second consists of the Schur polynomials.
The Frobenius characteristic is the linear equivalence taking one basis to the other.
Its cycle-type formula in the power-sum basis requires Young's rule and is a separate step.

## Main definitions

* `TauCeti.spechtCharacterBasis`: the Specht characters form a basis of class functions.
* `TauCeti.frobeniusCharacteristic`: the basis-preserving linear equivalence to symmetric
  homogeneous polynomials.

## Main results

* `TauCeti.frobeniusCharacteristic_spechtCharacter`: the image of the character of `S^μ` is
  the Schur polynomial `s_μ`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
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

private theorem partition_parts_card_le (μ : n.Partition) : μ.parts.card ≤ n := by
  have aux : ∀ s : Multiset ℕ, (∀ x ∈ s, 0 < x) → s.card ≤ s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons x s ih =>
      intro hs
      have hx : 1 ≤ x := hs x (by simp)
      have hs' : ∀ y ∈ s, 0 < y := fun y hy => hs y (by simp [hy])
      have hsum := ih hs'
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  exact (aux μ.parts (fun x hx => μ.parts_pos hx)).trans_eq μ.parts_sum

/-- When the alphabet has at least `n` letters, every partition of `n` indexes a Schur basis
vector: it has at most `n` nonzero parts. -/
private def partitionEquivSchurIndex (n d : ℕ) (h : n ≤ d) :
    n.Partition ≃ {μ : n.Partition // μ.parts.card ≤ Fintype.card (Fin d)} where
  toFun μ := ⟨μ, (partition_parts_card_le μ).trans (by simpa using h)⟩
  invFun μ := μ.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- The finite-variable Frobenius characteristic is the linear equivalence sending the
character of each complex Specht module to the Schur polynomial of the same shape. -/
noncomputable def frobeniusCharacteristic (n d : ℕ) (h : n ≤ d) :
    ClassFunction ℂ (Equiv.Perm (Fin n)) ≃ₗ[ℂ]
      symmetricHomogeneousSubmodule (Fin d) ℂ n :=
  (spechtCharacterBasis n).equiv (schurPolyBasis (Fin d) ℂ n)
    (partitionEquivSchurIndex n d h)

/-- The Frobenius characteristic takes an irreducible character to its Schur polynomial. -/
@[simp]
theorem frobeniusCharacteristic_spechtCharacter (d : ℕ) (h : n ≤ d)
    (μ : n.Partition) :
    ((frobeniusCharacteristic n d h
      (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) :
        symmetricHomogeneousSubmodule (Fin d) ℂ n) : MvPolynomial (Fin d) ℂ) =
      schurPoly (Fin d) ℂ μ := by
  rw [← spechtCharacterBasis_apply, frobeniusCharacteristic, Module.Basis.equiv_apply]
  exact coe_schurPolyBasis (partitionEquivSchurIndex n d h μ)

/-- The Schur coefficient of a class function under the Frobenius characteristic is its
character pairing with the corresponding Specht character. This gives an explicit formula for
the map on arbitrary class functions. -/
theorem frobeniusCharacteristic_apply (d : ℕ) (h : n ≤ d)
    (f : ClassFunction ℂ (Equiv.Perm (Fin n))) :
    ((frobeniusCharacteristic n d h f : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
      MvPolynomial (Fin d) ℂ) =
      ∑ μ : n.Partition,
        ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f •
          schurPoly (Fin d) ℂ μ := by
  have hcard : Nat.card (n.Partition) = Nat.card (ConjClasses (Equiv.Perm (Fin n))) :=
    Nat.card_congr (partitionEquivConjClasses n)
  have hexp := ClassFunction.sum_characterPairing_smul_ofCharacter
    (fun μ : n.Partition => (spechtModuleℂ μ).ρ) spechtRepresentation_pairwise hcard f
  conv_lhs => rw [← hexp]
  simp [frobeniusCharacteristic_spechtCharacter]

end TauCeti
