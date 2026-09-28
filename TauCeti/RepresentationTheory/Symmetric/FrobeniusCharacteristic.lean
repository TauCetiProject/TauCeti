/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-!
# The finite-variable Frobenius characteristic

For `d ≥ n`, the complex class functions of `Sₙ` and the symmetric homogeneous polynomials of
degree `n` in `d` variables have bases indexed by the partitions of `n`. The first basis consists
of the characters of the complex Specht modules; the second consists of the Schur polynomials.
The Frobenius characteristic is the linear equivalence taking one basis to the other.
Its cycle-type formula in the power-sum basis requires Young's rule and is a separate step.

## Main definitions

* `TauCeti.frobeniusCharacteristic`: the basis-preserving linear equivalence to symmetric
  homogeneous polynomials.

## Main results

* `TauCeti.frobeniusCharacteristic_spechtCharacter`: the image of the character of `S^μ` is
  the Schur polynomial `s_μ`.
* `TauCeti.schurPolyBasis_repr_frobeniusCharacteristic`: each Schur coordinate is the pairing
  with the corresponding Specht character.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
-/

public section

namespace TauCeti

variable {n : ℕ}

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
  simpa only [partitionEquivSchurIndex_apply] using
    coe_schurPolyBasis (partitionEquivSchurIndex n d h μ)

/-- The Schur coordinate of a Frobenius characteristic is the pairing with the corresponding
Specht character. -/
@[simp]
theorem schurPolyBasis_repr_frobeniusCharacteristic (d : ℕ) (h : n ≤ d)
    (f : ClassFunction ℂ (Equiv.Perm (Fin n)))
    (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card (Fin d)}) :
    (schurPolyBasis (Fin d) ℂ n).repr (frobeniusCharacteristic n d h f) μ =
      ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ.1).ρ) f := by
  let e := partitionEquivSchurIndex n d h
  have hμ : e μ.1 = μ := by
    apply Subtype.ext
    exact partitionEquivSchurIndex_apply n d h μ.1
  conv_lhs => rw [← hμ]
  rw [frobeniusCharacteristic]
  have hrepr := Module.Basis.repr_reindex_apply (schurPolyBasis (Fin d) ℂ n)
    ((spechtCharacterBasis n).equiv (schurPolyBasis (Fin d) ℂ n) e f) e.symm μ.1
  simp only [Equiv.symm_symm] at hrepr
  rw [← hrepr]
  rw [← Module.Basis.map_equiv (spechtCharacterBasis n) (schurPolyBasis (Fin d) ℂ n) e]
  simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact spechtCharacterBasis_repr f μ.1

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
  conv_lhs => rw [← (spechtCharacterBasis n).sum_repr f]
  simp [spechtCharacterBasis_repr, frobeniusCharacteristic_spechtCharacter]

end TauCeti
