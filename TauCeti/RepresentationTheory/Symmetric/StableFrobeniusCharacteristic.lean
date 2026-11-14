/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
import TauCeti.RepresentationTheory.Symmetric.Specht.Extremes

/-!
# The stable Frobenius characteristic

The finite-variable Frobenius characteristic `TauCeti.frobeniusCharacteristic` identifies the
complex class functions of `Sₙ` with the symmetric polynomials of degree `n` in an alphabet of at
least `n` letters. This file removes the dependence on the alphabet: the **Frobenius
characteristic** `ch_n` is the linear equivalence from the class functions of `Sₙ` onto the
symmetric functions of degree `n`, `TauCeti.stableSymmetricSubmodule ℂ n`, sending the character
`χ^μ` of the complex Specht module `S^μ` to the Schur function `s_μ`.

Projecting `ch_n` to an alphabet of `d ≥ n` letters gives back the finite-variable characteristic.
The **cycle-type formula** `ch_n(f) = ∑_ρ (f(ρ) / z_ρ) p_ρ` expands `ch_n(f)` in the power-sum
products `p_ρ = TauCeti.stablePsumPart ℂ ρ`; in every alphabet, including those with fewer than
`n` letters, the projection of `ch_n(f)` is the ungrouped average
`(1 / n!) ∑_{π ∈ Sₙ} f(π) p_{ρ(π)}`.
The trivial character goes to the complete homogeneous symmetric function `h_n` and the sign
character to the elementary symmetric function `e_n`.

The Schur coordinates of `ch_n(f)` are the character pairings `⟨χ^μ, f⟩`, which are the
multiplicities of the irreducible characters when `f` is a character. Hence `f` is a virtual
character, an integer combination of characters, exactly when all Schur coordinates of `ch_n(f)`
are integers: `ch_n` identifies the virtual characters of `Sₙ` with the complex symmetric
functions of degree `n` having integer Schur coordinates, the `ℤ`-span of the Schur basis.

## Main definitions

* `TauCeti.stableFrobeniusCharacteristic n`: the Frobenius characteristic
  `ClassFunction ℂ (Equiv.Perm (Fin n)) ≃ₗ[ℂ] stableSymmetricSubmodule ℂ n`.

## Main results

* `TauCeti.stableFrobeniusCharacteristic_spechtCharacter`: `ch_n(χ^μ) = s_μ`, with the inverse
  form `TauCeti.stableFrobeniusCharacteristic_symm_stableSchur`.
* `TauCeti.stableSchurBasis_repr_stableFrobeniusCharacteristic`: the Schur coordinates of `ch_n(f)`
  are the character pairings `⟨χ^μ, f⟩`.
* `TauCeti.stableSymmetricProj_stableFrobeniusCharacteristic`: in `d ≥ n` variables, `ch_n` is the
  finite-variable Frobenius characteristic.
* `TauCeti.stableFrobeniusCharacteristic_eq_sum_stablePsumPart`: the cycle-type formula
  `ch_n(f) = ∑_ρ (f(ρ) / z_ρ) p_ρ`.
* `TauCeti.coe_stableSymmetricProj_stableFrobeniusCharacteristic_eq_sum_psumPart`: the ungrouped
  cycle-type formula, in every alphabet.
* `TauCeti.stableFrobeniusCharacteristic_trivial`, `TauCeti.stableFrobeniusCharacteristic_sign`:
  `ch_n(1) = h_n` and `ch_n(sgn) = e_n`, with inverse forms
  `TauCeti.stableFrobeniusCharacteristic_symm_stableHsymm` and
  `TauCeti.stableFrobeniusCharacteristic_symm_stableEsymm`.
* `TauCeti.mem_virtualCharacters_iff_forall_exists_stableSchurBasis_repr_eq_intCast`: a class
  function is a virtual character exactly when its characteristic has integral Schur coordinates.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7: the characteristic map `ch : R → Λ`, (7.2) for `ch(f) = ∑_ρ z_ρ⁻¹ f(ρ) p_ρ`, and
  `ch(χ^λ) = s_λ`, `ch(1) = h_n` and `ch(ε) = e_n`.
-/

public section

namespace TauCeti

open Equiv MvPolynomial

variable {n : ℕ}

variable (n) in
/-- **The Frobenius characteristic** `ch_n`: the linear equivalence from the complex class functions
of `Sₙ` to the symmetric functions of degree `n` sending the character of each complex Specht module
`S^μ` to the Schur function `s_μ`. -/
noncomputable def stableFrobeniusCharacteristic :
    ClassFunction ℂ (Perm (Fin n)) ≃ₗ[ℂ] stableSymmetricSubmodule ℂ n :=
  (spechtCharacterBasis n).equiv (stableSchurBasis ℂ n) (Equiv.refl _)

/-- **The Frobenius characteristic of an irreducible character is its Schur function**,
`ch_n(χ^μ) = s_μ`. -/
@[simp]
theorem stableFrobeniusCharacteristic_spechtCharacter (μ : n.Partition) :
    stableFrobeniusCharacteristic n (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) =
      stableSchur ℂ μ := by
  rw [← spechtCharacterBasis_apply, stableFrobeniusCharacteristic, Module.Basis.equiv_apply,
    Equiv.refl_apply, stableSchurBasis_apply]

/-- The inverse of the Frobenius characteristic takes the Schur function `s_μ` to the irreducible
character `χ^μ`. -/
@[simp]
theorem stableFrobeniusCharacteristic_symm_stableSchur (μ : n.Partition) :
    (stableFrobeniusCharacteristic n).symm (stableSchur ℂ μ) =
      ClassFunction.ofCharacter (spechtModuleℂ μ).ρ := by
  rw [LinearEquiv.symm_apply_eq, stableFrobeniusCharacteristic_spechtCharacter]

/-- **The Schur coordinates of a Frobenius characteristic are character pairings**: the coefficient
of `s_μ` in `ch_n(f)` is `⟨χ^μ, f⟩`, the multiplicity of `χ^μ` when `f` is a character. -/
@[simp]
theorem stableSchurBasis_repr_stableFrobeniusCharacteristic (f : ClassFunction ℂ (Perm (Fin n)))
    (μ : n.Partition) :
    (stableSchurBasis ℂ n).repr (stableFrobeniusCharacteristic n f) μ =
      ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f := by
  rw [← spechtCharacterBasis_repr]
  conv_lhs => rw [← (spechtCharacterBasis n).sum_repr f]
  simp only [map_sum, map_smul, spechtCharacterBasis_apply,
    stableFrobeniusCharacteristic_spechtCharacter, ← stableSchurBasis_apply,
    Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.univ_sum_single]

/-- **The Schur expansion of a Frobenius characteristic**:
`ch_n(f) = ∑_μ ⟨χ^μ, f⟩ s_μ`. -/
theorem stableFrobeniusCharacteristic_apply (f : ClassFunction ℂ (Perm (Fin n))) :
    stableFrobeniusCharacteristic n f =
      ∑ μ : n.Partition,
        ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f •
          stableSchur ℂ μ := by
  conv_lhs => rw [← (spechtCharacterBasis n).sum_repr f]
  simp only [map_sum, map_smul, spechtCharacterBasis_apply,
    stableFrobeniusCharacteristic_spechtCharacter, spechtCharacterBasis_repr]

/-- **In `d ≥ n` variables the Frobenius characteristic is the finite-variable one**: projecting
`ch_n(f)` to the alphabet `Fin d` gives `TauCeti.frobeniusCharacteristic (Fin d) n`. -/
theorem stableSymmetricProj_stableFrobeniusCharacteristic {d : ℕ} (h : n ≤ d)
    (f : ClassFunction ℂ (Perm (Fin n))) :
    stableSymmetricProj ℂ n d (stableFrobeniusCharacteristic n f) =
      frobeniusCharacteristic (Fin d) n (by simpa using h) f := by
  have key : stableSymmetricProj ℂ n d ∘ₗ (stableFrobeniusCharacteristic n).toLinearMap =
      (frobeniusCharacteristic (Fin d) n (by simpa using h)).toLinearMap :=
    (spechtCharacterBasis n).ext fun μ => Subtype.ext <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, spechtCharacterBasis_apply,
        stableFrobeniusCharacteristic_spechtCharacter, coe_stableSymmetricProj_stableSchur,
        frobeniusCharacteristic_spechtCharacter]
  exact congr($key f)

/-- **The ungrouped cycle-type formula for the Frobenius characteristic**: in every alphabet
`Fin d`, the projection of `ch_n(f)` is `(1 / n!) ∑_{π ∈ Sₙ} f(π) p_{ρ(π)}`. Unlike
`TauCeti.frobeniusCharacteristic_eq_sum_psumPart`, there is no condition on the number of letters:
in fewer than `n` variables both sides are projections of the same symmetric function. -/
theorem coe_stableSymmetricProj_stableFrobeniusCharacteristic_eq_sum_psumPart (d : ℕ)
    (f : ClassFunction ℂ (Perm (Fin n))) :
    (stableSymmetricProj ℂ n d (stableFrobeniusCharacteristic n f) : MvPolynomial (Fin d) ℂ) =
      (n.factorial : ℂ)⁻¹ •
        ∑ π : Perm (Fin n), (f : Perm (Fin n) → ℂ) π • psumPart (Fin d) ℂ π.partition := by
  simp only [stableFrobeniusCharacteristic_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul, coe_stableSymmetricProj_stableSchur, sum_characterPairing_smul_schurPoly]

/-- **The cycle-type formula for the Frobenius characteristic**, `ch_n(f) = ∑_ρ (f(ρ) / z_ρ) p_ρ`:
the coefficient of the power-sum product `p_ρ` is the value of `f` on the permutations of cycle
type `ρ` divided by the order `z_ρ` of their centralizer. -/
theorem stableFrobeniusCharacteristic_eq_sum_stablePsumPart (f : ClassFunction ℂ (Perm (Fin n))) :
    stableFrobeniusCharacteristic n f =
      ∑ ρ : n.Partition,
        (ClassFunction.toConjClasses f (partitionEquivConjClasses n ρ) / (zPart ρ : ℂ)) •
          stablePsumPart ℂ ρ := by
  refine stableSymmetricSubmodule_ext fun d => Subtype.ext ?_
  classical
  rw [coe_stableSymmetricProj_stableFrobeniusCharacteristic_eq_sum_psumPart]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    coe_stableSymmetricProj_stablePsumPart]
  -- group the permutations by cycle type: the class of type `ρ` has `n! / z_ρ` elements
  rw [← Finset.sum_fiberwise Finset.univ (fun π => (partitionEquivConjClasses n).symm
    (ConjClasses.mk π)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hmem (π : Perm (Fin n)) : (partitionEquivConjClasses n).symm (ConjClasses.mk π) = ρ ↔
      π ∈ (partitionEquivConjClasses n ρ).carrier := by
    rw [Equiv.symm_apply_eq, ConjClasses.mem_carrier_iff_mk_eq]
  have hterm : ∀ π ∈ Finset.univ.filter
      fun π => (partitionEquivConjClasses n).symm (ConjClasses.mk π) = ρ,
      (f : Perm (Fin n) → ℂ) π • psumPart (Fin d) ℂ π.partition =
        ClassFunction.toConjClasses f (partitionEquivConjClasses n ρ) • psumPart (Fin d) ℂ ρ := by
    intro π hπ
    have hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ :=
      (Equiv.symm_apply_eq _).mp (Finset.mem_filter.mp hπ).2
    rw [← hπ, ClassFunction.toConjClasses_mk, psumPart_eq_psumPart_partition ℂ hπ]
  have hcard : ((Finset.univ.filter fun π : Perm (Fin n) =>
      (partitionEquivConjClasses n).symm (ConjClasses.mk π) = ρ).card : ℂ) * zPart ρ =
      n.factorial := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (β := (partitionEquivConjClasses n ρ).carrier)
      (Equiv.subtypeEquivRight fun π => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem])]
    exact_mod_cast card_carrier_partitionEquivConjClasses_mul_zPart ρ
  have hz : (zPart ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (zPart_pos ρ).ne'
  have hc : ((Finset.univ.filter fun π : Perm (Fin n) =>
      (partitionEquivConjClasses n).symm (ConjClasses.mk π) = ρ).card : ℂ) ≠ 0 :=
    left_ne_zero_of_mul (hcard ▸ Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    smul_smul, ← hcard]
  congr 1
  field_simp

/-- **The Frobenius characteristic of the trivial character is the complete homogeneous symmetric
function**, `ch_n(1) = h_n`. -/
@[simp]
theorem stableFrobeniusCharacteristic_trivial :
    stableFrobeniusCharacteristic n
        (ClassFunction.ofCharacter (Representation.trivial ℂ (Perm (Fin n)) ℂ)) =
      stableHsymm ℂ n := by
  have h : ClassFunction.ofCharacter (Representation.trivial ℂ (Perm (Fin n)) ℂ) =
      ClassFunction.ofCharacter (spechtModuleℂ (Nat.Partition.indiscrete n)).ρ :=
    Subtype.ext <| funext fun π => by
      simp only [ClassFunction.ofCharacter_apply, Representation.char_trivial,
        Module.finrank_self, Nat.cast_one, FDRep.character_ρ, character_spechtModuleℂ_intCast,
        spechtChar_indiscrete, Int.cast_one]
  rw [h, stableFrobeniusCharacteristic_spechtCharacter, stableSchur_indiscrete]

/-- **The Frobenius characteristic of the sign character is the elementary symmetric function**,
`ch_n(sgn) = e_n`. -/
@[simp]
theorem stableFrobeniusCharacteristic_sign :
    stableFrobeniusCharacteristic n
        (ClassFunction.ofCharacter
          (Representation.ofLinearCharacter (signLinearCharacter ℂ (Fin n)))) =
      stableEsymm ℂ n := by
  have h : ClassFunction.ofCharacter
        (Representation.ofLinearCharacter (signLinearCharacter ℂ (Fin n))) =
      ClassFunction.ofCharacter (spechtModuleℂ (Nat.Partition.ones n)).ρ :=
    Subtype.ext <| funext fun π => by
      simp only [ClassFunction.ofCharacter_apply, Representation.char_ofLinearCharacter,
        coe_signLinearCharacter_apply, FDRep.character_ρ, character_spechtModuleℂ_intCast,
        spechtChar_ones]
  rw [h, stableFrobeniusCharacteristic_spechtCharacter, stableSchur_ones]

/-- The inverse of the Frobenius characteristic takes the complete homogeneous symmetric function
`h_n` to the trivial character. -/
@[simp]
theorem stableFrobeniusCharacteristic_symm_stableHsymm :
    (stableFrobeniusCharacteristic n).symm (stableHsymm ℂ n) =
      ClassFunction.ofCharacter (Representation.trivial ℂ (Perm (Fin n)) ℂ) := by
  rw [LinearEquiv.symm_apply_eq, stableFrobeniusCharacteristic_trivial]

/-- The inverse of the Frobenius characteristic takes the elementary symmetric function `e_n` to
the sign character. -/
@[simp]
theorem stableFrobeniusCharacteristic_symm_stableEsymm :
    (stableFrobeniusCharacteristic n).symm (stableEsymm ℂ n) =
      ClassFunction.ofCharacter
        (Representation.ofLinearCharacter (signLinearCharacter ℂ (Fin n))) := by
  rw [LinearEquiv.symm_apply_eq, stableFrobeniusCharacteristic_sign]

/-- The inverse of the Frobenius characteristic in degree `0` takes the unit of the symmetric
functions to the trivial character of `S₀`. -/
@[simp]
theorem stableFrobeniusCharacteristic_zero_symm_stableSymmetricOne :
    (stableFrobeniusCharacteristic 0).symm (stableSymmetricOne ℂ) =
      ClassFunction.ofCharacter (Representation.trivial ℂ (Perm (Fin 0)) ℂ) := by
  rw [← stableHsymm_zero, stableFrobeniusCharacteristic_symm_stableHsymm]

/-- **The virtual characters are the class functions with integral Schur coordinates**: a class
function `f` of `Sₙ` is an integer combination of characters exactly when every Schur coordinate
`⟨χ^μ, f⟩` of its Frobenius characteristic is an integer. The virtual characters form a proper
sublattice of the integer-valued class functions: for `n = 2` the class function with values `1` at
the identity and `0` at the transposition is integer-valued, but its Schur coordinates are `1 / 2`.
-/
theorem mem_virtualCharacters_iff_forall_exists_stableSchurBasis_repr_eq_intCast
    (f : ClassFunction ℂ (Perm (Fin n))) :
    (f : Perm (Fin n) → ℂ) ∈ virtualCharacters ℂ (Perm (Fin n)) ↔
      ∀ μ : n.Partition, ∃ z : ℤ,
        (stableSchurBasis ℂ n).repr (stableFrobeniusCharacteristic n f) μ = z := by
  have hχ (μ : n.Partition) :
      ((ClassFunction.ofCharacter (spechtModuleℂ μ).ρ : ClassFunction ℂ (Perm (Fin n))) :
        Perm (Fin n) → ℂ) = (spechtModuleℂ μ).character :=
    funext fun π => by rw [ClassFunction.ofCharacter_apply, FDRep.character_ρ]
  simp only [stableSchurBasis_repr_stableFrobeniusCharacteristic]
  refine ⟨fun hf μ => exists_characterPairing_eq_intCast ?_ hf, fun h => ?_⟩
  · rw [hχ]
    exact character_mem_virtualCharacters (spechtModuleℂ μ)
  choose z hz using h
  have hf : (f : Perm (Fin n) → ℂ) = ∑ μ, z μ • (spechtModuleℂ μ).character := by
    conv_lhs => rw [← (spechtCharacterBasis n).sum_repr f]
    simp only [spechtCharacterBasis_repr, hz, spechtCharacterBasis_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower, hχ, Int.cast_smul_eq_zsmul]
  rw [hf]
  exact AddSubgroup.sum_mem _ fun μ _ =>
    AddSubgroup.zsmul_mem _ (character_mem_virtualCharacters (spechtModuleℂ μ)) _

end TauCeti
