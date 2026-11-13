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
In every alphabet, including those with fewer than `n` letters, the projection of `ch_n(f)` is
given by the **cycle-type formula** `(1 / n!) ∑_{π ∈ Sₙ} f(π) p_{ρ(π)}`; grouping the
permutations by cycle type, this is Macdonald's `∑_ρ z_ρ⁻¹ f(ρ) p_ρ` read in `d` variables. The
trivial character goes to the complete homogeneous symmetric function `h_n` and the sign
character to the elementary symmetric function `e_n`.

The Schur coordinates of `ch_n(f)` are the multiplicities `⟨χ^μ, f⟩`. Hence `f` is a virtual
character, an integer combination of characters, exactly when all Schur coordinates of `ch_n(f)`
are integers: `ch_n` identifies the virtual characters of `Sₙ` with the integral symmetric
functions of degree `n` written in the Schur basis.

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
* `TauCeti.coe_stableSymmetricProj_stableFrobeniusCharacteristic`: the cycle-type formula, in
  every alphabet.
* `TauCeti.stableFrobeniusCharacteristic_trivial`, `TauCeti.stableFrobeniusCharacteristic_sign`:
  `ch_n(1) = h_n` and `ch_n(sgn) = e_n`.
* `TauCeti.mem_virtualCharacters_iff_forall_exists_stableSchurBasis_repr_eq_intCast`: a class
  function is a virtual character exactly when its characteristic has integral Schur coordinates.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7: the characteristic map `ch : R → Λ`, (7.2) for `ch(f) = ∑_ρ z_ρ⁻¹ f(ρ) p_ρ` and
  (7.3) for `ch(χ^λ) = s_λ`, with `ch(1) = h_n` and `ch(ε) = e_n`.
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

/-- **The Schur coordinates of a Frobenius characteristic are multiplicities**: the coefficient of
`s_μ` in `ch_n(f)` is the character pairing `⟨χ^μ, f⟩`. -/
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

/-- **The cycle-type formula for the Frobenius characteristic**: in every alphabet `Fin d`, the
projection of `ch_n(f)` is `(1 / n!) ∑_{π ∈ Sₙ} f(π) p_{ρ(π)}`. Unlike
`TauCeti.frobeniusCharacteristic_eq_sum_psumPart`, there is no condition on the number of letters:
in fewer than `n` variables both sides are projections of the same symmetric function. -/
theorem coe_stableSymmetricProj_stableFrobeniusCharacteristic (d : ℕ)
    (f : ClassFunction ℂ (Perm (Fin n))) :
    (stableSymmetricProj ℂ n d (stableFrobeniusCharacteristic n f) : MvPolynomial (Fin d) ℂ) =
      (n.factorial : ℂ)⁻¹ •
        ∑ π : Perm (Fin n), (f : Perm (Fin n) → ℂ) π • psumPart (Fin d) ℂ π.partition := by
  -- both sides are linear in `f`, and they agree on the basis of Specht characters by the inverse
  -- of Frobenius's formula, which holds in every alphabet
  let L : ClassFunction ℂ (Perm (Fin n)) →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    (n.factorial : ℂ)⁻¹ • (Fintype.linearCombination ℂ fun π : Perm (Fin n) =>
      psumPart (Fin d) ℂ π.partition) ∘ₗ (ClassFunction ℂ (Perm (Fin n))).subtype
  have hL : (symmetricHomogeneousSubmodule (Fin d) ℂ n).subtype ∘ₗ stableSymmetricProj ℂ n d ∘ₗ
      (stableFrobeniusCharacteristic n).toLinearMap = L := by
    refine (spechtCharacterBasis n).ext fun μ => ?_
    have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      spechtCharacterBasis_apply, stableFrobeniusCharacteristic_spechtCharacter,
      coe_stableSymmetricProj_stableSchur, L, LinearMap.smul_apply,
      Fintype.linearCombination_apply, ClassFunction.ofCharacter_apply, FDRep.character_ρ,
      character_spechtModuleℂ_intCast, Int.cast_smul_eq_zsmul, sum_spechtChar_smul_psumPart,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  exact congr($hL f)

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
