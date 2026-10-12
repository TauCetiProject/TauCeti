/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.PowerSum
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.YoungRule
public import TauCeti.RepresentationTheory.Symmetric.Specht.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial

/-!
# The finite-variable Frobenius characteristic and Frobenius's formula

For `d ≥ n`, the complex class functions of `Sₙ` and the symmetric homogeneous polynomials of
degree `n` in `d` variables have bases indexed by the partitions of `n`. The first basis consists
of the characters of the complex Specht modules; the second consists of the Schur polynomials.
The Frobenius characteristic is the linear equivalence taking one basis to the other.

Its classical description is the **cycle-type formula**: the Frobenius characteristic of a class
function `f` is the average of the power-sum products over the cycle types,

`ch(f) = (1 / n!) · ∑_{π ∈ Sₙ} f(π) · p_{ρ(π)}`.

That formula rests on **Frobenius's formula**, which expands the power-sum products in the Schur
polynomials with the character table of `Sₙ` as the matrix of coefficients,

`p_ρ = ∑_{λ ⊢ n} χ^λ(ρ) · s_λ`,

and on its inverse `∑_{π ∈ Sₙ} χ^μ(π) · p_{ρ(π)} = n! · s_μ`. Both are proved here, in any finite
alphabet and over any commutative ring, through the monomial symmetric polynomials `m_ν`. The
power sums expand as `p_ρ = ∑_ν ψ^ν(ρ) m_ν` with the permutation characters `ψ^ν` as coefficients
(`TauCeti.psumPart_eq_sum_card_fixedPoints_smul_msymm`), and the Schur polynomials as
`s_λ = ∑_ν K_{λν} m_ν` with the Kostka numbers (`TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm`).
Young's rule `ψ^ν = ∑_λ K_{λν} χ^λ`
(`TauCeti.char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar`) converts the first expansion
into the second, which is Frobenius's formula; its character-pairing form
`∑_π χ^μ(π) ψ^ν(π) = n! K_{μν}` (`TauCeti.sum_spechtChar_mul_char_permutationModule`) gives the
inverse directly, without passing through the orthogonality relations.

## Main definitions

* `TauCeti.frobeniusCharacteristic`: the basis-preserving linear equivalence to symmetric
  homogeneous polynomials.

## Main results

* `TauCeti.frobeniusCharacteristic_spechtCharacter`: the image of the character of `S^μ` is
  the Schur polynomial `s_μ`.
* `TauCeti.schurPolyBasis_repr_frobeniusCharacteristic`: each Schur coordinate is the pairing
  with the corresponding Specht character.
* `TauCeti.psumPart_eq_sum_spechtCharValue_smul_schurPoly`: **Frobenius's formula**
  `p_ρ = ∑_λ χ^λ(ρ) s_λ`.
* `TauCeti.sum_spechtChar_smul_psumPart`: **its inverse**, `∑_π χ^μ(π) p_{ρ(π)} = n! s_μ`.
* `TauCeti.frobeniusCharacteristic_eq_sum_psumPart`: **the cycle-type formula** for the
  Frobenius characteristic.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7,
  where the power sums are expanded in the Schur functions with the characters of `Sₙ` as
  coefficients.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, §4.1
  (Frobenius's formula) and Appendix A.
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

/-! ### Frobenius's formula -/

section Formula

open Equiv MvPolynomial

variable {σ : Type*} [Fintype σ] (R : Type*) [CommRing R]

/-- Young's rule on the fixed-tabloid counts, over `ℤ`: the number of `ν`-tabloids fixed by `π` is
`∑_λ K_{λν} χ^λ(π)`. -/
private theorem card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar (ν : n.Partition)
    (π : Perm (Fin n)) :
    (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℤ) =
      ∑ l : n.Partition, (kostkaNumber l ν : ℤ) * spechtChar l π := by
  have h := char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar ν π
  rw [char_permutationModule] at h
  exact_mod_cast h

/-- Young's rule as a character pairing, over `ℤ` and with the permutation character written as
the fixed-tabloid count: `∑_π χ^λ(π) ψ^ν(π) = n! K_{λν}`. -/
private theorem sum_spechtChar_mul_card_fixedPoints (l ν : n.Partition) :
    ∑ π : Perm (Fin n),
        spechtChar l π * (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℤ) =
      n.factorial * kostkaNumber l ν := by
  have h : ∑ π : Perm (Fin n), (spechtChar l π : ℚ) *
      (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℚ) =
      n.factorial * kostkaNumber l ν := by
    rw [← sum_spechtChar_mul_char_permutationModule]
    exact Finset.sum_congr rfl fun π _ => by rw [char_permutationModule]
  exact_mod_cast h

/-- **Frobenius's formula**: the power-sum product of a partition `ρ` of `n` expands in the Schur
polynomials as `p_ρ = ∑_{λ ⊢ n} χ^λ(ρ) s_λ`, the coefficients being the column of `ρ` in the
character table of `Sₙ`. This holds in every finite alphabet and over every commutative ring; the
Schur polynomials of the partitions with more parts than the alphabet has letters vanish. -/
theorem psumPart_eq_sum_spechtCharValue_smul_schurPoly (ρ : n.Partition) :
    psumPart σ R ρ = ∑ l : n.Partition, spechtCharValue l ρ • schurPoly σ R l := by
  obtain ⟨π, hπ⟩ := (partitionEquivConjClasses n ρ).exists_rep
  have hχ (l : n.Partition) : spechtCharValue l ρ = spechtChar l π :=
    spechtCharValue_eq_spechtChar l ρ hπ
  classical
  simp_rw [psumPart_eq_sum_card_fixedPoints_smul_msymm R hπ, hχ,
    schurPoly_eq_sum_kostkaNumber_smul_msymm, Finset.smul_sum, ← smul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := congrArg (Int.cast : ℤ → R) (card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar ν π)
  push_cast at h
  simp_rw [h, zsmul_eq_mul, mul_comm]

/-- **The inverse of Frobenius's formula**: weighting the power-sum products over the cycle types by
a Specht character recovers the Schur polynomial, `∑_{π ∈ Sₙ} χ^μ(π) p_{ρ(π)} = n! s_μ`. Over a
`ℚ`-algebra this says that `(1 / n!) ∑_π χ^μ(π) p_{ρ(π)}` is `s_μ`. -/
theorem sum_spechtChar_smul_psumPart (μ : n.Partition) :
    ∑ π : Perm (Fin n), spechtChar μ π • psumPart σ R π.partition =
      n.factorial • schurPoly σ R μ := by
  classical
  have hp (π : Perm (Fin n)) : psumPart σ R π.partition =
      psumPart σ R ((partitionEquivConjClasses n).symm (ConjClasses.mk π)) :=
    (psumPart_eq_psumPart_partition R ((partitionEquivConjClasses n).apply_symm_apply _).symm).symm
  have hm (π : Perm (Fin n)) := psumPart_eq_sum_card_fixedPoints_smul_msymm (σ := σ) R
    ((partitionEquivConjClasses n).apply_symm_apply (ConjClasses.mk π)).symm
  simp_rw [hp, hm, schurPoly_eq_sum_kostkaNumber_smul_msymm, Finset.smul_sum, ← smul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := congrArg (Int.cast : ℤ → R) (sum_spechtChar_mul_card_fixedPoints μ ν)
  push_cast at h
  simp_rw [zsmul_eq_mul, nsmul_eq_mul, h]

end Formula

/-! ### The cycle-type formula -/

open Equiv MvPolynomial in
/-- **The cycle-type formula for the Frobenius characteristic**: the Frobenius characteristic of a
class function `f` of `Sₙ` is `(1 / n!) ∑_{π ∈ Sₙ} f(π) p_{ρ(π)}`, the average of the power-sum
products over the cycle types weighted by `f`. -/
theorem frobeniusCharacteristic_eq_sum_psumPart (d : ℕ) (h : n ≤ d)
    (f : ClassFunction ℂ (Perm (Fin n))) :
    ((frobeniusCharacteristic n d h f : symmetricHomogeneousSubmodule (Fin d) ℂ n) :
      MvPolynomial (Fin d) ℂ) =
      (n.factorial : ℂ)⁻¹ •
        ∑ π : Perm (Fin n), (f : Perm (Fin n) → ℂ) π • psumPart (Fin d) ℂ π.partition := by
  -- both sides are linear in `f`, and they agree on the basis of Specht characters
  let L : ClassFunction ℂ (Perm (Fin n)) →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    (n.factorial : ℂ)⁻¹ • (Fintype.linearCombination ℂ fun π : Perm (Fin n) =>
      psumPart (Fin d) ℂ π.partition) ∘ₗ (ClassFunction ℂ (Perm (Fin n))).subtype
  have hL : (symmetricHomogeneousSubmodule (Fin d) ℂ n).subtype ∘ₗ
      (frobeniusCharacteristic n d h).toLinearMap = L := by
    refine (spechtCharacterBasis n).ext fun μ => ?_
    have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      spechtCharacterBasis_apply, frobeniusCharacteristic_spechtCharacter, L, LinearMap.smul_apply,
      Fintype.linearCombination_apply, ClassFunction.ofCharacter_apply, FDRep.character_ρ,
      character_spechtModuleℂ_intCast, Int.cast_smul_eq_zsmul, sum_spechtChar_smul_psumPart,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  exact congr($hL f)

end TauCeti
