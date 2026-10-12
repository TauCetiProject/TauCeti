/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Multiplicity
public import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality
import TauCeti.LinearAlgebra.Matrix.Cholesky.Unitriangular
import TauCeti.RepresentationTheory.Symmetric.PermutationModule.PowerSum
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.HsymmPart

/-!
# Young's rule

The Young permutation module `M^ν` of a partition `ν` of `n`, the permutation representation of
`Sₙ` on the `ν`-tabloids, decomposes into Specht modules according to the Kostka numbers: the
multiplicity of `S^λ` in `M^ν` is the number `K_{λν}` of semistandard tableaux of shape `λ` and
content `ν`. This is **Young's rule**, proved here in three equivalent forms:

* `TauCeti.spechtMultiplicity_eq_kostkaNumber`: the dimension of the space of intertwiners from
  `S^λ` to `M^ν`, `TauCeti.spechtMultiplicity`, is `K_{λν}`;
* `TauCeti.sum_spechtChar_mul_char_permutationModule`: the character pairing of `χ^λ` with the
  permutation character `ψ^ν` of `M^ν` is `K_{λν}`;
* `TauCeti.char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar`: `ψ^ν = ∑_λ K_{λν} χ^λ`.

## The argument

Write `m_{λν} = ⟨χ^λ, ψ^ν⟩` for the multiplicities. Both matrices `m` and `K` are unitriangular
for the dominance order: `K_{λν}` vanishes unless `λ` dominates `ν` and `K_{νν} = 1`
(`TauCeti.kostkaNumber_eq_zero_of_not_dominates`, `TauCeti.kostkaNumber_self`), and the same holds
for `m` (`TauCeti.spechtMultiplicity_eq_zero_of_not_dominates`, `TauCeti.spechtMultiplicity_self`).
They also have the same Gram matrix. Expanding `ψ^ν` and `ψ^ξ` in the Specht characters
(`TauCeti.eq_sum_spechtChar`) gives `∑_λ m_{λν} m_{λξ} = ⟨ψ^ν, ψ^ξ⟩`. On the other side,
`∑_π ψ^ν(π) p_{ρ(π)} = n! h_ν` (`TauCeti.sum_card_fixedPoints_smul_psumPart_partition`), whose
coefficient at the monomial of `ξ` is `n! ⟨ψ^ν, ψ^ξ⟩` on the left and, by
`h_ν = ∑_μ K_{μν} s_μ`, `n! ∑_μ K_{μν} K_{μξ}` on the right
(`TauCeti.sum_char_permutationModule_mul_char_permutationModule`). A unitriangular matrix is
determined by its Gram matrix (`TauCeti.eq_of_transpose_mul_self_eq`), so `m = K`.

## Main results

* `TauCeti.sum_char_permutationModule_mul_char_permutationModule`: **`∑_π ψ^ν(π) ψ^ξ(π)` is
  `n! ∑_μ K_{μν} K_{μξ}`**.
* `TauCeti.sum_spechtChar_shapePartition_mul_char_permutationModule`: the pairing of the Specht
  character of a diagram with a permutation character is the Specht multiplicity.
* `TauCeti.sum_spechtChar_mul_char_permutationModule`: **`⟨χ^λ, ψ^ν⟩ = K_{λν}`**.
* `TauCeti.spechtMultiplicity_eq_kostkaNumber`: **Young's rule**, the Specht multiplicity in a
  Young permutation module is a Kostka number.
* `TauCeti.char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar`: **`ψ^ν = ∑_λ K_{λν} χ^λ`**.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 14.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Sections 6 and 7.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.11.
-/

public section

namespace TauCeti

open Equiv MvPolynomial

variable {n : ℕ}

/-- **The inner product of two permutation characters**: `∑_π ψ^ν(π) ψ^ξ(π) = n! ∑_μ K_{μν} K_{μξ}`.
Both sides are the coefficient of the monomial of `ξ` in `∑_π ψ^ν(π) p_{ρ(π)} = n! h_ν`,
read on the left through the monomial expansion of the power sums and on the right through the
Schur expansion `h_ν = ∑_μ K_{μν} s_μ`. -/
theorem sum_char_permutationModule_mul_char_permutationModule (ν ξ : n.Partition) :
    ∑ π : Perm (Fin n),
        (permutationModule ν).ρ.character π * (permutationModule ξ).ρ.character π =
      n.factorial * ∑ μ : n.Partition, (kostkaNumber μ ν * kostkaNumber μ ξ : ℚ) := by
  -- a partition of `n` has at most `n` parts, so `n` letters record its sorted monomial
  have hξ : ξ.parts.card ≤ Fintype.card (Fin n) := by
    have h := Multiset.card_nsmul_le_sum (s := ξ.parts) (a := 1) fun x hx => ξ.parts_pos hx
    rw [smul_eq_mul, mul_one, ξ.parts_sum] at h
    rwa [Fintype.card_fin]
  have key := congrArg (fun p : MvPolynomial (Fin n) ℚ => p.coeff (partWeight (Fin n) ξ))
    (sum_card_fixedPoints_smul_psumPart_partition (σ := Fin n) ℚ ν)
  simp only [← Nat.cast_smul_eq_nsmul ℚ, coeff_sum, coeff_smul, smul_eq_mul,
    coeff_partWeight_psumPart_partition ℚ _ ξ hξ,
    coeff_hsymmPart_partWeight ν ξ (by rwa [colLen_zero_diagramOf])] at key
  rw [← key]
  exact Finset.sum_congr rfl fun π _ => by rw [char_permutationModule, char_permutationModule]

/-- **The pairing of a Specht character with a permutation character is the Specht
multiplicity**: for a Young diagram `D` and a partition `μ` of its size,
`∑_π χ^{D}(π) ψ^μ(π) = |D|! · m`, where `m = TauCeti.spechtMultiplicity D μ` is the dimension of
the space of intertwiners from the Specht module of `D` to `M^μ`. -/
theorem sum_spechtChar_shapePartition_mul_char_permutationModule (D : YoungDiagram)
    (μ : D.card.Partition) :
    ∑ π, (spechtChar (shapePartition D) π : ℚ) * (permutationModule μ).ρ.character π =
      D.card.factorial * spechtMultiplicity D μ := by
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (spechtSubrepresentation D).toRepresentation (permutationModule μ).ρ
  rw [← spechtMultiplicity_def, Nat.card_perm, Nat.card_fin] at h
  have hfac : (D.card.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  rw [← h, mul_inv_cancel_left₀ hfac]
  -- a permutation is conjugate to its inverse, so the Specht character does not see the inverse
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [mul_comm, ← spechtChar_shapePartition, spechtChar_eq_of_isConj _
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv π).symm)]

/-- The pairing of `χ^λ` with `ψ^ν` vanishes unless `λ` dominates `ν`: this is the vanishing of the
Specht multiplicity outside the dominance cone. -/
private theorem sum_spechtChar_mul_char_permutationModule_eq_zero {l ν : n.Partition}
    (h : ¬Dominates l ν) :
    ∑ π, (spechtChar l π : ℚ) * (permutationModule ν).ρ.character π = 0 := by
  obtain ⟨D, hc, rfl⟩ : ∃ (D : YoungDiagram) (hc : D.card = n), toPartition D hc = l :=
    ⟨_, _, toPartition_diagramOf l⟩
  subst hc
  rw [toPartition_eq_shapePartition] at h ⊢
  rw [sum_spechtChar_shapePartition_mul_char_permutationModule,
    spechtMultiplicity_eq_zero_of_not_dominates ν h, Nat.cast_zero, mul_zero]

/-- The pairing of `χ^λ` with `ψ^λ` is `1`, up to the factor `n!`: this is the diagonal Specht
multiplicity. -/
private theorem sum_spechtChar_mul_char_permutationModule_self (l : n.Partition) :
    ∑ π, (spechtChar l π : ℚ) * (permutationModule l).ρ.character π = n.factorial := by
  obtain ⟨D, hc, rfl⟩ : ∃ (D : YoungDiagram) (hc : D.card = n), toPartition D hc = l :=
    ⟨_, _, toPartition_diagramOf l⟩
  subst hc
  rw [toPartition_eq_shapePartition, sum_spechtChar_shapePartition_mul_char_permutationModule,
    spechtMultiplicity_self, Nat.cast_one, mul_one]

open scoped DominanceOrder in
/-- **Young's rule, as a character pairing**: `∑_π χ^λ(π) ψ^ν(π) = n! K_{λν}`, that is, the
multiplicity `⟨χ^λ, ψ^ν⟩` of the Specht character `χ^λ` in the permutation character `ψ^ν` of
`M^ν` is the Kostka number `K_{λν}`. -/
theorem sum_spechtChar_mul_char_permutationModule (l ν : n.Partition) :
    ∑ π, (spechtChar l π : ℚ) * (permutationModule ν).ρ.character π =
      n.factorial * kostkaNumber l ν := by
  have hfac : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  -- the matrix of multiplicities `m_{λν} = ⟨χ^λ, ψ^ν⟩` and the Kostka matrix
  let U : Matrix n.Partition n.Partition ℚ := Matrix.of fun l ν =>
    (n.factorial : ℚ)⁻¹ * ∑ π, (permutationModule ν).ρ.character π * spechtChar l π
  let V : Matrix n.Partition n.Partition ℚ := Matrix.of fun l ν => (kostkaNumber l ν : ℚ)
  have hU : ∀ l ν : n.Partition, ∑ π, (spechtChar l π : ℚ) * (permutationModule ν).ρ.character π =
      n.factorial * U l ν := fun l ν => by
    simp only [U, Matrix.of_apply, mul_inv_cancel_left₀ hfac, mul_comm]
  have hUV : U = V := by
    refine eq_of_transpose_mul_self_eq (fun l ν h => ?_) (fun l ν h => ?_) (fun l => ?_)
      (fun l => ?_) ?_
    · rw [DominanceOrder.partition_le_iff]
      by_contra hd
      exact h (by rw [← mul_right_inj' hfac, ← hU, mul_zero,
        sum_spechtChar_mul_char_permutationModule_eq_zero hd])
    · rw [DominanceOrder.partition_le_iff]
      by_contra hd
      exact h (by simp [V, kostkaNumber_eq_zero_of_not_dominates hd])
    · rw [← mul_right_inj' hfac, ← hU, sum_spechtChar_mul_char_permutationModule_self, mul_one]
    · simp [V, kostkaNumber_self]
    · -- the Gram matrices agree: both are `⟨ψ^ν, ψ^ξ⟩`
      ext ν ξ
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      have hE : ∀ π, ∑ l, U l ν * spechtChar l π = (permutationModule ν).ρ.character π :=
        fun π => by
          have h := eq_sum_spechtChar (ClassFunction.ofCharacter (permutationModule ν).ρ) π
          simp only [ClassFunction.ofCharacter_apply] at h
          exact h.symm
      have hL : ∑ l, U l ν * U l ξ = (n.factorial : ℚ)⁻¹ * ∑ π,
          (permutationModule ν).ρ.character π * (permutationModule ξ).ρ.character π := by
        have hUξ : ∀ l, U l ξ = (n.factorial : ℚ)⁻¹ *
            ∑ π, (permutationModule ξ).ρ.character π * spechtChar l π := fun l => rfl
        simp_rw [hUξ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [← hE π, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hL, sum_char_permutationModule_mul_char_permutationModule, inv_mul_cancel_left₀ hfac]
      rfl
  rw [hU, hUV]
  rfl

/-- **Young's rule**: the multiplicity of the Specht module `S^λ` in the Young permutation module
`M^μ`, the dimension of the space of intertwiners `TauCeti.spechtMultiplicity λ μ`, is the Kostka
number `K_{λμ}`, the number of semistandard tableaux of shape `λ` and content `μ`. -/
theorem spechtMultiplicity_eq_kostkaNumber (lam : YoungDiagram) (μ : lam.card.Partition) :
    spechtMultiplicity lam μ = kostkaNumber (shapePartition lam) μ := by
  have hfac : (lam.card.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have h := (sum_spechtChar_shapePartition_mul_char_permutationModule lam μ).symm.trans
    (sum_spechtChar_mul_char_permutationModule (shapePartition lam) μ)
  exact_mod_cast mul_left_cancel₀ hfac h

/-- **Young's rule, on characters**: the permutation character of `M^ν` is
`ψ^ν = ∑_λ K_{λν} χ^λ`. -/
theorem char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar (ν : n.Partition)
    (σ : Perm (Fin n)) :
    (permutationModule ν).ρ.character σ =
      ∑ l : n.Partition, (kostkaNumber l ν : ℚ) * spechtChar l σ := by
  have hfac : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have h := eq_sum_spechtChar (ClassFunction.ofCharacter (permutationModule ν).ρ) σ
  simp only [ClassFunction.ofCharacter_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_congr rfl fun π _ => mul_comm _ _, sum_spechtChar_mul_char_permutationModule,
    inv_mul_cancel_left₀ hfac]

end TauCeti
