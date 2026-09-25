/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Partitions
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-!
# The power sums and the permutation characters of `Sₙ`

Let `ψ^ν` be the character of the Young permutation module `M^ν`, the permutation representation
of `Sₙ` on the `ν`-tabloids.  These characters are the coefficients of the power-sum product
`p_ρ` of a partition `ρ` of `n` in the monomial symmetric polynomials `m_ν`,

`p_ρ = ∑_{ν ⊢ n} ψ^ν(ρ) m_ν`,

where `ψ^ν(ρ)` is the value of `ψ^ν` at any permutation of cycle type `ρ`.  Equivalently, the
coefficient of `x^d` in `p_ρ` is the number of tabloids fixed by such a permutation, for the shape
obtained by sorting the exponents of `x^d`.

The proof reads both sides as counts of invariant colourings.  A `ν`-tabloid is a colouring of
`Fin n` by the rows of `ν` (`TauCeti.quotientFiberSubgroupEquiv`, applied to the row map
`TauCeti.youngBlock ν`), and it is fixed by `π` exactly when the colouring is constant on the cycles
of `π`; on the other side, the coefficient of `x^d` in `p_ρ` counts the colourings constant on the
cycles of `π` with `d i` points of colour `i` (`TauCeti.coeff_psumPart_partition`).  Writing the
rows of `ν` as letters of the alphabet puts the two counts side by side at the sorted monomial of
`ν`, and the symmetry of `p_ρ` moves any other monomial of degree `n` there
(`TauCeti.coeff_eq_coeff_partWeight`).

Combined with Young's rule, `ψ^ν = ∑_λ K_{λν} χ^λ`, and the monomial expansion of the Schur
polynomials `s_λ = ∑_ν K_{λν} m_ν` (`TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm`), this
expansion is Frobenius's formula `p_ρ = ∑_λ χ^λ(ρ) s_λ` for the irreducible characters.

## Main results

* `TauCeti.coeff_partWeight_psumPart_partition`: the coefficient of the power-sum product over the
  cycle type of `π` at the sorted monomial of `ν` counts the `ν`-tabloids fixed by `π`.
* `TauCeti.coeff_psumPart_eq_card_fixedPoints`: **the coefficient of `p_ρ` at any monomial of
  degree `n`** counts the tabloids fixed by a permutation of cycle type `ρ`, for the shape of the
  monomial.
* `TauCeti.psumPart_eq_sum_card_fixedPoints_smul_msymm`: **the monomial expansion of `p_ρ`**, with
  the fixed-tabloid counts as coefficients.
* `TauCeti.psumPart_eq_sum_character_smul_msymm`: the same expansion over `ℚ`, with the
  characters of the Young permutation modules as coefficients.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Proposition 7.7.1.
-/

public section

namespace TauCeti

open Equiv Finset MvPolynomial

variable {σ : Type*} [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}

/-! ### The rows of a partition as letters -/

/-- The rows of `ν` fit in an alphabet with at least as many letters as `ν` has parts. -/
private theorem length_sort_parts_le (ν : n.Partition) (hν : ν.parts.card ≤ Fintype.card σ) :
    (ν.parts.sort (· ≥ ·)).length ≤ Fintype.card σ :=
  (Multiset.length_sort _).trans_le hν

/-- The power-sum product of the partition indexing the class of `π` is the power-sum product over
the cycle type of `π`: both take one power sum per cycle. -/
private theorem psumPart_eq_psumPart_partition {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) :
    psumPart σ R ρ = psumPart σ R π.partition := by
  rw [psumPart, psumPart, ← (partitionEquivConjClasses n).symm_apply_apply ρ, ← hπ,
    parts_partitionEquivConjClasses_symm_mk]

/-- The colouring of `Fin n` by the rows of `ν`, the `i`-th row being written as the `i`-th letter
of the alphabet `σ`. -/
private noncomputable def youngColouring (ν : n.Partition) (hν : ν.parts.card ≤ Fintype.card σ) :
    Fin n → σ :=
  (Fintype.equivFin σ).symm ∘ Fin.castLE (length_sort_parts_le ν hν) ∘ youngBlock ν

/-- The permutations preserving the colouring by rows are the Young subgroup. -/
private theorem fiberSubgroup_youngColouring (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    fiberSubgroup (youngColouring ν hν) = youngSubgroup ν := by
  rw [youngColouring, ← Function.comp_assoc, youngSubgroup_eq_fiberSubgroup]
  exact fiberSubgroup_comp_of_injective
    ((Fintype.equivFin σ).symm.injective.comp (Fin.castLE_injective _)) _

/-- In the colouring by rows, each letter of `σ` is used as often as the sorted monomial of `ν`
prescribes: the `i`-th letter as often as the `i`-th part, and the letters beyond the last part
not at all. -/
private theorem card_filter_youngColouring [DecidableEq σ] (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) (x : σ) :
    #{j | youngColouring ν hν j = x} = partWeight σ ν x := by
  rw [partWeight_apply, rowLen_diagramOf]
  rcases lt_or_ge (Fintype.equivFin σ x : ℕ) (ν.parts.sort (· ≥ ·)).length with hx | hx
  · -- The letter `x` is the row `i`, whose cells are the fibre of `youngBlock ν` over `i`.
    let i : Fin (ν.parts.sort (· ≥ ·)).length := ⟨Fintype.equivFin σ x, hx⟩
    have hfilter : (univ.filter fun j => youngColouring ν hν j = x) =
        univ.filter fun j => youngBlock ν j = i := by
      refine Finset.filter_congr fun j _ => ?_
      rw [youngColouring, Function.comp_apply, Function.comp_apply, Equiv.symm_apply_eq,
        Fin.ext_iff, Fin.ext_iff, Fin.val_castLE, eq_comm]
    rw [hfilter, ← Fintype.card_subtype, ← Fintype.card_congr (youngBlockEquiv ν i),
      Fintype.card_fin, List.getD_eq_getElem _ _ hx]
  · -- The letter `x` lies beyond the last row, so it is not used.
    rw [List.getD_eq_default _ _ hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    rw [youngColouring, Function.comp_apply, Function.comp_apply, Equiv.symm_apply_eq,
      Fin.ext_iff, Fin.val_castLE] at hj
    have hlt := (youngBlock ν j).2
    omega

/-! ### The coefficients of a power-sum product -/

/-- **The coefficient of `p_ρ` at the sorted monomial of `ν` counts the `ν`-tabloids fixed by a
permutation `π` of cycle type `ρ`.**  Here `ρ` is the cycle type of `π`, fixed points included,
and the alphabet has at least as many letters as `ν` has parts. -/
theorem coeff_partWeight_psumPart_partition (π : Perm (Fin n)) (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    (psumPart σ R π.partition).coeff (partWeight σ ν) =
      Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} := by
  classical
  rw [coeff_psumPart_partition, ← fiberSubgroup_youngColouring ν hν,
    card_fixedPoints_quotient_fiberSubgroup]
  congr 3
  ext f
  exact and_congr_right' (forall_congr' fun i => by rw [card_filter_youngColouring ν hν i])

variable [DecidableEq σ]

/-- **The coefficient of `p_ρ` at a monomial of degree `n` counts fixed tabloids**: at `x^d` it is
the number of tabloids fixed by a permutation `π` of cycle type `ρ`, for the shape obtained by
sorting the exponents of `x^d`.  That count is the value at `π` of the permutation character of the
corresponding Young permutation module (`TauCeti.char_permutationModule`). -/
theorem coeff_psumPart_eq_card_fixedPoints {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {d : σ →₀ ℕ}
    (h : d.degree = n) :
    (psumPart σ R ρ).coeff d =
      Nat.card {q : Perm (Fin n) ⧸ youngSubgroup (weightPartition d h) // π • q = q} := by
  rw [coeff_eq_coeff_partWeight (psumPart_isSymmetric R ρ) h, psumPart_eq_psumPart_partition R hπ,
    coeff_partWeight_psumPart_partition R π _ (card_parts_weightPartition_le d h)]

/-! ### The monomial expansion -/

/-- **The monomial expansion of a power-sum product**: `p_ρ = ∑_{ν ⊢ n} ψ^ν(π) m_ν` for any
permutation `π` of cycle type `ρ`, where `ψ^ν(π)` is the number of `ν`-tabloids fixed by `π`.
The sum runs over every partition of `n`: those with more parts than the alphabet has letters
contribute nothing, their monomial symmetric polynomial vanishing there. -/
theorem psumPart_eq_sum_card_fixedPoints_smul_msymm {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) :
    psumPart σ R ρ = ∑ ν : n.Partition,
      (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : R) • msymm σ R ν := by
  ext d
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  by_cases hd : d.degree = n
  · rw [coeff_psumPart_eq_card_fixedPoints R hπ hd, Finset.sum_eq_single (weightPartition d hd)]
    · rw [coeff_msymm R _ hd, ite_eq_left rfl, mul_one]
    · exact fun ν _ hne => by
        rw [coeff_msymm R ν hd, ite_eq_right fun hw => hne hw.symm, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · rw [(isHomogeneous_psumPart R ρ).coeff_eq_zero hd]
    exact (Finset.sum_eq_zero fun ν _ => by
      rw [coeff_msymm_eq_zero_of_degree_ne R ν hd, mul_zero]).symm

/-- **The monomial expansion of a power-sum product in terms of permutation characters**:
`p_ρ = ∑_{ν ⊢ n} ψ^ν(π) m_ν` over `ℚ`, where `ψ^ν` is the character of the Young permutation
module `M^ν` and `π` is any permutation of cycle type `ρ`. -/
theorem psumPart_eq_sum_character_smul_msymm {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) :
    psumPart σ ℚ ρ = ∑ ν : n.Partition, (permutationModule ν).ρ.character π • msymm σ ℚ ν := by
  refine (psumPart_eq_sum_card_fixedPoints_smul_msymm (σ := σ) ℚ hπ).trans
    (Finset.sum_congr rfl fun ν _ => ?_)
  rw [char_permutationModule]

end TauCeti
