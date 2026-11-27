/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.Star.StarAlgHom
import Mathlib.Data.Matrix.Block
import TauCeti.Algebra.GroupWithZero.Pi
import TauCeti.Algebra.Lie.GeneralLinear.Embedding
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.LinearAlgebra.Matrix.Submatrix
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Multiplicity matrices and realization of `⋆`-homomorphisms of matrix direct sums

Every `⋆`-homomorphism
`φ : (∀ i : ι, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j : κ, CStarMatrix (m j) (m j) ℂ)`
between finite direct sums of full complex matrix C⋆-algebras determines a nonnegative-integer
*multiplicity matrix* `φ.multiplicityMatrix : Matrix κ ι ℕ`, whose `(j, i)` entry records how many
orthogonal copies of the `i`-th source block `φ` places inside the `j`-th target block.
Equivalently, when `n i` is nonempty, `φ.multiplicityMatrix j i` is the rank (and the trace) of the
image in target block `j` of any minimal diagonal projection `Matrix.single p p 1` of source block
`i`; when `n i` is empty, the source block is zero and the entry vanishes.

This file defines `NonUnitalStarAlgHom.multiplicityMatrix`, establishes its basic rank/trace
identities, block-size inequalities, kernel/injectivity criteria, and constructs the canonical
block-diagonal realization `TauCeti.cstarMatrixPiBlockHom` together with realizability criteria.
Classification up to unitary conjugacy, approximate unitary equivalence, and functoriality under
composition are proved in
`TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix.Classification`.

## Main results

* **Multiplicity matrix and trace/rank formulas**: `NonUnitalStarAlgHom.multiplicityMatrix`,
  together with `NonUnitalStarAlgHom.multiplicityMatrix_apply`,
  `NonUnitalStarAlgHom.multiplicityMatrix_apply_eq_rank_single`,
  `NonUnitalStarAlgHom.natCast_multiplicityMatrix_apply_eq_trace_single`, and
  `NonUnitalStarAlgHom.multiplicityMatrix_mul_card_eq_rank`.
* **Block-size inequality and unitality**: for finite `ι`,
  `∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j)` for each `j`
  (`NonUnitalStarAlgHom.sum_multiplicityMatrix_mul_card_le`), with equality for all `j` if and only
  if `φ 1 = 1` (`NonUnitalStarAlgHom.map_one_eq_one_iff_sum_multiplicityMatrix_eq`,
  `StarAlgHom.sum_multiplicityMatrix_mul_card_eq`).
* **Zero blocks and injectivity**: vanishing of row `j` characterizes vanishing of the `j`-th
  coordinate of `φ`, vanishing of column `i` characterizes vanishing on the `i`-th source summand,
  and injectivity of `φ` holds if and only if every nonempty source block has a nonzero multiplicity
  in at least one target block
  (`NonUnitalStarAlgHom.injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero`, and
  `NonUnitalStarAlgHom.injective_iff_forall_exists_multiplicityMatrix_ne_zero` when every `n i` is
  nonempty).
* **Matrix-unit realization and realizability**: given `H : Matrix κ ι ℕ` and injections
  `f j : (Σ i, n i × Fin (H j i)) ↪ m j`, `TauCeti.cstarMatrixPiBlockHom` constructs the concrete
  block-diagonal `⋆`-homomorphism sending each matrix unit to a sum of `H j i` orthogonal matrix
  units along `f j`, preserving `1` if and only if each `f j` is surjective
  (`TauCeti.cstarMatrixBlockHom_one_eq_one_iff`, `TauCeti.cstarMatrixPiBlockHom_one_eq_one_iff`). A
  matrix `H` is realized by a `⋆`-homomorphism (respectively, a unital `⋆`-homomorphism) if and only
  if `H` vanishes on empty source blocks and the block-size inequalities (respectively, equalities)
  hold (`TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff`,
  `TauCeti.exists_starAlgHom_multiplicityMatrix_eq_iff`; see also the `_of_nonempty` variants when
  every `n i` is nonempty).

## References

* Mikael Rørdam, *Classification of Nuclear C⋆-Algebras*, Section 1.1.
* Bruce Blackadar, *K-Theory for Operator Algebras*, Section 7.2.
* Kenneth R. Davidson, *C⋆-Algebras by Example*, Section III.2.
-/

public section

noncomputable section

open scoped Matrix

namespace NonUnitalStarAlgHom

section Basic

variable {ι κ : Type*} {n : ι → Type*} {m : κ → Type*}
  [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]

/-- The **multiplicity matrix** of a `⋆`-homomorphism between products of complex matrix
C⋆-algebras: entry `(j, i)` is the rank of the image in target block `j` of the central unit of
source block `i`, divided by the size of block `i` (hence `0` when `n i` is empty). -/
def multiplicityMatrix
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    Matrix κ ι ℕ :=
  letI := Classical.decEq ι
  letI := fun i ↦ Classical.decEq (n i)
  Matrix.of fun j i ↦
    Matrix.rank (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) / Fintype.card (n i)

/-- Explicit formula for entry `(j, i)` of `φ.multiplicityMatrix` in terms of the rank of the image
of the `i`-th block unit. -/
theorem multiplicityMatrix_apply [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] :
    φ.multiplicityMatrix j i =
      Matrix.rank (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) / Fintype.card (n i) := by
  rw [multiplicityMatrix, Matrix.of_apply]
  congr!

/-- On an empty source block `n i`, the multiplicity `φ.multiplicityMatrix j i` vanishes. -/
@[simp]
theorem multiplicityMatrix_apply_of_isEmpty_source
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [IsEmpty (n i)] :
    φ.multiplicityMatrix j i = 0 := by
  classical
  rw [multiplicityMatrix_apply, Fintype.card_eq_zero, Nat.div_zero]

/-- On an empty target block `m j`, the multiplicity `φ.multiplicityMatrix j i` vanishes. -/
@[simp]
theorem multiplicityMatrix_apply_of_isEmpty_target
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) [IsEmpty (m j)] (i : ι) :
    φ.multiplicityMatrix j i = 0 := by
  classical
  rw [multiplicityMatrix_apply, Subsingleton.elim (CStarMatrix.ofMatrix.symm (φ _ j)) 0,
    Matrix.rank_zero, Nat.zero_div]

/-- The zero `⋆`-homomorphism has zero multiplicity matrix. -/
@[simp]
theorem multiplicityMatrix_zero :
    (0 : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ]
      (∀ j, CStarMatrix (m j) (m j) ℂ)).multiplicityMatrix = 0 := by
  classical
  ext j i
  simp [multiplicityMatrix_apply]

private theorem isIdempotentElem_map_apply
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    {x : ∀ i, CStarMatrix (n i) (n i) ℂ} (hx : IsIdempotentElem x) (j : κ) :
    IsIdempotentElem (φ x j) := by
  rw [IsIdempotentElem, ← Pi.mul_apply, ← map_mul, hx.eq]

private theorem isIdempotentElem_ofMatrix_symm_map
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    {x : ∀ i, CStarMatrix (n i) (n i) ℂ} (hx : IsIdempotentElem x) (j : κ) :
    IsIdempotentElem (CStarMatrix.ofMatrix.symm (φ x j)) := by
  rw [IsIdempotentElem, ← CStarMatrix.ofMatrix_symm_mul, (isIdempotentElem_map_apply φ hx j).eq]

private theorem trace_map_single_eq_of_index [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p q : n i) :
    Matrix.trace (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) =
      Matrix.trace (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single q q 1))) j)) := by
  have hp : (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p (1 : ℂ))) :
      ∀ i', CStarMatrix (n i') (n i') ℂ) =
      Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)) *
        Pi.single i (CStarMatrix.ofMatrix (Matrix.single q p 1)) := by simp
  have hq : (Pi.single i (CStarMatrix.ofMatrix (Matrix.single q q (1 : ℂ))) :
      ∀ i', CStarMatrix (n i') (n i') ℂ) =
      Pi.single i (CStarMatrix.ofMatrix (Matrix.single q p 1)) *
        Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)) := by simp
  rw [hp, hq, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, CStarMatrix.ofMatrix_symm_mul,
    CStarMatrix.ofMatrix_symm_mul, Matrix.trace_mul_comm]

private theorem rank_map_piSingle_one_eq_rank_single_mul_card [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p : n i) :
    Matrix.rank (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) =
      Matrix.rank (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) *
        Fintype.card (n i) := by
  apply Nat.cast_injective (R := ℂ)
  rw [← Matrix.IsIdempotentElem.trace_eq_rank
      (isIdempotentElem_ofMatrix_symm_map φ (IsIdempotentElem.one.piSingle i) j),
    Nat.cast_mul,
    ← Matrix.IsIdempotentElem.trace_eq_rank
      (isIdempotentElem_ofMatrix_symm_map φ
        ((CStarMatrix.isIdempotentElem_ofMatrix_single_one p).piSingle i) j),
    CStarMatrix.piSingle_one_eq_sum_ofMatrix_single i, map_sum, Finset.sum_apply,
    CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum]
  simp_rw [trace_map_single_eq_of_index φ j i _ p]
  simp [mul_comm]

/-- For any diagonal index `p : n i`, entry `(j, i)` of `φ.multiplicityMatrix` equals the rank of
the image in target block `j` of the minimal projection `Matrix.single p p 1` of block `i`. -/
theorem multiplicityMatrix_apply_eq_rank_single [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p : n i) :
    φ.multiplicityMatrix j i =
      Matrix.rank (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) := by
  rw [multiplicityMatrix_apply, rank_map_piSingle_one_eq_rank_single_mul_card φ j i p,
    Nat.mul_div_cancel _ (Fintype.card_pos_iff.mpr ⟨p⟩)]

/-- Cast to `ℂ`, entry `(j, i)` of `φ.multiplicityMatrix` equals the matrix trace of the image in
target block `j` of any minimal diagonal projection `Matrix.single p p 1` of source block `i`. -/
theorem natCast_multiplicityMatrix_apply_eq_trace_single [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p : n i) :
    (φ.multiplicityMatrix j i : ℂ) =
      Matrix.trace (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) := by
  rw [multiplicityMatrix_apply_eq_rank_single φ j i p,
    Matrix.IsIdempotentElem.trace_eq_rank
      (isIdempotentElem_ofMatrix_symm_map φ
        ((CStarMatrix.isIdempotentElem_ofMatrix_single_one p).piSingle i) j)]

/-- Multiplying entry `(j, i)` of `φ.multiplicityMatrix` by `Fintype.card (n i)` recovers the rank
of the image of the `i`-th block unit in target block `j`, including when `n i` is empty. -/
theorem multiplicityMatrix_mul_card_eq_rank [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] :
    φ.multiplicityMatrix j i * Fintype.card (n i) =
      Matrix.rank (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) := by
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · have h0 : (1 : CStarMatrix (n i) (n i) ℂ) = 0 := CStarMatrix.ext fun a ↦ hE.elim a
    simp [h0]
  · rw [multiplicityMatrix_apply_eq_rank_single φ j i hne.some,
      rank_map_piSingle_one_eq_rank_single_mul_card φ j i hne.some]

/-- Cast to `ℂ`, `φ.multiplicityMatrix j i * Fintype.card (n i)` equals the trace of the image in
target block `j` of the `i`-th block unit. -/
theorem natCast_multiplicityMatrix_mul_card_eq_trace [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] :
    ((φ.multiplicityMatrix j i * Fintype.card (n i) : ℕ) : ℂ) =
      Matrix.trace (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) := by
  rw [multiplicityMatrix_mul_card_eq_rank,
    Matrix.IsIdempotentElem.trace_eq_rank
      (isIdempotentElem_ofMatrix_symm_map φ (IsIdempotentElem.one.piSingle i) j)]

/-- Entrywise formula for the multiplicity matrix of the identity `⋆`-homomorphism: `1` on the
diagonal at nonempty blocks, and `0` elsewhere. -/
theorem multiplicityMatrix_id_apply [DecidableEq ι] (i' i : ι) :
    (NonUnitalStarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).multiplicityMatrix i' i =
      if i' = i ∧ Fintype.card (n i) ≠ 0 then 1 else 0 := by
  classical
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · have _ := hE; simp [Fintype.card_eq_zero]
  · by_cases hii : i' = i
    · subst hii
      simp [multiplicityMatrix_apply, Fintype.card_ne_zero, Nat.div_self Fintype.card_pos]
    · simp [hii, multiplicityMatrix_apply]

/-- When every block index type `n i` is nonempty, the identity `⋆`-homomorphism has the identity
multiplicity matrix. -/
@[simp]
theorem multiplicityMatrix_id [DecidableEq ι] [∀ i, Nonempty (n i)] :
    (NonUnitalStarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).multiplicityMatrix = 1 := by
  ext i' i; rw [multiplicityMatrix_id_apply, Matrix.one_apply]; simp [Fintype.card_ne_zero]

end Basic

section BlockInequalityAndKernel

variable {ι κ : Type*} {n : ι → Type*} {m : κ → Type*}
  [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]

private theorem trace_map_one_eq_sum [Fintype ι] [∀ i, DecidableEq (n i)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (φ 1 j)) =
      ∑ i : ι, ((φ.multiplicityMatrix j i * Fintype.card (n i) : ℕ) : ℂ) := by
  classical
  rw [← Finset.univ_sum_single (1 : ∀ i, CStarMatrix (n i) (n i) ℂ), map_sum, Finset.sum_apply,
    CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (natCast_multiplicityMatrix_mul_card_eq_trace φ j i).symm

/-- For each target block `j`, the weighted sum of source block sizes
`∑ i, φ.multiplicityMatrix j i * Fintype.card (n i)` equals the rank of `φ 1 j`. -/
theorem sum_multiplicityMatrix_mul_card_eq_rank_map_one [Fintype ι] [∀ i, DecidableEq (n i)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    ∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) =
      Matrix.rank (CStarMatrix.ofMatrix.symm (φ 1 j)) := by
  classical
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_sum, ← trace_map_one_eq_sum φ j,
    Matrix.IsIdempotentElem.trace_eq_rank (isIdempotentElem_ofMatrix_symm_map φ .one j)]

/-- **Block-size inequality**: for each target block `j`,
`∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j)`. -/
theorem sum_multiplicityMatrix_mul_card_le [Fintype ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    ∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j) := by
  classical
  rw [sum_multiplicityMatrix_mul_card_eq_rank_map_one φ j]
  exact Matrix.rank_le_card_width _

private theorem map_eq_zero_of_trace_eq_zero
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    {x : ∀ i, CStarMatrix (n i) (n i) ℂ} (j : κ) (hx : IsIdempotentElem x)
    (htr : Matrix.trace (CStarMatrix.ofMatrix.symm (φ x j)) = 0) : φ x j = 0 :=
  CStarMatrix.eq_zero_of_isIdempotentElem_of_trace_eq_zero (isIdempotentElem_map_apply φ hx j) htr

/-- **Unitality criterion**: `φ` preserves the unit (`φ 1 = 1`) if and only if equality holds in
the block-size inequality at every target block `j`. -/
theorem map_one_eq_one_iff_sum_multiplicityMatrix_eq [Fintype ι]
    [∀ i, DecidableEq (n i)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    φ 1 = 1 ↔ ∀ j, ∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) = Fintype.card (m j) := by
  refine ⟨fun h j ↦ ?_, fun h ↦ funext fun j ↦ ?_⟩
  · rw [sum_multiplicityMatrix_mul_card_eq_rank_map_one φ j, h]
    rw [Pi.one_apply, CStarMatrix.ofMatrix_symm_one, Matrix.rank_one]
  · rw [Pi.one_apply]
    have hP : IsIdempotentElem (φ 1 j) := isIdempotentElem_map_apply φ .one j
    have hzero := CStarMatrix.eq_zero_of_isIdempotentElem_of_trace_eq_zero hP.one_sub <| by
      rw [CStarMatrix.ofMatrix_symm_sub, CStarMatrix.ofMatrix_symm_one, Matrix.trace_sub,
        Matrix.trace_one, trace_map_one_eq_sum φ j, ← Nat.cast_sum, h j, sub_self]
    exact (sub_eq_zero.mp hzero).symm

/-- Row `j` of `φ.multiplicityMatrix` vanishes if and only if the `j`-th target component of `φ`
is identically zero. -/
theorem multiplicityMatrix_row_eq_zero_iff [Finite ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (∀ i, φ.multiplicityMatrix j i = 0) ↔ ∀ x, φ x j = 0 := by
  classical
  cases nonempty_fintype ι
  refine ⟨fun hj x ↦ ?_, fun hj i ↦ by simp [multiplicityMatrix_apply, hj]⟩
  have h1 : φ 1 j = 0 := map_eq_zero_of_trace_eq_zero φ j .one <| by
    rw [trace_map_one_eq_sum φ j]
    simp [hj]
  rw [← mul_one x, map_mul, Pi.mul_apply, h1, mul_zero]

/-- Column `i` of `φ.multiplicityMatrix` vanishes if and only if `φ` vanishes on the `i`-th source
summand. -/
theorem multiplicityMatrix_col_eq_zero_iff [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (i : ι) :
    (∀ j, φ.multiplicityMatrix j i = 0) ↔ ∀ a, φ (Pi.single i a) = 0 := by
  classical
  refine ⟨fun hi a ↦ funext fun j ↦ ?_, fun hi j ↦ by simp [multiplicityMatrix_apply, hi]⟩
  have he : φ (Pi.single i 1) j = 0 :=
    map_eq_zero_of_trace_eq_zero φ j (IsIdempotentElem.piSingle_one i) <| by
      rw [← natCast_multiplicityMatrix_mul_card_eq_trace φ j i, hi j, zero_mul, Nat.cast_zero]
  have hmul : (Pi.single i a : ∀ i', CStarMatrix (n i') (n i') ℂ) =
      Pi.single i 1 * Pi.single i a := by rw [← Pi.single_mul, one_mul]
  rw [hmul, map_mul, Pi.mul_apply, he, zero_mul, Pi.zero_apply]

/-- The multiplicity matrix of `φ` is zero if and only if `φ = 0`. -/
@[simp]
theorem multiplicityMatrix_eq_zero_iff [Finite ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    φ.multiplicityMatrix = 0 ↔ φ = 0 := by
  refine ⟨fun h ↦ ext fun x ↦ funext fun j ↦ ?_, fun h ↦ by simp [h]⟩
  exact (multiplicityMatrix_row_eq_zero_iff φ j).mp (fun i ↦ by simp [h]) x

/-- **Injectivity criterion** (including possibly empty blocks): `φ` is injective if and only if
every nonempty source block `i` has a nonzero entry in column `i` of `φ.multiplicityMatrix`. -/
theorem injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    Function.Injective φ ↔ ∀ i, Nonempty (n i) → ∃ j, φ.multiplicityMatrix j i ≠ 0 := by
  classical
  rw [injective_iff_map_eq_zero]
  refine ⟨fun hinj i ⟨p⟩ ↦ ?_, fun hcol x hx ↦ funext fun i ↦ ?_⟩
  · by_contra! hzero
    have ha := (multiplicityMatrix_col_eq_zero_iff φ i).mp hzero
      (CStarMatrix.ofMatrix (Matrix.single p p 1))
    have h0 := congrArg (fun y ↦ y i p p) (hinj _ ha)
    simp at h0
  · rcases isEmpty_or_nonempty (n i) with hE | hne
    · exact CStarMatrix.ext fun a ↦ hE.elim a
    · by_contra hxi
      have ⟨p, q, hpq⟩ : ∃ p q : n i, x i p q ≠ 0 := by
        by_contra! hall
        exact hxi (CStarMatrix.ext hall)
      -- Simplicity of `M_{n i}(ℂ)`: sandwiching `x i` between matrix units recovers every unit.
      have hsingle (a b : n i) :
          φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single a b 1))) = 0 := by
        have hid : (Pi.single i (CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ))) :
            ∀ i', CStarMatrix (n i') (n i') ℂ) =
            Pi.single i (CStarMatrix.ofMatrix (Matrix.single a p 1)) * x *
              Pi.single i (CStarMatrix.ofMatrix (Matrix.single q b (x i p q)⁻¹)) := by
          rw [← Pi.single_mul_left, ← Pi.single_mul,
            CStarMatrix.ofMatrix_single_mul_mul_ofMatrix_single, one_mul, mul_inv_cancel₀ hpq]
        rw [hid, map_mul, map_mul, hx, mul_zero, zero_mul]
      obtain ⟨j, hj⟩ := hcol i hne
      apply hj
      rw [multiplicityMatrix_apply_eq_rank_single φ j i p, hsingle p p]
      simp

/-- **Injectivity criterion**: when every source block `n i` is nonempty, `φ` is injective if and
only if no column of `φ.multiplicityMatrix` vanishes. -/
theorem injective_iff_forall_exists_multiplicityMatrix_ne_zero [∀ i, Nonempty (n i)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    Function.Injective φ ↔ ∀ i, ∃ j, φ.multiplicityMatrix j i ≠ 0 := by
  rw [injective_iff_forall_nonempty_exists_multiplicityMatrix_ne_zero]
  exact forall_congr' fun i ↦ ⟨fun h ↦ h inferInstance, fun h _ ↦ h⟩

end BlockInequalityAndKernel

end NonUnitalStarAlgHom

namespace StarAlgHom

section Basic

variable {ι κ : Type*} {n : ι → Type*} {m : κ → Type*}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

/-- Entrywise formula for the multiplicity matrix of the identity unital `⋆`-homomorphism: `1` on
the diagonal at nonempty blocks, and `0` elsewhere. -/
theorem multiplicityMatrix_id_apply [DecidableEq ι] (i' i : ι) :
    (StarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom.multiplicityMatrix
        i' i =
      if i' = i ∧ Fintype.card (n i) ≠ 0 then 1 else 0 := by
  rw [toNonUnitalStarAlgHom_id, NonUnitalStarAlgHom.multiplicityMatrix_id_apply]

/-- When every block index type `n i` is nonempty, the identity unital `⋆`-homomorphism has the
identity multiplicity matrix. -/
theorem multiplicityMatrix_id [DecidableEq ι] [∀ i, Nonempty (n i)] :
    (StarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom.multiplicityMatrix =
      1 := by
  rw [toNonUnitalStarAlgHom_id, NonUnitalStarAlgHom.multiplicityMatrix_id]

/-- For a unital `⋆`-homomorphism `φ`, the weighted sum of source block sizes in each target block
`j` equals `Fintype.card (m j)`. -/
theorem sum_multiplicityMatrix_mul_card_eq [Fintype ι] [∀ j, Fintype (m j)]
    [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    ∑ i, φ.toNonUnitalStarAlgHom.multiplicityMatrix j i * Fintype.card (n i) =
      Fintype.card (m j) :=
  (φ.toNonUnitalStarAlgHom.map_one_eq_one_iff_sum_multiplicityMatrix_eq.mp (map_one φ)) j

end Basic

end StarAlgHom

namespace TauCeti

section Realization

variable {ι κ M : Type*} {n : ι → Type*} {m : κ → Type*}

private def rawBlockDiag [DecidableEq ι] (r : ι → ℕ)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    Matrix (Σ i, n i × Fin (r i)) (Σ i, n i × Fin (r i)) ℂ :=
  Matrix.blockDiagonal' fun i ↦
    Matrix.blockDiagonal fun _ : Fin (r i) ↦ CStarMatrix.ofMatrix.symm (x i)

/-- The **block-diagonal `⋆`-homomorphism** into a single matrix C⋆-algebra `CStarMatrix M M ℂ`
determined by multiplicities `r : ι → ℕ` and an injection
`f : (Σ i, n i × Fin (r i)) ↪ M`: each source block `x i` is repeated `r i` times along the
coordinates in the image of `f`, with zeros in the complementary corner. -/
def cstarMatrixBlockHom [Fintype ι] [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) :
    (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] CStarMatrix M M ℂ :=
  letI := Classical.decEq ι
  letI := Classical.decEq M
  letI : DecidableEq (Σ i, n i × Fin (r i)) := Classical.decEq _
  { toFun x := CStarMatrix.ofMatrix (glEmbedding ℂ f (rawBlockDiag r x))
    map_smul' c x := CStarMatrix.ofMatrix.symm.injective <| by
      simp only [Equiv.symm_apply_apply, CStarMatrix.ofMatrix_symm_smul, rawBlockDiag,
        Pi.smul_apply, ← Pi.smul_def, Matrix.blockDiagonal_smul, Matrix.blockDiagonal'_smul,
        map_smul, MonoidHom.id_apply]
    map_zero' := CStarMatrix.ofMatrix.symm.injective <| by
      simp only [Equiv.symm_apply_apply, CStarMatrix.ofMatrix_symm_zero, rawBlockDiag,
        Pi.zero_apply, ← Pi.zero_def, Matrix.blockDiagonal_zero, Matrix.blockDiagonal'_zero,
        map_zero]
    map_add' x y := CStarMatrix.ofMatrix.symm.injective <| by
      simp only [Equiv.symm_apply_apply, CStarMatrix.ofMatrix_symm_add, rawBlockDiag, Pi.add_apply,
        ← Pi.add_def, Matrix.blockDiagonal_add, Matrix.blockDiagonal'_add, map_add]
    map_mul' x y := CStarMatrix.ofMatrix.symm.injective <| by
      simp only [Equiv.symm_apply_apply, CStarMatrix.ofMatrix_symm_mul, glEmbedding_apply,
        rawBlockDiag, Pi.mul_apply, Matrix.blockDiagonal_mul, Matrix.blockDiagonal'_mul,
        Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((1 : Matrix M M ℂ).submatrix f id),
        Matrix.submatrix_one_mul_submatrix_one f, Matrix.one_mul]
    map_star' x := CStarMatrix.ofMatrix.symm.injective <| by
      simp [rawBlockDiag, glEmbedding_apply, Matrix.mul_assoc] }

private theorem cstarMatrixBlockHom_eq_ofMatrix_glEmbedding [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [Fintype M] [DecidableEq M]
    (r : ι → ℕ) [DecidableEq (Σ i, n i × Fin (r i))]
    (f : (Σ i, n i × Fin (r i)) ↪ M) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    cstarMatrixBlockHom r f x = CStarMatrix.ofMatrix (glEmbedding ℂ f (rawBlockDiag r x)) := by
  simp only [cstarMatrixBlockHom, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk]
  congr!

private theorem cstarMatrixBlockHom_apply_map_map [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (x : ∀ i, CStarMatrix (n i) (n i) ℂ)
    (a b : Σ i, n i × Fin (r i)) :
    cstarMatrixBlockHom r f x (f a) (f b) = rawBlockDiag r x a b := by
  classical
  rw [cstarMatrixBlockHom_eq_ofMatrix_glEmbedding, CStarMatrix.ofMatrix_apply,
    glEmbedding_apply_apply]

/-- Evaluating `cstarMatrixBlockHom r f x` at matching block `i` and copy `t` along `f` recovers
the `(p, q)` entry of `x i`. -/
@[simp]
theorem cstarMatrixBlockHom_apply_same [Fintype ι] [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (i : ι) (p q : n i) (t : Fin (r i)) :
    cstarMatrixBlockHom r f x (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) = x i p q := by
  classical
  rw [cstarMatrixBlockHom_apply_map_map]
  simp [rawBlockDiag]

/-- Entries of `cstarMatrixBlockHom r f x` between distinct source blocks `i₁ ≠ i₂` vanish. -/
theorem cstarMatrixBlockHom_apply_of_block_ne [Fintype ι] [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) {i₁ i₂ : ι} (h : i₁ ≠ i₂)
    (p : n i₁) (q : n i₂) (t₁ : Fin (r i₁)) (t₂ : Fin (r i₂)) :
    cstarMatrixBlockHom r f x (f ⟨i₁, p, t₁⟩) (f ⟨i₂, q, t₂⟩) = 0 := by
  classical
  rw [cstarMatrixBlockHom_apply_map_map, rawBlockDiag, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- Entries of `cstarMatrixBlockHom r f x` between distinct copies `t₁ ≠ t₂` of block `i` vanish. -/
theorem cstarMatrixBlockHom_apply_of_copy_ne [Fintype ι] [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (i : ι) (p q : n i) {t₁ t₂ : Fin (r i)} (h : t₁ ≠ t₂) :
    cstarMatrixBlockHom r f x (f ⟨i, p, t₁⟩) (f ⟨i, q, t₂⟩) = 0 := by
  classical
  rw [cstarMatrixBlockHom_apply_map_map, rawBlockDiag, Matrix.blockDiagonal'_apply_eq,
    Matrix.blockDiagonal_apply_ne _ _ _ h]

/-- Rows of `cstarMatrixBlockHom r f x` outside `Set.range f` vanish. -/
theorem cstarMatrixBlockHom_apply_of_notMem_range_left [Fintype ι] [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) {z₁ : M} (hz₁ : z₁ ∉ Set.range f) (z₂ : M) :
    cstarMatrixBlockHom r f x z₁ z₂ = 0 := by
  classical
  rw [cstarMatrixBlockHom_eq_ofMatrix_glEmbedding, CStarMatrix.ofMatrix_apply,
    glEmbedding_apply_apply_of_notMem_range_left f _ hz₁]

/-- Columns of `cstarMatrixBlockHom r f x` outside `Set.range f` vanish. -/
theorem cstarMatrixBlockHom_apply_of_notMem_range_right [Fintype ι] [∀ i, Fintype (n i)]
    [Fintype M] (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (z₁ : M) {z₂ : M} (hz₂ : z₂ ∉ Set.range f) :
    cstarMatrixBlockHom r f x z₁ z₂ = 0 := by
  classical
  rw [cstarMatrixBlockHom_eq_ofMatrix_glEmbedding, CStarMatrix.ofMatrix_apply,
    glEmbedding_apply_apply_of_notMem_range_right f _ _ hz₂]

/-- `cstarMatrixBlockHom r f` preserves the identity if and only if `f` is surjective. -/
theorem cstarMatrixBlockHom_one_eq_one_iff [Fintype ι] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) :
    cstarMatrixBlockHom r f 1 = 1 ↔ Function.Surjective f := by
  refine ⟨fun h z ↦ ?_, fun hf ↦ ?_⟩
  · by_contra hz
    have h0 := cstarMatrixBlockHom_apply_of_notMem_range_left r f 1 hz z
    rw [h, CStarMatrix.one_apply_eq] at h0
    exact one_ne_zero h0
  · ext z₁ z₂
    rcases hf z₁ with ⟨⟨i₁, p₁, t₁⟩, rfl⟩
    rcases hf z₂ with ⟨⟨i₂, p₂, t₂⟩, rfl⟩
    by_cases hi : i₁ = i₂
    · subst hi
      by_cases ht : t₁ = t₂
      · subst ht; simp [CStarMatrix.one_apply]
      · rw [cstarMatrixBlockHom_apply_of_copy_ne _ _ _ _ _ _ ht, CStarMatrix.one_apply,
          ite_eq_right (f.injective.ne (by grind))]
    · rw [cstarMatrixBlockHom_apply_of_block_ne _ _ _ hi, CStarMatrix.one_apply,
        ite_eq_right (f.injective.ne (by grind))]

private theorem rawBlockDiag_piSingle_single [DecidableEq ι]
    (r : ι → ℕ) [DecidableEq (Σ i, n i × Fin (r i))]
    (i : ι) [DecidableEq (n i)] (p q : n i) (c : ℂ) :
    rawBlockDiag r (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q c))) =
      ∑ t : Fin (r i), Matrix.single (⟨i, p, t⟩ : Σ i', n i' × Fin (r i')) ⟨i, q, t⟩ c := by
  ext ⟨i₁, p₁, t₁⟩ ⟨i₂, p₂, t₂⟩
  simp only [Matrix.sum_apply, Matrix.single_apply]
  by_cases hi : i₁ = i₂
  · subst hi; rw [rawBlockDiag, Matrix.blockDiagonal'_apply_eq]
    by_cases hii : i₁ = i
    · subst hii; simp only [Pi.single_eq_same, Equiv.symm_apply_apply]
      by_cases ht : t₁ = t₂
      · subst ht; rw [Fintype.sum_eq_single t₁ fun _ _ ↦ by grind]; simp [Matrix.single_apply]
      · rw [Finset.sum_eq_zero fun _ _ ↦ by grind, Matrix.blockDiagonal_apply_ne _ _ _ ht]
    · simp only [Pi.single_eq_of_ne hii, CStarMatrix.ofMatrix_symm_zero, ← Pi.zero_def,
        Matrix.blockDiagonal_zero, Matrix.zero_apply]
      exact (Finset.sum_eq_zero fun _ _ ↦
        ite_eq_right fun h ↦ hii (congrArg Sigma.fst h.1).symm).symm
  · rw [rawBlockDiag, Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    exact (Finset.sum_eq_zero fun _ _ ↦ by grind).symm

/-- Action of `TauCeti.cstarMatrixBlockHom` on a matrix unit `Matrix.single p q c` in source block
`i`: it is the sum of the `r i` orthogonal matrix units
`Matrix.single (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) c` in `CStarMatrix M M ℂ`. -/
theorem cstarMatrixBlockHom_piSingle_single [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (i : ι) [DecidableEq (n i)] (p q : n i) (c : ℂ) :
    cstarMatrixBlockHom r f (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q c))) =
      CStarMatrix.ofMatrix (∑ t : Fin (r i), Matrix.single (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) c) := by
  classical
  rw [cstarMatrixBlockHom_eq_ofMatrix_glEmbedding, rawBlockDiag_piSingle_single, map_sum]
  simp

/-- The **product block-diagonal `⋆`-homomorphism** realizing a multiplicity matrix
`H : Matrix κ ι ℕ` along a family of injections `f j : (Σ i, n i × Fin (H j i)) ↪ m j`. -/
def cstarMatrixPiBlockHom [Fintype ι] [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j) :
    (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ) where
  toFun x j := cstarMatrixBlockHom (H j) (f j) x
  map_smul' c x := funext fun j ↦ map_smul (cstarMatrixBlockHom (H j) (f j)) c x
  map_zero' := funext fun j ↦ map_zero (cstarMatrixBlockHom (H j) (f j))
  map_add' x y := funext fun j ↦ map_add (cstarMatrixBlockHom (H j) (f j)) x y
  map_mul' x y := funext fun j ↦ map_mul (cstarMatrixBlockHom (H j) (f j)) x y
  map_star' x := funext fun j ↦ map_star (cstarMatrixBlockHom (H j) (f j)) x

/-- Coordinate evaluation of `TauCeti.cstarMatrixPiBlockHom`. -/
@[simp]
theorem cstarMatrixPiBlockHom_apply [Fintype ι] [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (j : κ) :
    cstarMatrixPiBlockHom H f x j = cstarMatrixBlockHom (H j) (f j) x :=
  (rfl)

/-- `cstarMatrixPiBlockHom H f` preserves the identity if and only if every coordinate embedding
`f j` is surjective. -/
theorem cstarMatrixPiBlockHom_one_eq_one_iff [Fintype ι] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j) :
    cstarMatrixPiBlockHom H f 1 = 1 ↔ ∀ j, Function.Surjective (f j) := by
  simp_rw [funext_iff, cstarMatrixPiBlockHom_apply, Pi.one_apply,
    cstarMatrixBlockHom_one_eq_one_iff]

/-- Entry `(j, i)` of the multiplicity matrix of `cstarMatrixPiBlockHom H f` equals `H j i` whenever
`n i` is nonempty, and `0` when `n i` is empty. -/
theorem multiplicityMatrix_cstarMatrixPiBlockHom_apply [Fintype ι] [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j) (j : κ) (i : ι) :
    (cstarMatrixPiBlockHom H f).multiplicityMatrix j i =
      if Fintype.card (n i) ≠ 0 then H j i else 0 := by
  classical
  split_ifs with hcard
  · obtain ⟨p⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    apply Nat.cast_injective (R := ℂ)
    rw [(cstarMatrixPiBlockHom H f).natCast_multiplicityMatrix_apply_eq_trace_single j i p,
      cstarMatrixPiBlockHom_apply, cstarMatrixBlockHom_piSingle_single, Equiv.symm_apply_apply,
      Matrix.trace_sum]
    simp [Matrix.trace]
  · have _ : IsEmpty (n i) := Fintype.card_eq_zero_iff.mp (Classical.not_not.mp hcard)
    exact (cstarMatrixPiBlockHom H f).multiplicityMatrix_apply_of_isEmpty_source j i

/-- When `H` vanishes on empty source blocks, `cstarMatrixPiBlockHom H f` has multiplicity matrix
`H`. -/
theorem multiplicityMatrix_cstarMatrixPiBlockHom_of_forall_isEmpty_eq_zero
    [Fintype ι] [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j)
    (hEmpty : ∀ j i, IsEmpty (n i) → H j i = 0) :
    (cstarMatrixPiBlockHom H f).multiplicityMatrix = H := by
  ext j i
  rw [multiplicityMatrix_cstarMatrixPiBlockHom_apply]
  rcases isEmpty_or_nonempty (n i) with hE | _
  · have _ := hE
    simp [Fintype.card_eq_zero, hEmpty j i hE]
  · simp [Fintype.card_ne_zero]

/-- When every source block `n i` is nonempty, `cstarMatrixPiBlockHom H f` has multiplicity matrix
`H`. -/
@[simp]
theorem multiplicityMatrix_cstarMatrixPiBlockHom [Fintype ι] [∀ i, Fintype (n i)]
    [∀ i, Nonempty (n i)] [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j) :
    (cstarMatrixPiBlockHom H f).multiplicityMatrix = H :=
  multiplicityMatrix_cstarMatrixPiBlockHom_of_forall_isEmpty_eq_zero H f fun _ _ hE ↦
    (not_nonempty_iff.mpr hE inferInstance).elim

/-- **Realizability of multiplicity matrices** (including possibly empty blocks): a matrix
`H : Matrix κ ι ℕ` is the multiplicity matrix of some `⋆`-homomorphism if and only if `H` vanishes
on empty source blocks and satisfies the block-size inequality at every target block `j`. -/
theorem exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff [Fintype ι]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] (H : Matrix κ ι ℕ) :
    (∃ φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ),
        φ.multiplicityMatrix = H) ↔
      (∀ j i, IsEmpty (n i) → H j i = 0) ∧
        ∀ j, ∑ i, H j i * Fintype.card (n i) ≤ Fintype.card (m j) := by
  classical
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨fun j i _ ↦ ?_, fun j ↦ ?_⟩, fun ⟨hEmpty, hle⟩ ↦ ?_⟩
  · rw [← hφ, φ.multiplicityMatrix_apply_of_isEmpty_source]
  · rw [← hφ]; exact φ.sum_multiplicityMatrix_mul_card_le j
  · have hemb (j : κ) : Nonempty ((Σ i, n i × Fin (H j i)) ↪ m j) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa [Fintype.card_sigma, Fintype.card_prod, mul_comm] using hle j
    exact ⟨cstarMatrixPiBlockHom H (fun j ↦ Classical.choice (hemb j)),
      multiplicityMatrix_cstarMatrixPiBlockHom_of_forall_isEmpty_eq_zero H _ hEmpty⟩

/-- **Realizability of multiplicity matrices**: when every source block `n i` is nonempty, a matrix
`H : Matrix κ ι ℕ` is the multiplicity matrix of some `⋆`-homomorphism if and only if
`∑ i, H j i * Fintype.card (n i) ≤ Fintype.card (m j)` for every `j`. -/
theorem exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff_of_nonempty [Fintype ι]
    [∀ i, Fintype (n i)] [∀ i, Nonempty (n i)] [∀ j, Fintype (m j)] (H : Matrix κ ι ℕ) :
    (∃ φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ),
        φ.multiplicityMatrix = H) ↔
      ∀ j, ∑ i, H j i * Fintype.card (n i) ≤ Fintype.card (m j) := by
  rw [exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff]
  exact and_iff_right fun _ _ hE ↦ (not_nonempty_iff.mpr hE inferInstance).elim

/-- **Realizability by unital `⋆`-homomorphisms** (including possibly empty blocks): `H` is the
multiplicity matrix of a unital `⋆`-homomorphism if and only if `H` vanishes on empty source blocks
and `∑ i, H j i * Fintype.card (n i) = Fintype.card (m j)` for every `j`. -/
theorem exists_starAlgHom_multiplicityMatrix_eq_iff [Fintype ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (H : Matrix κ ι ℕ) :
    (∃ φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ),
        φ.toNonUnitalStarAlgHom.multiplicityMatrix = H) ↔
      (∀ j i, IsEmpty (n i) → H j i = 0) ∧
        ∀ j, ∑ i, H j i * Fintype.card (n i) = Fintype.card (m j) := by
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨fun j i _ ↦ ?_, fun j ↦ ?_⟩, fun ⟨hEmpty, heq⟩ ↦ ?_⟩
  · rw [← hφ, φ.toNonUnitalStarAlgHom.multiplicityMatrix_apply_of_isEmpty_source]
  · rw [← hφ]; exact φ.sum_multiplicityMatrix_mul_card_eq j
  · obtain ⟨φ, hφ⟩ := (exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff H).mpr
      ⟨hEmpty, fun j ↦ (heq j).le⟩
    have h1 : φ 1 = 1 :=
      φ.map_one_eq_one_iff_sum_multiplicityMatrix_eq.mpr fun j ↦ by rw [hφ, heq j]
    have hcomm (c : ℂ) : φ (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h1]
    exact ⟨{ φ with map_one' := h1, commutes' := hcomm }, hφ⟩

/-- **Realizability by unital `⋆`-homomorphisms**: when every source block `n i` is nonempty, `H`
is the multiplicity matrix of a unital `⋆`-homomorphism if and only if
`∑ i, H j i * Fintype.card (n i) = Fintype.card (m j)` for every `j`. -/
theorem exists_starAlgHom_multiplicityMatrix_eq_iff_of_nonempty [Fintype ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (H : Matrix κ ι ℕ) :
    (∃ φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ),
        φ.toNonUnitalStarAlgHom.multiplicityMatrix = H) ↔
      ∀ j, ∑ i, H j i * Fintype.card (n i) = Fintype.card (m j) := by
  rw [exists_starAlgHom_multiplicityMatrix_eq_iff]
  exact and_iff_right fun _ _ hE ↦ (not_nonempty_iff.mpr hE inferInstance).elim

end Realization

end TauCeti

end
