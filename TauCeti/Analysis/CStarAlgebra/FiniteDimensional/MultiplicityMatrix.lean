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
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import TauCeti.Algebra.Lie.GeneralLinear.Embedding
import TauCeti.Algebra.Star.Pi
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.EuclideanLin
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.LinearAlgebra.Matrix.Submatrix
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Classification of `⋆`-homomorphisms between finite direct sums of matrix C⋆-algebras

Every `⋆`-homomorphism
`φ : (∀ i : ι, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j : κ, CStarMatrix (m j) (m j) ℂ)`
between finite direct sums of full complex matrix C⋆-algebras is classified up to unitary conjugacy
in the target by its nonnegative-integer *multiplicity matrix*
`φ.multiplicityMatrix : Matrix κ ι ℕ`, whose `(j, i)` entry records how many orthogonal copies of
the `i`-th source block `φ` places inside the `j`-th target block. Equivalently, when `n i` is
nonempty, `φ.multiplicityMatrix j i` is the rank (and the trace) of the image in target block `j`
of any minimal diagonal projection `Matrix.single p p 1` of source block `i`; when `n i` is empty,
the source block is zero and the entry vanishes.

This file establishes the algebraic and Hilbert-space classification of such `⋆`-homomorphisms:

* **Multiplicity matrix and trace/rank formulas**: `NonUnitalStarAlgHom.multiplicityMatrix`,
  together with `NonUnitalStarAlgHom.multiplicityMatrix_apply`,
  `NonUnitalStarAlgHom.multiplicityMatrix_apply_eq_rank_single`,
  `NonUnitalStarAlgHom.natCast_multiplicityMatrix_apply_eq_trace_single`, and
  `NonUnitalStarAlgHom.multiplicityMatrix_mul_card_eq_rank`.
* **Block-size inequality and unitality**: for finite `ι`,
  `∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j)` for each `j`
  (`NonUnitalStarAlgHom.sum_multiplicityMatrix_mul_card_le`), with equality for all `j` if and only
  if `φ 1 = 1` (`NonUnitalStarAlgHom.map_one_eq_one_iff_sum_multiplicityMatrix_eq`).
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
  units along `f j`. A matrix `H` is realized by a `⋆`-homomorphism (respectively, a unital
  `⋆`-homomorphism) if and only if `H` vanishes on empty source blocks and the block-size
  inequalities (respectively, equalities) hold
  (`TauCeti.exists_nonUnitalStarAlgHom_multiplicityMatrix_eq_iff`,
  `TauCeti.exists_starAlgHom_multiplicityMatrix_eq_iff`; see also the `_of_nonempty` variants when
  every `n i` is nonempty).
* **Uniqueness up to unitary conjugacy and functoriality**: every `φ` is unitarily conjugate in the
  target to `TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f`
  (`NonUnitalStarAlgHom.exists_unitary_conj_cstarMatrixPiBlockHom`). Consequently, two
  `⋆`-homomorphisms have equal multiplicity matrices if and only if they are unitarily conjugate in
  the target (`NonUnitalStarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq`), and if and only
  if they are approximately unitarily equivalent
  (`NonUnitalStarAlgHom.approximatelyUnitarilyEquivalent_iff_multiplicityMatrix_eq`). Composition of
  `⋆`-homomorphisms multiplies their multiplicity matrices
  (`NonUnitalStarAlgHom.multiplicityMatrix_comp`).
* **Single-block corollaries**: a unital `⋆`-homomorphism
  `CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` exists if and only if
  `Fintype.card n ∣ Fintype.card m` (`TauCeti.nonempty_starAlgHom_cstarMatrix_iff`), and any two
  such unital maps are unitarily conjugate (`StarAlgHom.exists_unitary_conj_cstarMatrix`).

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

private theorem isIdempotentElem_ofMatrix_symm_map
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    {x : ∀ i, CStarMatrix (n i) (n i) ℂ} (hx : IsIdempotentElem x) (j : κ) :
    IsIdempotentElem (CStarMatrix.ofMatrix.symm (φ x j)) := by
  rw [IsIdempotentElem, ← CStarMatrix.ofMatrix_symm_mul, ← Pi.mul_apply, ← map_mul, hx.eq]

private theorem trace_ofMatrix_symm_map_eq_rank
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    {x : ∀ i, CStarMatrix (n i) (n i) ℂ} (hx : IsIdempotentElem x) (j : κ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (φ x j)) =
      (Matrix.rank (CStarMatrix.ofMatrix.symm (φ x j)) : ℂ) := by
  classical
  have hid := isIdempotentElem_ofMatrix_symm_map φ hx j
  have hlin : IsIdempotentElem (Matrix.toLin' (CStarMatrix.ofMatrix.symm (φ x j))) :=
    hid.map Matrix.toLinAlgEquiv'
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ hlin).trace,
    Matrix.toLin'_apply', Matrix.rank]

private theorem isIdempotentElem_piSingle_one [DecidableEq ι] (i : ι) [DecidableEq (n i)] :
    IsIdempotentElem
      (Pi.single i (1 : CStarMatrix (n i) (n i) ℂ) : ∀ i', CStarMatrix (n i') (n i') ℂ) :=
  IsIdempotentElem.one.map (MulHom.single i)

private theorem piSingle_ofMatrix_single_mul [DecidableEq ι] (i : ι) [DecidableEq (n i)]
    (a b c : n i) :
    (Pi.single i (CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ))) :
        ∀ i', CStarMatrix (n i') (n i') ℂ) *
      Pi.single i (CStarMatrix.ofMatrix (Matrix.single b c 1)) =
      Pi.single i (CStarMatrix.ofMatrix (Matrix.single a c 1)) := by
  rw [← Pi.single_mul]
  congr 1
  apply CStarMatrix.ofMatrix.symm.injective
  simp

private theorem trace_map_single_eq_of_index [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p q : n i) :
    Matrix.trace (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) =
      Matrix.trace (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single q q 1))) j)) := by
  rw [← piSingle_ofMatrix_single_mul i p q p, ← piSingle_ofMatrix_single_mul i q p q,
    map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, CStarMatrix.ofMatrix_symm_mul,
    CStarMatrix.ofMatrix_symm_mul, Matrix.trace_mul_comm]

private theorem piSingle_one_eq_sum_single [DecidableEq ι] (i : ι) [DecidableEq (n i)] :
    (Pi.single i (1 : CStarMatrix (n i) (n i) ℂ) : ∀ i', CStarMatrix (n i') (n i') ℂ) =
      ∑ q : n i, Pi.single i (CStarMatrix.ofMatrix (Matrix.single q q 1)) := by
  funext i'
  by_cases hi : i' = i
  · subst hi
    apply CStarMatrix.ofMatrix.symm.injective
    simp [Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum, Matrix.sum_single_one]
  · simp [Finset.sum_apply, Pi.single_eq_of_ne hi]

private theorem rank_map_piSingle_one_eq_rank_single_mul_card [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) [DecidableEq (n i)] (p : n i) :
    Matrix.rank (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)) =
      Matrix.rank (CStarMatrix.ofMatrix.symm
        (φ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) j)) *
        Fintype.card (n i) := by
  apply Nat.cast_injective (R := ℂ)
  rw [← trace_ofMatrix_symm_map_eq_rank φ (isIdempotentElem_piSingle_one i) j, Nat.cast_mul,
    ← trace_ofMatrix_symm_map_eq_rank φ (piSingle_ofMatrix_single_mul i p p p) j,
    piSingle_one_eq_sum_single i, map_sum, Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum,
    Matrix.trace_sum]
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
    trace_ofMatrix_symm_map_eq_rank φ (piSingle_ofMatrix_single_mul i p p p) j]

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
    trace_ofMatrix_symm_map_eq_rank φ (isIdempotentElem_piSingle_one i) j]

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
  rw [Nat.cast_sum, ← trace_map_one_eq_sum φ j, trace_ofMatrix_symm_map_eq_rank φ .one j]

/-- **Block-size inequality**: for each target block `j`,
`∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j)`. -/
theorem sum_multiplicityMatrix_mul_card_le [Fintype ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    ∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) ≤ Fintype.card (m j) := by
  classical
  rw [sum_multiplicityMatrix_mul_card_eq_rank_map_one φ j]
  exact Matrix.rank_le_card_width _

/-- **Unitality criterion**: `φ` preserves the unit (`φ 1 = 1`) if and only if equality holds in
the block-size inequality at every target block `j`. -/
theorem map_one_eq_one_iff_sum_multiplicityMatrix_eq [Fintype ι]
    [∀ i, DecidableEq (n i)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    φ 1 = 1 ↔ ∀ j, ∑ i, φ.multiplicityMatrix j i * Fintype.card (n i) = Fintype.card (m j) := by
  refine ⟨fun h j ↦ ?_, fun h ↦ funext fun j ↦ ?_⟩
  · rw [sum_multiplicityMatrix_mul_card_eq_rank_map_one φ j, h]
    rw [Pi.one_apply, CStarMatrix.ofMatrix_symm_one, Matrix.rank_one]
  · set P : Matrix (m j) (m j) ℂ := CStarMatrix.ofMatrix.symm (φ 1 j)
    have hP : IsIdempotentElem P := isIdempotentElem_ofMatrix_symm_map φ .one j
    have hQ : IsIdempotentElem (1 - P) := hP.one_sub
    have htr : (1 - P).trace = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_one, trace_map_one_eq_sum φ j, ← Nat.cast_sum, h j,
        sub_self]
    have hzero := Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero hQ htr
    apply CStarMatrix.ofMatrix.symm.injective
    rw [Pi.one_apply, CStarMatrix.ofMatrix_symm_one]
    exact (sub_eq_zero.mp hzero).symm

/-- Row `j` of `φ.multiplicityMatrix` vanishes if and only if the `j`-th target component of `φ`
is identically zero. -/
theorem multiplicityMatrix_row_eq_zero_iff [Finite ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (∀ i, φ.multiplicityMatrix j i = 0) ↔ ∀ x, φ x j = 0 := by
  classical
  cases nonempty_fintype ι
  refine ⟨fun hj x ↦ ?_, fun hj i ↦ by simp [multiplicityMatrix_apply, hj]⟩
  have htr1 : (CStarMatrix.ofMatrix.symm (φ 1 j)).trace = 0 := by
    rw [trace_map_one_eq_sum φ j]
    simp [hj]
  have h1 : φ 1 j = 0 := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [CStarMatrix.ofMatrix_symm_zero]
    exact Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero
      (isIdempotentElem_ofMatrix_symm_map φ .one j) htr1
  rw [← mul_one x, map_mul, Pi.mul_apply, h1, mul_zero]

/-- Column `i` of `φ.multiplicityMatrix` vanishes if and only if `φ` vanishes on the `i`-th source
summand. -/
theorem multiplicityMatrix_col_eq_zero_iff [DecidableEq ι]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (i : ι) :
    (∀ j, φ.multiplicityMatrix j i = 0) ↔ ∀ a, φ (Pi.single i a) = 0 := by
  classical
  refine ⟨fun hi a ↦ funext fun j ↦ ?_, fun hi j ↦ by simp [multiplicityMatrix_apply, hi]⟩
  have htr : (CStarMatrix.ofMatrix.symm (φ (Pi.single i 1) j)).trace = 0 := by
    rw [← natCast_multiplicityMatrix_mul_card_eq_trace φ j i, hi j, zero_mul, Nat.cast_zero]
  have he : φ (Pi.single i 1) j = 0 := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [CStarMatrix.ofMatrix_symm_zero]
    exact Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero
      (isIdempotentElem_ofMatrix_symm_map φ (isIdempotentElem_piSingle_one i) j) htr
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
          funext i'
          by_cases hi : i' = i
          · subst hi
            apply CStarMatrix.ofMatrix.symm.injective
            simp [Matrix.single_mul_mul_single, hpq]
          · simp [Pi.single_eq_of_ne hi]
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

private theorem id_toNonUnitalStarAlgHom :
    (StarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ) := by
  ext; simp

/-- Entrywise formula for the multiplicity matrix of the identity unital `⋆`-homomorphism: `1` on
the diagonal at nonempty blocks, and `0` elsewhere. -/
theorem multiplicityMatrix_id_apply [DecidableEq ι] (i' i : ι) :
    (StarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom.multiplicityMatrix
        i' i =
      if i' = i ∧ Fintype.card (n i) ≠ 0 then 1 else 0 := by
  rw [id_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.multiplicityMatrix_id_apply]

/-- When every block index type `n i` is nonempty, the identity unital `⋆`-homomorphism has the
identity multiplicity matrix. -/
@[simp]
theorem multiplicityMatrix_id [DecidableEq ι] [∀ i, Nonempty (n i)] :
    (StarAlgHom.id ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom.multiplicityMatrix =
      1 := by
  rw [id_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.multiplicityMatrix_id]

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

private theorem rawBlockDiag_zero [DecidableEq ι] (r : ι → ℕ) :
    rawBlockDiag r (0 : ∀ i, CStarMatrix (n i) (n i) ℂ) = 0 := by
  simp [rawBlockDiag, ← Pi.zero_def]

private theorem rawBlockDiag_add [DecidableEq ι] (r : ι → ℕ)
    (x y : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    rawBlockDiag r (x + y) = rawBlockDiag r x + rawBlockDiag r y := by
  rw [rawBlockDiag, rawBlockDiag, rawBlockDiag, ← Matrix.blockDiagonal'_add]
  refine congrArg Matrix.blockDiagonal' (funext fun i ↦ ?_)
  simp only [Pi.add_apply, CStarMatrix.ofMatrix_symm_add, ← Pi.add_def, Matrix.blockDiagonal_add]

private theorem rawBlockDiag_smul [DecidableEq ι] (r : ι → ℕ)
    (c : ℂ) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    rawBlockDiag r (c • x) = c • rawBlockDiag r x := by
  rw [rawBlockDiag, rawBlockDiag, ← Matrix.blockDiagonal'_smul]
  refine congrArg Matrix.blockDiagonal' (funext fun i ↦ ?_)
  simp only [Pi.smul_apply, CStarMatrix.ofMatrix_symm_smul, ← Pi.smul_def,
    Matrix.blockDiagonal_smul]

private theorem rawBlockDiag_mul [DecidableEq ι] [∀ i, Fintype (n i)] (r : ι → ℕ)
    [Fintype (Σ i, n i × Fin (r i))] (x y : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    rawBlockDiag r (x * y) = rawBlockDiag r x * rawBlockDiag r y := by
  ext ⟨i₁, p₁, t₁⟩ ⟨i₂, p₂, t₂⟩
  let emb : n i₁ ↪ Σ i, n i × Fin (r i) := ⟨fun q ↦ ⟨i₁, q, t₁⟩, fun _ _ h ↦ by grind⟩
  have hemb (q : n i₁) : emb q = ⟨i₁, q, t₁⟩ := rfl
  have hsub : (rawBlockDiag r x * rawBlockDiag r y) ⟨i₁, p₁, t₁⟩ ⟨i₂, p₂, t₂⟩ =
      ∑ q : n i₁, x i₁ p₁ q * rawBlockDiag r y ⟨i₁, q, t₁⟩ ⟨i₂, p₂, t₂⟩ := by
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb)),
      Finset.sum_map]
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hemb]
      exact congrArg (· * _) (by simp [rawBlockDiag])
    · rintro ⟨i', q, t'⟩ _ hnot
      have hz : rawBlockDiag r x ⟨i₁, p₁, t₁⟩ ⟨i', q, t'⟩ = 0 := by
        by_cases hi : i₁ = i'
        · subst hi
          have ht : t₁ ≠ t' := fun ht ↦
            hnot (Finset.mem_map.mpr ⟨q, Finset.mem_univ _, by simp [hemb, ht]⟩)
          rw [rawBlockDiag, Matrix.blockDiagonal'_apply_eq,
            Matrix.blockDiagonal_apply_ne _ _ _ ht]
        · rw [rawBlockDiag, Matrix.blockDiagonal'_apply_ne _ _ _ hi]
      rw [hz, zero_mul]
  rw [hsub]
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases ht : t₁ = t₂
    · subst ht
      rw [rawBlockDiag, Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal_apply_eq,
        Pi.mul_apply, CStarMatrix.ofMatrix_symm_mul, Matrix.mul_apply]
      simp [rawBlockDiag]
    · rw [rawBlockDiag, Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal_apply_ne _ _ _ ht]
      refine (Finset.sum_eq_zero fun q _ ↦ ?_).symm
      rw [rawBlockDiag, Matrix.blockDiagonal'_apply_eq,
        Matrix.blockDiagonal_apply_ne _ _ _ ht, mul_zero]
  · simp [rawBlockDiag, fun M a b ↦ Matrix.blockDiagonal'_apply_ne M a b hi]

/-- The **block-diagonal `⋆`-homomorphism** into a single matrix C⋆-algebra `CStarMatrix M M ℂ`
determined by multiplicities `r : ι → ℕ` and an injection
`f : (Σ i, n i × Fin (r i)) ↪ M`: each source block `x i` is repeated `r i` times along the
coordinates in the image of `f`, with zeros in the complementary corner. -/
def cstarMatrixBlockHom [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) :
    (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] CStarMatrix M M ℂ :=
  letI := Classical.decEq ι
  letI := Classical.decEq M
  letI : DecidableEq (Σ i, n i × Fin (r i)) := Classical.decEq _
  haveI : Finite (Σ i, n i × Fin (r i)) := Finite.of_injective f f.injective
  letI : Fintype (Σ i, n i × Fin (r i)) := Fintype.ofFinite _
  { toFun x := CStarMatrix.ofMatrix (glEmbedding ℂ f (rawBlockDiag r x))
    map_smul' c x := CStarMatrix.ofMatrix.symm.injective <| by simp [rawBlockDiag_smul]
    map_zero' := CStarMatrix.ofMatrix.symm.injective <| by simp [rawBlockDiag_zero]
    map_add' x y := CStarMatrix.ofMatrix.symm.injective <| by simp [rawBlockDiag_add]
    map_mul' x y := CStarMatrix.ofMatrix.symm.injective <| by
      simp only [Equiv.symm_apply_apply, CStarMatrix.ofMatrix_symm_mul, glEmbedding_apply,
        rawBlockDiag_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((1 : Matrix M M ℂ).submatrix f id),
        Matrix.submatrix_one_mul_submatrix_one f, Matrix.one_mul]
    map_star' x := CStarMatrix.ofMatrix.symm.injective <| by
      simp [rawBlockDiag, glEmbedding_apply, Matrix.mul_assoc] }

private theorem cstarMatrixBlockHom_apply_map_map [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (x : ∀ i, CStarMatrix (n i) (n i) ℂ)
    (a b : Σ i, n i × Fin (r i)) :
    cstarMatrixBlockHom r f x (f a) (f b) = @rawBlockDiag ι n (Classical.decEq ι) r x a b := by
  simp [cstarMatrixBlockHom]

/-- Evaluating `cstarMatrixBlockHom r f x` at matching block `i` and copy `t` along `f` recovers
the `(p, q)` entry of `x i`. -/
@[simp]
theorem cstarMatrixBlockHom_apply_same [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (i : ι) (p q : n i) (t : Fin (r i)) :
    cstarMatrixBlockHom r f x (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) = x i p q := by
  let _ := Classical.decEq ι
  rw [cstarMatrixBlockHom_apply_map_map]
  have hdec : @rawBlockDiag ι n (Classical.decEq ι) r = rawBlockDiag r := by congr!
  rw [hdec]; simp [rawBlockDiag]

/-- Entries of `cstarMatrixBlockHom r f x` between distinct source blocks `i₁ ≠ i₂` vanish. -/
theorem cstarMatrixBlockHom_apply_of_block_ne [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) {i₁ i₂ : ι} (h : i₁ ≠ i₂)
    (p : n i₁) (q : n i₂) (t₁ : Fin (r i₁)) (t₂ : Fin (r i₂)) :
    cstarMatrixBlockHom r f x (f ⟨i₁, p, t₁⟩) (f ⟨i₂, q, t₂⟩) = 0 := by
  let _ := Classical.decEq ι
  rw [cstarMatrixBlockHom_apply_map_map]
  have hdec : @rawBlockDiag ι n (Classical.decEq ι) r = rawBlockDiag r := by congr!
  rw [hdec, rawBlockDiag, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- Entries of `cstarMatrixBlockHom r f x` between distinct copies `t₁ ≠ t₂` of block `i` vanish. -/
theorem cstarMatrixBlockHom_apply_of_copy_ne [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (i : ι) (p q : n i) {t₁ t₂ : Fin (r i)} (h : t₁ ≠ t₂) :
    cstarMatrixBlockHom r f x (f ⟨i, p, t₁⟩) (f ⟨i, q, t₂⟩) = 0 := by
  let _ := Classical.decEq ι
  rw [cstarMatrixBlockHom_apply_map_map]
  have hdec : @rawBlockDiag ι n (Classical.decEq ι) r = rawBlockDiag r := by congr!
  rw [hdec, rawBlockDiag, Matrix.blockDiagonal'_apply_eq,
    Matrix.blockDiagonal_apply_ne _ _ _ h]

/-- Rows of `cstarMatrixBlockHom r f x` outside `Set.range f` vanish. -/
theorem cstarMatrixBlockHom_apply_of_notMem_range_left [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) {z₁ : M} (hz₁ : z₁ ∉ Set.range f) (z₂ : M) :
    cstarMatrixBlockHom r f x z₁ z₂ = 0 := by
  have : Finite (Σ i, n i × Fin (r i)) := Finite.of_injective f f.injective
  let _ : Fintype (Σ i, n i × Fin (r i)) := Fintype.ofFinite _
  let _ := Classical.decEq M
  let _ : DecidableEq (Σ i, n i × Fin (r i)) := Classical.decEq _
  simp [cstarMatrixBlockHom, glEmbedding_apply_apply_of_notMem_range_left f _ hz₁]

/-- Columns of `cstarMatrixBlockHom r f x` outside `Set.range f` vanish. -/
theorem cstarMatrixBlockHom_apply_of_notMem_range_right [∀ i, Fintype (n i)] [Fintype M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (z₁ : M) {z₂ : M} (hz₂ : z₂ ∉ Set.range f) :
    cstarMatrixBlockHom r f x z₁ z₂ = 0 := by
  have : Finite (Σ i, n i × Fin (r i)) := Finite.of_injective f f.injective
  let _ : Fintype (Σ i, n i × Fin (r i)) := Fintype.ofFinite _
  let _ := Classical.decEq M
  let _ : DecidableEq (Σ i, n i × Fin (r i)) := Classical.decEq _
  simp [cstarMatrixBlockHom, glEmbedding_apply_apply_of_notMem_range_right f _ _ hz₂]

/-- When `f` is surjective, `cstarMatrixBlockHom r f` preserves the identity. -/
theorem cstarMatrixBlockHom_one_of_surjective [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (hf : Function.Surjective f) :
    cstarMatrixBlockHom r f 1 = 1 := by
  ext z₁ z₂
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

/-- Action of `TauCeti.cstarMatrixBlockHom` on a matrix unit `Matrix.single p q c` in source block
`i`: it is the sum of the `r i` orthogonal matrix units
`Matrix.single (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) c` in `CStarMatrix M M ℂ`. -/
theorem cstarMatrixBlockHom_piSingle_single [DecidableEq ι]
    [∀ i, Fintype (n i)] [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (i : ι) [DecidableEq (n i)] (p q : n i) (c : ℂ) :
    cstarMatrixBlockHom r f (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q c))) =
      CStarMatrix.ofMatrix (∑ t : Fin (r i), Matrix.single (f ⟨i, p, t⟩) (f ⟨i, q, t⟩) c) := by
  let _ : DecidableEq (Σ i', n i' × Fin (r i')) := Classical.decEq _
  have : Finite (Σ i', n i' × Fin (r i')) := Finite.of_injective f f.injective
  let _ : Fintype (Σ i', n i' × Fin (r i')) := Fintype.ofFinite _
  have hdec : @rawBlockDiag ι n (Classical.decEq ι) r = rawBlockDiag r := by congr!
  have hraw : rawBlockDiag r (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q c))) =
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
  simp only [cstarMatrixBlockHom, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, hdec,
    hraw, map_sum, glEmbedding_single]
  congr!

/-- The **product block-diagonal `⋆`-homomorphism** realizing a multiplicity matrix
`H : Matrix κ ι ℕ` along a family of injections `f j : (Σ i, n i × Fin (H j i)) ↪ m j`. -/
def cstarMatrixPiBlockHom [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
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
theorem cstarMatrixPiBlockHom_apply [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (H : Matrix κ ι ℕ) (f : ∀ j, (Σ i, n i × Fin (H j i)) ↪ m j)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) (j : κ) :
    cstarMatrixPiBlockHom H f x j = cstarMatrixBlockHom (H j) (f j) x :=
  (rfl)

/-- Entry `(j, i)` of the multiplicity matrix of `cstarMatrixPiBlockHom H f` equals `H j i` whenever
`n i` is nonempty, and `0` when `n i` is empty. -/
theorem multiplicityMatrix_cstarMatrixPiBlockHom_apply [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
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
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
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
theorem multiplicityMatrix_cstarMatrixPiBlockHom [∀ i, Fintype (n i)] [∀ i, Nonempty (n i)]
    [∀ j, Fintype (m j)]
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

namespace NonUnitalStarAlgHom

section UnitaryConjugacy

variable {ι κ : Type*} {n : ι → Type*} {m : κ → Type*}

private def evalEuclideanHom [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ]
      (EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) :=
  (CStarMatrix.toEuclideanCLM (m j)).toNonUnitalStarAlgHom.comp
    ((Pi.evalNonUnitalStarAlgHom ℂ _ j).comp φ)

@[simp]
private theorem evalEuclideanHom_apply [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    evalEuclideanHom φ j x = CStarMatrix.toEuclideanCLM (m j) (φ x j) := by
  simp [evalEuclideanHom]

private theorem star_piSingle_ofMatrix_single [DecidableEq ι] (i : ι) [DecidableEq (n i)]
    (p q : n i) :
    star (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q (1 : ℂ))) :
        ∀ i', CStarMatrix (n i') (n i') ℂ) =
      Pi.single i (CStarMatrix.ofMatrix (Matrix.single q p 1)) := by
  rw [← Pi.single_star]
  congr 1
  exact CStarMatrix.ofMatrix.symm.injective (by simp)

private theorem piSingle_mul_of_ne [DecidableEq ι] [∀ i, Fintype (n i)]
    {i₁ i₂ : ι} (h : i₁ ≠ i₂) (a : CStarMatrix (n i₁) (n i₁) ℂ)
    (b : CStarMatrix (n i₂) (n i₂) ℂ) :
    (Pi.single i₁ a : ∀ i, CStarMatrix (n i) (n i) ℂ) * Pi.single i₂ b = 0 := by
  rw [← Pi.single_mul_left, Pi.single_eq_of_ne h, mul_zero, Pi.single_zero]

private theorem finrank_range_evalEuclideanHom_single [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (h : Nonempty (n i)) :
    Module.finrank ℂ (LinearMap.range (evalEuclideanHom φ j
      (Pi.single i (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1)))).toLinearMap) =
      φ.multiplicityMatrix j i := by
  rw [evalEuclideanHom_apply, CStarMatrix.finrank_range_toEuclideanCLM,
    ← φ.multiplicityMatrix_apply_eq_rank_single j i h.some]

private def minimalRangeBasis [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (h : Nonempty (n i)) :
    OrthonormalBasis (Fin (φ.multiplicityMatrix j i)) ℂ
      (LinearMap.range (evalEuclideanHom φ j
        (Pi.single i (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1)))).toLinearMap) :=
  (stdOrthonormalBasis ℂ _).reindex
    (finCongr (finrank_range_evalEuclideanHom_single φ j i h))

private def partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (Σ i, n i × Fin (φ.multiplicityMatrix j i)) → EuclideanSpace ℂ (m j) :=
  fun ⟨i, p, t⟩ ↦
    let h : Nonempty (n i) := ⟨p⟩
    evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p h.some 1)))
      (minimalRangeBasis φ j i h t)

private theorem evalEuclideanHom_single_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (p q : n i) (a : Σ i', n i' × Fin (φ.multiplicityMatrix j i')) :
    evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)))
        (partialBasisVec φ j a) =
      if h : i = a.1 then
        if h ▸ q = a.2.1 then partialBasisVec φ j ⟨i, p, h ▸ a.2.2⟩ else 0
      else 0 := by
  rcases a with ⟨i', q', t'⟩
  dsimp only [partialBasisVec]
  rw [← mul_apply_eq_comp, ← map_mul]
  by_cases hi : i = i'
  · subst hi
    simp only [↓reduceDIte]
    by_cases hq : q = q'
    · subst hq; rw [piSingle_ofMatrix_single_mul]; simp
    · have hC : CStarMatrix.ofMatrix (Matrix.single p q (1 : ℂ)) *
          CStarMatrix.ofMatrix (Matrix.single q' (⟨q'⟩ : Nonempty (n i)).some 1) = 0 :=
        CStarMatrix.ofMatrix.symm.injective (by simp [hq])
      have hzero : (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q (1 : ℂ))) :
          ∀ k, CStarMatrix (n k) (n k) ℂ) *
          Pi.single i (CStarMatrix.ofMatrix (Matrix.single q' (⟨q'⟩ : Nonempty (n i)).some 1)) =
          0 := by rw [← Pi.single_mul, hC, Pi.single_zero]
      rw [hzero]; simp [hq]
  · rw [piSingle_mul_of_ne hi]; simp [hi]

private theorem orthonormal_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    Orthonormal ℂ (partialBasisVec φ j) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, p₁, t₁⟩ ⟨i₂, p₂, t₂⟩
  have hL : partialBasisVec φ j ⟨i₁, p₁, t₁⟩ =
      evalEuclideanHom φ j
        (Pi.single i₁ (CStarMatrix.ofMatrix (Matrix.single p₁ (⟨p₁⟩ : Nonempty (n i₁)).some 1)))
        (minimalRangeBasis φ j i₁ ⟨p₁⟩ t₁) := rfl
  rw [hL, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, star_piSingle_ofMatrix_single, evalEuclideanHom_single_partialBasisVec]
  by_cases hi : i₁ = i₂
  · subst hi; simp only [↓reduceDIte]
    by_cases hp : p₁ = p₂
    · subst hp; simp only [↓reduceIte, partialBasisVec]
      set h : Nonempty (n i₁) := ⟨p₁⟩
      set w := minimalRangeBasis φ j i₁ h t₂
      obtain ⟨u, hu⟩ := w.prop
      have hw : evalEuclideanHom φ j
          (Pi.single i₁ (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1))) w = w := by
        rw [← hu]
        simp only [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, ← map_mul,
          piSingle_ofMatrix_single_mul]
      rw [hw, ← Submodule.coe_inner,
        orthonormal_iff_ite.mp (minimalRangeBasis φ j i₁ h).orthonormal t₁ t₂]; simp
    · simp [hp]
  · simp [hi]

private theorem span_range_partialBasisVec_eq_range_one [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    Submodule.span ℂ (Set.range (partialBasisVec φ j)) =
      LinearMap.range (evalEuclideanHom φ j 1).toLinearMap := by
  cases nonempty_fintype ι
  apply Submodule.eq_of_le_of_finrank_eq
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨i, p, t⟩, rfl⟩
    refine ⟨partialBasisVec φ j ⟨i, p, t⟩, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, partialBasisVec, ← mul_apply_eq_comp,
      ← map_mul, one_mul]
  · rw [finrank_span_eq_card (orthonormal_partialBasisVec φ j).linearIndependent,
      evalEuclideanHom_apply, CStarMatrix.finrank_range_toEuclideanCLM,
      ← φ.sum_multiplicityMatrix_mul_card_eq_rank_map_one j]
    simp [Fintype.card_sigma, Fintype.card_prod, mul_comm]

private theorem evalEuclideanHom_eq_zero_of_notMem_range [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ)
    {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) {z : m j} (hz : z ∉ Set.range f)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    evalEuclideanHom φ j x (b z) = 0 := by
  have horth : Submodule.span ℂ (Set.range (partialBasisVec φ j)) ≤
      Submodule.orthogonal (ℂ ∙ b z) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, ← hb a]
    exact b.inner_eq_zero fun hfz ↦ hz ⟨a, hfz⟩
  have h1_mem : evalEuclideanHom φ j 1 (b z) ∈
      Submodule.span ℂ (Set.range (partialBasisVec φ j)) := by
    rw [span_range_partialBasisVec_eq_range_one]; exact ⟨b z, rfl⟩
  have h1_self : inner ℂ (evalEuclideanHom φ j 1 (b z)) (evalEuclideanHom φ j 1 (b z)) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, star_one, ← mul_apply_eq_comp, ← map_mul, one_mul]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (horth h1_mem)
  rw [← mul_one x, map_mul, mul_apply_eq_comp, inner_self_eq_zero.mp h1_self, map_zero]

private theorem toEuclideanCLM_blockHom_single_basisFun [DecidableEq ι]
    [∀ i, Fintype (n i)] {M : Type*} [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (i : ι) [DecidableEq (n i)]
    (p q : n i) (z : M) :
    CStarMatrix.toEuclideanCLM M
        (TauCeti.cstarMatrixBlockHom r f (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1))))
        (EuclideanSpace.basisFun M ℂ z) =
      ∑ t : Fin (r i),
        if z = f ⟨i, q, t⟩ then EuclideanSpace.basisFun M ℂ (f ⟨i, p, t⟩) else 0 := by
  rw [TauCeti.cstarMatrixBlockHom_piSingle_single, CStarMatrix.toEuclideanCLM_apply,
    Equiv.symm_apply_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Matrix.toEuclideanCLM_single_basisFun, one_smul]

private theorem elem_eq_sum_piSingle_single [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    x = ∑ i : ι, ∑ p : n i, ∑ q : n i,
      CStarMatrix.ofMatrix.symm (x i) p q •
        Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  funext i'
  by_cases hi : i' = i
  · subst hi; apply CStarMatrix.ofMatrix.symm.injective
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, CStarMatrix.smul_of,
      CStarMatrix.ofMatrix_symm_sum, Equiv.symm_apply_apply, Matrix.smul_single, smul_eq_mul,
      mul_one]
    exact Matrix.matrix_eq_sum_single _
  · simp [Finset.sum_apply, Pi.single_eq_of_ne hi]

private theorem intertwine_single_of_basis [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) (i : ι) (p q : n i) :
    (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) *
        CStarMatrix.toEuclideanCLM (m j)
          (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f
            (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)))) =
      evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1))) *
        (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) := by
  have hU (z : m j) : (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j))
      (EuclideanSpace.basisFun (m j) ℂ z) = b z := by simp [EuclideanSpace.basisFun_apply]
  have hfinj := f.injective
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (m j) ℂ).toBasis.ext fun z ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, mul_apply_eq_comp,
    hU z, toEuclideanCLM_blockHom_single_basisFun]
  by_cases hz : z ∈ Set.range f
  · rcases hz with ⟨⟨i', q', t'⟩, rfl⟩
    rw [hb, evalEuclideanHom_single_partialBasisVec]
    by_cases hi : i = i'
    · subst hi
      by_cases hq : q = q'
      · subst hq; rw [Fintype.sum_eq_single t' fun _ _ ↦ by grind]; simp [hb]
      · rw [Finset.sum_eq_zero fun _ _ ↦ by grind]; simp [hq]
    · rw [Finset.sum_eq_zero fun _ _ ↦ by grind]; simp [hi]
  · rw [Finset.sum_eq_zero fun _ _ ↦ by grind, map_zero,
      evalEuclideanHom_eq_zero_of_notMem_range φ j hb hz]

private theorem intertwine_of_basis [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) *
        CStarMatrix.toEuclideanCLM (m j)
          (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x) =
      evalEuclideanHom φ j x *
        (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) := by
  cases nonempty_fintype ι
  ext w
  have key (i : ι) (p q : n i) :=
    congrFun (congrArg DFunLike.coe (intertwine_single_of_basis φ j hb i p q)) w
  simp only [mul_apply_eq_comp] at key ⊢
  conv_lhs => rw [elem_eq_sum_piSingle_single x]
  conv_rhs => rw [elem_eq_sum_piSingle_single x]
  simp only [map_sum, map_smul, sum_apply, smul_apply, key]

private theorem exists_orthonormalBasis_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j)),
      ∀ a, b (f a) = partialBasisVec φ j a := by
  let s : Set (m j) := Set.range f
  let v : m j → EuclideanSpace ℂ (m j) := Function.extend f (partialBasisVec φ j) 0
  have hv_apply (a : Σ i, n i × Fin (φ.multiplicityMatrix j i)) :
      v (f a) = partialBasisVec φ j a := f.injective.extend_apply _ _ a
  have hv_orth : Orthonormal ℂ (s.domRestrict v) := by
    have heq : s.domRestrict v ∘ Equiv.ofInjective f f.injective = partialBasisVec φ j :=
      funext fun a ↦ hv_apply a
    have hcomp := (orthonormal_partialBasisVec φ j).comp
      (Equiv.ofInjective f f.injective).symm (Equiv.injective _)
    simpa [← heq, Function.comp_assoc] using hcomp
  obtain ⟨b, hb_mem⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := m j)) hv_orth
  exact ⟨b, fun a ↦ (hb_mem (f a) ⟨a, rfl⟩).trans (hv_apply a)⟩

private theorem exists_unitary_conj_cstarMatrixBlockHom [Finite ι]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ u : unitary (CStarMatrix (m j) (m j) ℂ), ∀ x,
      (u : CStarMatrix (m j) (m j) ℂ) * TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x *
        star (u : CStarMatrix (m j) (m j) ℂ) = φ x j := by
  let _ := Classical.decEq ι
  let _ := fun i ↦ Classical.decEq (n i)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_partialBasisVec φ j f
  let uH : unitary (EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) :=
    Unitary.linearIsometryEquiv.symm b.repr.symm
  let u : unitary (CStarMatrix (m j) (m j) ℂ) :=
    Unitary.map (StarMonoidHom.ofClass (CStarMatrix.toEuclideanCLM (m j)).symm) uH
  refine ⟨u, fun x ↦ (CStarMatrix.toEuclideanCLM (m j)).injective ?_⟩
  have hu : CStarMatrix.toEuclideanCLM (m j) u = (b.repr.symm : _ →L[ℂ] _) := by
    simp [u, uH, StarMonoidHom.ofClass]
  calc CStarMatrix.toEuclideanCLM (m j)
        ((u : CStarMatrix (m j) (m j) ℂ) *
          TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x *
          star (u : CStarMatrix (m j) (m j) ℂ))
      = ((b.repr.symm : _ →L[ℂ] _) *
          CStarMatrix.toEuclideanCLM (m j)
            (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x)) *
          star (uH : _ →L[ℂ] _) := by simp [map_mul, map_star, hu, uH, mul_assoc]
    _ = evalEuclideanHom φ j x * ((uH : _ →L[ℂ] _) * star (uH : _ →L[ℂ] _)) := by
        rw [intertwine_of_basis φ j hb x, mul_assoc, ← Unitary.coe_symm_linearIsometryEquiv_apply]
    _ = CStarMatrix.toEuclideanCLM (m j) (φ x j) := by
        rw [Unitary.mul_star_self_of_mem uH.prop, mul_one, evalEuclideanHom_apply]

/-- **Standard block-diagonal form up to unitary conjugacy**: every `⋆`-homomorphism `φ` is
unitarily conjugate in the target to `TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f` for any
family of injections `f j : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j`. -/
theorem exists_unitary_conj_cstarMatrixPiBlockHom [Finite ι]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (f : ∀ j, (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
      (u : ∀ j, CStarMatrix (m j) (m j) ℂ) *
        TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f x *
        star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = φ x := by
  choose u hu using fun j ↦ φ.exists_unitary_conj_cstarMatrixBlockHom j (f j)
  refine ⟨⟨fun j ↦ u j, Pi.mem_unitary_iff.mpr fun j ↦ (u j).prop⟩, fun x ↦ funext fun j ↦ ?_⟩
  simpa only [Pi.mul_apply, Pi.star_apply, TauCeti.cstarMatrixPiBlockHom_apply] using hu j x

/-- Unitary conjugation in the target leaves `multiplicityMatrix` invariant. -/
@[simp high]
theorem multiplicityMatrix_conjStarAlgAut_comp [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    ((Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp φ).multiplicityMatrix =
      φ.multiplicityMatrix := by
  classical
  ext j i
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · simp
  · obtain ⟨p⟩ := hne
    apply Nat.cast_injective (R := ℂ)
    rw [natCast_multiplicityMatrix_apply_eq_trace_single _ j i p,
      natCast_multiplicityMatrix_apply_eq_trace_single φ j i p]
    simp only [comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
      Pi.mul_apply, Pi.star_apply, CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star]
    have huj := Pi.mem_unitary_iff.mp u.prop j
    have hmul : (CStarMatrix.ofMatrix.symm ((u : ∀ j', CStarMatrix (m j') (m j') ℂ) j))ᴴ *
        CStarMatrix.ofMatrix.symm ((u : ∀ j', CStarMatrix (m j') (m j') ℂ) j) = 1 := by
      rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul,
        Unitary.star_mul_self_of_mem huj, CStarMatrix.ofMatrix_symm_one]
    rw [Matrix.trace_mul_cycle, hmul, Matrix.one_mul]

/-- Unitary conjugation in the source leaves `multiplicityMatrix` invariant. -/
@[simp high]
theorem multiplicityMatrix_comp_conjStarAlgAut
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    (φ.comp (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom).multiplicityMatrix =
      φ.multiplicityMatrix := by
  classical
  ext j i
  have hunit : Unitary.conjStarAlgAut ℂ (∀ i', CStarMatrix (n i') (n i') ℂ) u
      (Pi.single i 1) = Pi.single i 1 := by
    ext i' r s
    by_cases hi : i' = i
    · subst hi; simp [Unitary.conjStarAlgAut_apply,
        Unitary.mul_star_self_of_mem (Pi.mem_unitary_iff.mp u.prop i')]
    · simp [Unitary.conjStarAlgAut_apply, Pi.single_eq_of_ne hi]
  simp [multiplicityMatrix_apply, hunit]

/-- Entrywise formula for the multiplicity matrix of a unitary inner automorphism: `1` on the
diagonal at nonempty blocks, and `0` elsewhere. -/
theorem multiplicityMatrix_conjStarAlgAut_apply [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) (i' i : ι) :
    (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
        u).toNonUnitalStarAlgHom.multiplicityMatrix i' i =
      if i' = i ∧ Fintype.card (n i) ≠ 0 then 1 else 0 := by
  have hcomp : (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
      u).toNonUnitalStarAlgHom =
      (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp (.id ℂ _) := by ext; simp
  rw [hcomp, multiplicityMatrix_conjStarAlgAut_comp, multiplicityMatrix_id_apply]

/-- When every block index type `n i` is nonempty, a unitary inner automorphism has the identity
multiplicity matrix. -/
@[simp]
theorem multiplicityMatrix_conjStarAlgAut [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
        u).toNonUnitalStarAlgHom.multiplicityMatrix = 1 := by
  ext i' i; rw [multiplicityMatrix_conjStarAlgAut_apply, Matrix.one_apply]
  simp [Fintype.card_ne_zero]

private def canonicalBlockEmbedding [Fintype ι] [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j :=
  Classical.choice <| Function.Embedding.nonempty_of_card_le <| by
    simpa [Fintype.card_sigma, Fintype.card_prod, mul_comm] using
      φ.sum_multiplicityMatrix_mul_card_le j

/-- **Classification up to unitary conjugacy**: two `⋆`-homomorphisms between finite products of
complex matrix C⋆-algebras are unitarily conjugate in the target if and only if they have the same
multiplicity matrix. -/
theorem exists_unitary_conj_iff_multiplicityMatrix_eq [Finite ι] [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
        (u : ∀ j, CStarMatrix (m j) (m j) ℂ) * φ x *
          star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = ψ x) ↔
      φ.multiplicityMatrix = ψ.multiplicityMatrix := by
  cases nonempty_fintype ι
  classical
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun hEq ↦ ?_⟩
  · have hψ : ψ = (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp φ :=
      NonUnitalStarAlgHom.ext fun x ↦ by
        rw [comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
          hu x]
    rw [hψ, φ.multiplicityMatrix_conjStarAlgAut_comp u]
  · let f := φ.canonicalBlockEmbedding
    obtain ⟨u₁, hu₁⟩ := φ.exists_unitary_conj_cstarMatrixPiBlockHom f
    obtain ⟨u₂, hu₂⟩ := ψ.exists_unitary_conj_cstarMatrixPiBlockHom (hEq ▸ f)
    have hcast {H₁ H₂ : Matrix κ ι ℕ} (h : H₁ = H₂)
        (g : ∀ j, (Σ i, n i × Fin (H₁ j i)) ↪ m j) :
        TauCeti.cstarMatrixPiBlockHom H₂ (h ▸ g) = TauCeti.cstarMatrixPiBlockHom H₁ g := by
      subst h; rfl
    refine ⟨u₂ * star u₁, fun x ↦ ?_⟩
    rw [← Unitary.conjStarAlgAut_apply (S := ℂ), Unitary.conjStarAlgAut_mul_apply,
      ← Unitary.conjStarAlgAut_symm, ← hu₁ x, ← Unitary.conjStarAlgAut_apply (S := ℂ),
      StarAlgEquiv.symm_apply_apply, ← hcast hEq f, Unitary.conjStarAlgAut_apply, hu₂ x]

end UnitaryConjugacy

section ApproximateUnitaryEquivalence

open scoped ComplexOrder

/-- Two `⋆`-homomorphisms between finite products of complex matrix C⋆-algebras are approximately
unitarily equivalent in the target if and only if they have the same multiplicity matrix (hence, by
`exists_unitary_conj_iff_multiplicityMatrix_eq`, if and only if they are unitarily conjugate). -/
theorem approximatelyUnitarilyEquivalent_iff_multiplicityMatrix_eq
    {ι κ : Type*} {n : ι → Type*} {m : κ → Type*} [Fintype ι] [Fintype κ] [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    TauCeti.ApproximatelyUnitarilyEquivalent φ ψ ↔
      φ.multiplicityMatrix = ψ.multiplicityMatrix := by
  classical
  refine ⟨fun h ↦ ?_, fun hEq ↦ ?_⟩
  · ext j i
    rcases isEmpty_or_nonempty (n i) with hE | hne
    · simp
    · obtain ⟨p⟩ := hne
      let e : ∀ i', CStarMatrix (n i') (n i') ℂ :=
        Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))
      let τ : (∀ j', CStarMatrix (m j') (m j') ℂ) → ℂ :=
        fun y ↦ Matrix.trace (CStarMatrix.ofMatrixL.symm (y j))
      have hcont : Continuous τ :=
        (CStarMatrix.ofMatrixL.symm.continuous.comp (continuous_apply j)).matrix_trace
      obtain ⟨δ, hδ, hlt⟩ := Metric.continuousAt_iff.mp hcont.continuousAt 1 zero_lt_one
      let B := ∀ j', CStarMatrix (m j') (m j') ℂ
      obtain ⟨u, hu⟩ := (TauCeti.approximatelyUnitarilyEquivalent_def φ ψ).mp h {e} δ hδ
      have hdist : dist ((u : B) * φ e * star (u : B) - ψ e) 0 < δ := by
        simpa [dist_zero_right] using hu e (Finset.mem_singleton_self e)
      have hnorm : ‖τ ((u : B) * φ e * star (u : B) - ψ e)‖ < 1 := by
        simpa [τ, dist_zero_right] using hlt hdist
      have hτ_diff : τ ((u : B) * φ e * star (u : B) - ψ e) =
          (φ.multiplicityMatrix j i : ℂ) - (ψ.multiplicityMatrix j i : ℂ) := by
        have hφ' := ((Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ
          |>.natCast_multiplicityMatrix_apply_eq_trace_single j i p).symm
        rw [φ.multiplicityMatrix_conjStarAlgAut_comp u, comp_apply,
          StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply] at hφ'
        dsimp only [τ]
        rw [Pi.sub_apply, map_sub, Matrix.trace_sub, CStarMatrix.ofMatrixL_symm_apply,
          CStarMatrix.ofMatrixL_symm_apply]
        exact congrArg₂ (· - ·) hφ' (ψ.natCast_multiplicityMatrix_apply_eq_trace_single j i p).symm
      rw [hτ_diff, ← Int.cast_natCast (φ.multiplicityMatrix j i),
        ← Int.cast_natCast (ψ.multiplicityMatrix j i), ← Int.cast_sub,
        Complex.norm_intCast] at hnorm
      have habs : |(φ.multiplicityMatrix j i : ℤ) - (ψ.multiplicityMatrix j i : ℤ)| < 1 := by
        exact_mod_cast hnorm
      obtain ⟨_, _⟩ := abs_lt.mp habs
      omega
  · obtain ⟨u, hu⟩ := (φ.exists_unitary_conj_iff_multiplicityMatrix_eq ψ).mpr hEq
    exact TauCeti.ApproximatelyUnitarilyEquivalent.of_unitary u hu

end ApproximateUnitaryEquivalence

section Composition

variable {ι κ μ : Type*} {n : ι → Type*} {m : κ → Type*} {l : μ → Type*}

private theorem multiplicityMatrix_comp_of_finite [Finite ι] [Fintype κ]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ k, Fintype (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₙₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).multiplicityMatrix = ψ.multiplicityMatrix * φ.multiplicityMatrix := by
  cases nonempty_fintype ι
  classical
  let f := φ.canonicalBlockEmbedding
  let φ₀ := TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f
  obtain ⟨u, hu⟩ := φ.exists_unitary_conj_cstarMatrixPiBlockHom f
  let ψ' := ψ.comp (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom
  have hcomp_eq : ψ.comp φ = ψ'.comp φ₀ :=
    NonUnitalStarAlgHom.ext fun x ↦ by
      dsimp only [ψ', φ₀]
      rw [comp_apply, comp_apply, comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
        Unitary.conjStarAlgAut_apply, hu x]
  ext k i
  rw [hcomp_eq, Matrix.mul_apply]
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · simp
  · obtain ⟨p⟩ := hne
    apply Nat.cast_injective (R := ℂ)
    rw [(ψ'.comp φ₀).natCast_multiplicityMatrix_apply_eq_trace_single k i p, comp_apply]
    have hφ₀ : φ₀ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) =
        ∑ j : κ, ∑ t : Fin (φ.multiplicityMatrix j i),
          Pi.single j (CStarMatrix.ofMatrix (Matrix.single (f j ⟨i, p, t⟩) (f j ⟨i, p, t⟩) 1)) := by
      funext j; apply CStarMatrix.ofMatrix.symm.injective
      simp only [φ₀, TauCeti.cstarMatrixPiBlockHom_apply,
        TauCeti.cstarMatrixBlockHom_piSingle_single, Finset.sum_apply, Equiv.symm_apply_apply]
      rw [Fintype.sum_eq_single j fun j' hj' ↦ by simp [Pi.single_eq_of_ne hj'.symm]]
      simp [CStarMatrix.ofMatrix_symm_sum]
    rw [hφ₀, map_sum, Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum,
      Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_sum, Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum]
    simp_rw [← ψ'.natCast_multiplicityMatrix_apply_eq_trace_single k j _]
    simp [ψ', mul_comm]

/-- **Functoriality of the multiplicity matrix**: composition of `⋆`-homomorphisms between products
of complex matrix C⋆-algebras corresponds to matrix multiplication of their multiplicity matrices.
-/
@[simp]
theorem multiplicityMatrix_comp [Fintype κ]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ k, Fintype (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₙₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).multiplicityMatrix = ψ.multiplicityMatrix * φ.multiplicityMatrix := by
  classical
  ext k i
  let ιHom : (Unit → CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ i', CStarMatrix (n i') (n i') ℂ) :=
    (NonUnitalStarAlgHom.single ℂ _ i).comp
      (StarAlgEquiv.funUnique ℂ Unit (CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom
  have hι : ιHom (Pi.single () 1) = Pi.single i 1 := by simp [ιHom]
  have hassoc : (ψ.comp φ).comp ιHom = ψ.comp (φ.comp ιHom) := NonUnitalStarAlgHom.ext fun _ ↦ rfl
  have hunit := congrFun (congrFun (multiplicityMatrix_comp_of_finite ψ (φ.comp ιHom)) k) ()
  rw [(ψ.comp φ).multiplicityMatrix_apply k i, ← hι, ← comp_apply,
    ← ((ψ.comp φ).comp ιHom).multiplicityMatrix_apply k (), hassoc, hunit,
    Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [φ.multiplicityMatrix_apply j i, ← hι, ← comp_apply,
    ← (φ.comp ιHom).multiplicityMatrix_apply j ()]

end Composition

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {ι κ μ : Type*} {n : ι → Type*} {m : κ → Type*} {l : μ → Type*}

private theorem comp_toNonUnitalStarAlgHom [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] [∀ k, Fintype (l k)] [∀ k, DecidableEq (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).toNonUnitalStarAlgHom = ψ.toNonUnitalStarAlgHom.comp φ.toNonUnitalStarAlgHom := by
  ext; simp

/-- Unitary conjugation in the target leaves the multiplicity matrix of a unital `⋆`-homomorphism
invariant. -/
@[simp high]
theorem multiplicityMatrix_conjStarAlgAut_comp [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (((Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom.comp φ).toNonUnitalStarAlgHom).multiplicityMatrix
      = φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  have heq : ((Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom :
      _ →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)).toNonUnitalStarAlgHom =
      (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom := by ext; simp
  rw [comp_toNonUnitalStarAlgHom, heq, NonUnitalStarAlgHom.multiplicityMatrix_conjStarAlgAut_comp]

/-- Unitary conjugation in the source leaves the multiplicity matrix of a unital `⋆`-homomorphism
invariant. -/
@[simp high]
theorem multiplicityMatrix_comp_conjStarAlgAut [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    ((φ.comp (Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom).toNonUnitalStarAlgHom).multiplicityMatrix
      = φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  have heq : ((Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom :
      _ →⋆ₐ[ℂ] (∀ i, CStarMatrix (n i) (n i) ℂ)).toNonUnitalStarAlgHom =
      (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom := by ext; simp
  rw [comp_toNonUnitalStarAlgHom, heq, NonUnitalStarAlgHom.multiplicityMatrix_comp_conjStarAlgAut]

/-- **Classification of unital `⋆`-homomorphisms up to unitary conjugacy**: two unital
`⋆`-homomorphisms between finite products of complex matrix C⋆-algebras are unitarily conjugate in
the target if and only if their multiplicity matrices coincide. -/
theorem exists_unitary_conj_iff_multiplicityMatrix_eq [Finite ι] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
        (u : ∀ j, CStarMatrix (m j) (m j) ℂ) * φ x *
          star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = ψ x) ↔
      φ.toNonUnitalStarAlgHom.multiplicityMatrix = ψ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  simp_rw [← StarAlgHom.coe_toNonUnitalStarAlgHom]
  exact φ.toNonUnitalStarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq
    ψ.toNonUnitalStarAlgHom

/-- Composition of unital `⋆`-homomorphisms multiplies their multiplicity matrices. -/
@[simp]
theorem multiplicityMatrix_comp [Fintype κ] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] [∀ k, Fintype (l k)] [∀ k, DecidableEq (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).toNonUnitalStarAlgHom.multiplicityMatrix =
      ψ.toNonUnitalStarAlgHom.multiplicityMatrix * φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  rw [comp_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.multiplicityMatrix_comp]

end StarAlgHom

namespace TauCeti

/-- **Divisibility criterion for unital matrix embeddings**: a unital `⋆`-homomorphism
`CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` exists if and only if
`Fintype.card n ∣ Fintype.card m`. -/
theorem nonempty_starAlgHom_cstarMatrix_iff {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] :
    Nonempty (CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ) ↔ Fintype.card n ∣ Fintype.card m := by
  let eₙ := StarAlgEquiv.funUnique ℂ Unit (CStarMatrix n n ℂ)
  let eₘ := StarAlgEquiv.funUnique ℂ Unit (CStarMatrix m m ℂ)
  refine ⟨fun ⟨φ⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · let φ' : (Unit → CStarMatrix n n ℂ) →⋆ₐ[ℂ] (Unit → CStarMatrix m m ℂ) :=
      eₘ.symm.toStarAlgHom.comp (φ.comp eₙ.toStarAlgHom)
    have hsum := φ'.sum_multiplicityMatrix_mul_card_eq ()
    rw [Fintype.sum_unique] at hsum
    exact ⟨φ'.toNonUnitalStarAlgHom.multiplicityMatrix () (), by rw [mul_comm, hsum]⟩
  · classical
    let entry : ℕ := if Nonempty n then k else 0
    obtain ⟨φ', _⟩ := (exists_starAlgHom_multiplicityMatrix_eq_iff
      (n := fun _ : Unit ↦ n) (m := fun _ : Unit ↦ m) (Matrix.of fun _ _ ↦ entry)).mpr
      ⟨fun _ _ hE ↦ by simp [entry, not_nonempty_iff.mpr hE], fun _ ↦ by
        rcases isEmpty_or_nonempty n with hE | hne
        · simp [Fintype.card_eq_zero, hk]
        · simp [entry, hne, hk, mul_comm]⟩
    exact ⟨eₘ.toStarAlgHom.comp (φ'.comp eₙ.symm.toStarAlgHom)⟩

end TauCeti

namespace StarAlgHom

/-- **Uniqueness of unital matrix embeddings up to unitary conjugacy**: any two unital
`⋆`-homomorphisms `CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` are unitarily conjugate in
`CStarMatrix m m ℂ`. -/
theorem exists_unitary_conj_cstarMatrix {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (φ ψ : CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ) :
    ∃ u : unitary (CStarMatrix m m ℂ), ∀ x,
      (u : CStarMatrix m m ℂ) * φ x * star (u : CStarMatrix m m ℂ) = ψ x := by
  let eₙ := StarAlgEquiv.funUnique ℂ Unit (CStarMatrix n n ℂ)
  let eₘ := StarAlgEquiv.funUnique ℂ Unit (CStarMatrix m m ℂ)
  let φ' := eₘ.symm.toStarAlgHom.comp (φ.comp eₙ.toStarAlgHom)
  let ψ' := eₘ.symm.toStarAlgHom.comp (ψ.comp eₙ.toStarAlgHom)
  have hEq : φ'.toNonUnitalStarAlgHom.multiplicityMatrix =
      ψ'.toNonUnitalStarAlgHom.multiplicityMatrix := by
    ext ⟨⟩ ⟨⟩
    rcases isEmpty_or_nonempty n with hE | hne
    · simp
    · have h₁ := φ'.sum_multiplicityMatrix_mul_card_eq ()
      have h₂ := ψ'.sum_multiplicityMatrix_mul_card_eq ()
      rw [Fintype.sum_unique] at h₁ h₂
      exact Nat.mul_right_cancel Fintype.card_pos (h₁.trans h₂.symm)
  obtain ⟨u, hu⟩ := (φ'.exists_unitary_conj_iff_multiplicityMatrix_eq ψ').mpr hEq
  refine ⟨⟨eₘ u, Unitary.map_mem eₘ u.prop⟩, fun x ↦ ?_⟩
  have hx := congrArg eₘ (hu (eₙ.symm x))
  simpa only [φ', ψ', map_mul, map_star, StarAlgHom.comp_apply,
    StarAlgEquiv.toStarAlgHom_apply, StarAlgEquiv.apply_symm_apply] using hx

end StarAlgHom

end
