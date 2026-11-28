/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism.Basic
public import TauCeti.LinearAlgebra.RootSystem.KostantPartition.IntervalMatrix
public import TauCeti.LinearAlgebra.RootSystem.KostantPartition.VectorPartition
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Positive
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The type-A Kostant partition function as an interval-matrix count

Let `b` be a base of Cartan type `Aₙ` of a finite reduced crystallographic root pairing, its simple
roots `α₀, …, α_{n-1}` labelled by `Fin n` in Bourbaki order (label `i` is Bourbaki node `i + 1`).
The positive roots are then the sums
`α_i + ⋯ + α_{j-1}` for `0 ≤ i < j ≤ n`, that is the roots `e_i - e_j` of the classical model, and
the column of simple-root coefficients of `e_i - e_j` is the indicator of the interval of nodes
`i ≤ k < j`. These columns are the columns of the interval matrix `TauCeti.intervalMatrix (n + 1)`,
so the Kostant partition function of `b` is its vector partition function:
`P(∑ₖ cₖ αₖ) = #{d : intervalMatrix (n + 1) *ᵥ d = c}`
(`TauCeti.kostantPartition_eq_vectorPartitionCount_intervalMatrix`).

This identifies the native Kostant partition function of every root system of type `A` with the
count to which the chamber theory of unimodular vector partition functions applies: the interval
matrix is totally unimodular (`TauCeti.intervalMatrix_isTotallyUnimodular`) and the all-ones
covector is positive on its columns (`TauCeti.sum_intervalMatrix_apply_pos`).

The positive roots are identified with intervals through the pinned datum
`TauCeti.DynkinType.typeASimplyConnectedRootDatum n`, whose roots are indexed by ordered pairs and
whose root coefficients are known explicitly
(`TauCeti.DynkinType.rootCoefficients_typeASimplyConnectedBase`). A labelling of the simple roots
of `b` realizing the Cartan matrix `Aₙ` extends to a bijection of root indices with the pinned
datum preserving root coefficients (`RootPairing.Base.indexEquivOfCartanMatrixEq`).

## Main definitions

* `TauCeti.typeAPosRootEquiv`: the labelling of the positive roots of a base of Cartan type `Aₙ` by
  the intervals `(i, j)`, `0 ≤ i < j ≤ n`.

## Main results

* `TauCeti.rootCoefficients_typeAPosRootEquiv`: the column of simple-root coefficients of the
  positive root labelled by the interval `(i, j)` is the column `(i, j)` of the interval matrix.
* `TauCeti.kostantPartition_eq_vectorPartitionCount_intervalMatrix`: the Kostant partition
  function of a base of Cartan type `Aₙ` is the vector partition function of the interval matrix.
* `TauCeti.kostantPartition_typeASimplyConnectedRootDatum_two`: in type `A₂`, `a α₀ + b α₁` has
  `min a b + 1` Kostant partitions when `a, b ≥ 0` and none otherwise.

## References

* S. Billey, V. Guillemin and E. Rassart, *A vector partition function for the multiplicities
  of `sl_k ℂ`*, J. Algebra **278** (2004), 251–293, §1.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public section

namespace TauCeti

open DynkinType

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]
  [P.IsReduced] {b : P.Base} {n : ℕ}

/-- The relabelling of the simple roots of `b` along which its Cartan matrix is that of the pinned
base of type `Aₙ`. -/
private def pinnedSupportEquiv (e : Fin n ≃ b.support) :
    b.support ≃ (typeASimplyConnectedBase n).support :=
  e.symm.trans (typeASimpleSupportEquiv n)

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsReduced] in
private lemma cartanMatrix_pinnedSupportEquiv {e : Fin n ≃ b.support}
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = CartanMatrix.A n i j) (i j : b.support) :
    (typeASimplyConnectedBase n).cartanMatrix (pinnedSupportEquiv e i) (pinnedSupportEquiv e j) =
      b.cartanMatrix i j := by
  rw [pinnedSupportEquiv, Equiv.trans_apply, Equiv.trans_apply,
    cartanMatrix_typeASimpleSupportEquiv, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {e : Fin n ≃ b.support} (he : ∀ i j, b.cartanMatrix (e i) (e j) = CartanMatrix.A n i j)

/-- The bijection of root indices with the pinned datum of type `Aₙ` extending the labelling `e`
of the simple roots. -/
private noncomputable def pinnedIndexEquiv : ι ≃ Fin (n * (n + 1)) :=
  b.indexEquivOfCartanMatrixEq (typeASimplyConnectedBase n) (pinnedSupportEquiv e)
    (cartanMatrix_pinnedSupportEquiv he)

private lemma isPos_pinnedIndexEquiv_iff (i : ι) :
    (typeASimplyConnectedBase n).IsPos (pinnedIndexEquiv he i) ↔ b.IsPos i :=
  b.isPos_indexEquivOfCartanMatrixEq_iff _ _ _ i

private lemma rootCoefficients_pinnedIndexEquiv (i : ι) (k : Fin n) :
    (typeASimplyConnectedBase n).rootCoefficients (pinnedIndexEquiv he i)
      (typeASimpleSupportEquiv n k) = b.rootCoefficients i (e k) := by
  rw [pinnedIndexEquiv, b.rootCoefficients_indexEquivOfCartanMatrixEq, Function.comp_apply]
  simp [pinnedSupportEquiv]

private lemma isPos_pinnedIndexEquiv_symm_iff (j : Fin (n * (n + 1))) :
    (typeASimplyConnectedBase n).IsPos j ↔ (pinnedIndexEquiv he).symm j ∈ posRootsFinset P b := by
  rw [mem_posRootsFinset, mem_posRoots, ← isPos_pinnedIndexEquiv_iff he, Equiv.apply_symm_apply]

/-- The positive roots of a base `b` of Cartan type `Aₙ`, labelled along `e` by the intervals of
the classical model: the interval `(i, j)` labels the positive root `α_i + ⋯ + α_{j-1}`. -/
noncomputable def typeAPosRootEquiv : PositiveInterval (n + 1) ≃ posRootsFinset P b :=
  ((Equiv.subtypeSubtypeEquivSubtype (p := fun q : Fin (n + 1) × Fin (n + 1) ↦ q.1 ≠ q.2)
      (q := fun q ↦ q.1 < q.2) fun h ↦ h.ne).symm.trans
    ((typeAIndexEquiv n).subtypeEquiv fun q ↦ (isPos_typeAIndexEquiv_iff q).symm)).trans
    ((pinnedIndexEquiv he).symm.subtypeEquiv (isPos_pinnedIndexEquiv_symm_iff he))

/-- The root index of an interval is transported back from the pinned type-A datum. -/
private lemma coe_typeAPosRootEquiv (p : PositiveInterval (n + 1)) :
    (typeAPosRootEquiv he p : ι) =
      (pinnedIndexEquiv he).symm (typeAIndexEquiv n ⟨p.val, p.property.ne⟩) := by
  simp [typeAPosRootEquiv, Equiv.subtypeSubtypeEquivSubtype,
    Equiv.subtypeSubtypeEquivSubtypeInter, Equiv.subtypeSubtypeEquivSubtypeExists,
    Equiv.subtypeEquivRight_symm_apply]

private lemma pinnedIndexEquiv_typeAPosRootEquiv (p : PositiveInterval (n + 1)) :
    pinnedIndexEquiv he (typeAPosRootEquiv he p) = typeAIndexEquiv n ⟨p.val, p.property.ne⟩ := by
  rw [coe_typeAPosRootEquiv, Equiv.apply_symm_apply]

/-- **The positive roots of type `Aₙ` are the intervals of simple roots.** The column of
simple-root coefficients of the positive root labelled by the interval `(i, j)` is the column
`(i, j)` of the interval matrix: the coefficient of `α_k` is `1` for `i ≤ k < j` and `0`
otherwise. -/
@[simp]
theorem rootCoefficients_typeAPosRootEquiv (p : PositiveInterval (n + 1)) (k : Fin n) :
    b.rootCoefficients (typeAPosRootEquiv he p) (e k) = intervalMatrix (n + 1) k p := by
  have hl : typeASimpleSupportEquiv n k = ⟨typeASimpleIndex n k, by simp⟩ :=
    Subtype.ext (coe_typeASimpleSupportEquiv k)
  rw [← rootCoefficients_pinnedIndexEquiv he, pinnedIndexEquiv_typeAPosRootEquiv, hl,
    rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv, intervalMatrix_apply]
  have hp : p.val.1 < p.val.2 := p.property
  simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc] at hp ⊢
  split_ifs <;> omega

include he in
/-- **The Kostant partition function of type `Aₙ` is the vector partition function of the interval
matrix.** For a base `b` of a finite reduced crystallographic root pairing whose simple roots,
labelled by `e`, realize the Cartan matrix `Aₙ`, the number of ways of writing `∑ₖ cₖ αₖ` as a
sum of positive roots is the number of vectors `d` of natural numbers with
`intervalMatrix (n + 1) *ᵥ d = c`. -/
theorem kostantPartition_eq_vectorPartitionCount_intervalMatrix (c : Fin n → ℤ) :
    kostantPartition P b (∑ k, c k • P.root (e k)) =
      (intervalMatrix (n + 1)).vectorPartitionCount c :=
  kostantPartition_eq_vectorPartitionCount (r := e) (s := typeAPosRootEquiv he)
    (fun k p ↦ (rootCoefficients_typeAPosRootEquiv he p k).symm) c

/-! ### The example of `A₂` -/

/-- The columns `(0, 1)`, `(1, 2)`, `(0, 2)` of the interval matrix of `A₂`, which are the simple
roots `α₀`, `α₁` and the highest root `α₀ + α₁`. -/
private def positiveIntervalThreeEquiv : Fin 3 ≃ PositiveInterval 3 where
  toFun := ![⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩, ⟨(0, 2), by decide⟩]
  invFun p := if p.val = (0, 1) then 0 else if p.val = (1, 2) then 1 else 2
  left_inv := by decide
  right_inv := by decide

private lemma intervalMatrix_three_submatrix :
    (intervalMatrix 3).submatrix id positiveIntervalThreeEquiv = !![1, 0, 1; 0, 1, 1] := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [positiveIntervalThreeEquiv]

/-- **The Kostant partition function of `A₂`.** In the pinned root datum of type `A₂`, the element
`a α₀ + b α₁` is a sum of positive roots in `min a b + 1` ways when `a, b ≥ 0`, and in none
otherwise: the partitions are `(a - z) α₀ + (b - z) α₁ + z (α₀ + α₁)` for `0 ≤ z ≤ min a b`. -/
theorem kostantPartition_typeASimplyConnectedRootDatum_two (a b : ℤ) :
    kostantPartition (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2)
      (a • (typeASimplyConnectedRootDatum 2).root (typeASimpleIndex 2 0) +
        b • (typeASimplyConnectedRootDatum 2).root (typeASimpleIndex 2 1)) =
      (min a b + 1).toNat := by
  have h := kostantPartition_eq_vectorPartitionCount_intervalMatrix
    (cartanMatrix_typeASimpleSupportEquiv (n := 2)) ![a, b]
  simp only [Fin.sum_univ_two, coe_typeASimpleSupportEquiv, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  rw [h, ← Matrix.vectorPartitionCount_a2, ← intervalMatrix_three_submatrix,
    Matrix.vectorPartitionCount_submatrix_equiv]

end TauCeti
