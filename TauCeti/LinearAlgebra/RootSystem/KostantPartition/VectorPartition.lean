/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.VectorPartition.Basic
public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.KostantPartition.Basic

/-!
# Kostant partitions as vector partitions

A base `b` of a root pairing makes the root lattice free on the simple roots, so an element
`ν = ∑ₖ cₖ αₖ` of the root lattice is recorded by its column `c` of simple-root coefficients, and a
positive root `β` by its column `b.rootCoefficients β`. Collect the columns of the positive roots
into an integer matrix `A`. Writing `ν` as a sum of positive roots with multiplicities `d` is then
the same as writing `c` as the nonnegative integer combination `A *ᵥ d` of the columns of `A`.
Hence the Kostant partition function of `b` is the vector partition function of `A`:
`P(∑ₖ cₖ αₖ) = #{d : A *ᵥ d = c}`.

This is what lets the chamber theory of vector partition functions be applied to Kostant partition
functions. To apply it to a concrete coordinate model, such as the interval matrix of type `A`, the
comparison is stated for any integer matrix `A` with rows labelled by the simple roots through an
equivalence `r` and columns labelled by the positive roots through an equivalence `s`, such that
the column `p` of `A` is the column of simple-root coefficients of the positive root `s p`. The
equivalence of partitions restricts a Kostant partition to the positive roots, and its inverse
extends a vector partition by zero on the negative roots.

## Main definitions

* `TauCeti.kostantPartitionEquivVectorPartitions`: the equivalence between the Kostant partitions
  of `∑ₖ cₖ αₖ` and the vector partitions of `c`.

## Main results

* `TauCeti.sum_zsmul_root_eq_sum_mulVec_zsmul_root`: a combination of positive roots, expanded in
  the simple roots.
* `TauCeti.kostantPartition_eq_vectorPartitionCount`: the Kostant partition function is the vector
  partition function of the matrix of simple-root coefficients of the positive roots.

## References

* B. Kostant, *A formula for the multiplicity of a weight*, Trans. Amer. Math. Soc. **93** (1959),
  53–73.
* S. Billey, V. Guillemin and E. Rassart, *A vector partition function for the multiplicities
  of `sl_k ℂ`*, J. Algebra **278** (2004), 251–293, §1.
-/

public section

namespace TauCeti

open Function Matrix

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Finite ι] {P : RootPairing ι R M N} {b : P.Base}
  {κ ι' : Type*} {r : κ ≃ b.support} {s : ι' ≃ posRootsFinset P b} {A : Matrix κ ι' ℤ}

/-! ### Extension by zero from the positive roots -/

/-- The extension by zero of a function on the positive roots, labelled along `s`. -/
private noncomputable def extendPosRoots (s : ι' ≃ posRootsFinset P b) (d : ι' → ℕ) : ι → ℕ :=
  open scoped Classical in
  fun i ↦ if h : i ∈ posRootsFinset P b then d (s.symm ⟨i, h⟩) else 0

private lemma extendPosRoots_apply_coe (s : ι' ≃ posRootsFinset P b) (d : ι' → ℕ) (p : ι') :
    extendPosRoots s d (s p) = d p := by
  simp [extendPosRoots]

/-- A function supported on the positive roots is the extension by zero of its restriction to the
positive roots, labelled along `s`. -/
private lemma extendPosRoots_comp {d : ι → ℕ} (hd : support d ⊆ posRoots P b) :
    extendPosRoots s (fun p ↦ d (s p)) = d := by
  funext i
  by_cases hi : i ∈ posRootsFinset P b
  · simp [extendPosRoots, hi]
  · simp only [extendPosRoots, hi, dite_false]
    by_contra h
    exact hi ((mem_posRootsFinset P b i).mpr (hd (mem_support.mpr (Ne.symm h))))

/-- A function vanishes off the positive roots after extension by zero. -/
private lemma mem_posRoots_of_extendPosRoots_ne_zero {d : ι' → ℕ} {i : ι}
    (hi : extendPosRoots s d i ≠ 0) : i ∈ posRoots P b := by
  by_contra h
  exact hi (by simp [extendPosRoots, mem_posRootsFinset, h])

/-! ### Kostant partitions and vector partitions -/

variable [Fintype κ] [Fintype ι']

/-- **A combination of positive roots, expanded in the simple roots.** If the column `p` of `A` is
the column of simple-root coefficients of the positive root `s p`, then `∑ₚ dₚ (s p)` is the
combination of the simple roots with coefficients `A *ᵥ d`. -/
theorem sum_zsmul_root_eq_sum_mulVec_zsmul_root
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (d : ι' → ℤ) :
    ∑ p, d p • P.root (s p) = ∑ k, (A *ᵥ d) k • P.root (r k) := by
  have hroot (p : ι') : P.root (s p) = ∑ k, A k p • P.root (r k) := by
    simp_rw [hA]
    rw [r.sum_comp fun j ↦ b.rootCoefficients (s p) j • P.root j,
      b.sum_rootCoefficients_smul_root]
  simp_rw [hroot, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [mulVec, dotProduct, Finset.sum_smul, mul_comm]

/-- A sum over the positive roots, reindexed along a labelling `s` of the positive roots. -/
private lemma sum_posRootsFinset_eq_sum (s : ι' ≃ posRootsFinset P b) (f : ι → M) :
    ∑ i ∈ posRootsFinset P b, f i = ∑ p, f (s p) :=
  ((posRootsFinset P b).sum_coe_sort f).symm.trans (s.sum_comp fun i ↦ f i).symm

/-- The defining sum of a Kostant partition, in the simple-root coordinates of `A`. -/
private lemma sum_posRootsFinset_smul_root_eq
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (d : ι → ℕ) :
    ∑ i ∈ posRootsFinset P b, d i • P.root i =
      ∑ k, (A *ᵥ fun p ↦ (d (s p) : ℤ)) k • P.root (r k) := by
  rw [← sum_zsmul_root_eq_sum_mulVec_zsmul_root hA, sum_posRootsFinset_eq_sum s]
  simp_rw [natCast_zsmul]

/-- **Kostant partitions are vector partitions.** Let the column `p` of `A` be the column of
simple-root coefficients of the positive root `s p`, with rows labelled by the simple roots along
`r`. Restricting to the positive roots identifies the Kostant partitions of `∑ₖ cₖ α_{r k}` with
the vector partitions of `c` with parts the columns of `A`; the inverse extends by zero. -/
noncomputable def kostantPartitionEquivVectorPartitions
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (c : κ → ℤ) :
    {d : ι → ℕ // IsKostantPartition P b (∑ k, c k • P.root (r k)) d} ≃ A.vectorPartitions c where
  toFun d := ⟨fun p ↦ d.val (s p), mem_vectorPartitions.mpr <|
    b.sum_zsmul_root_comp_injective r <| by
      simp only
      rw [← sum_posRootsFinset_smul_root_eq hA]
      exact ((isKostantPartition_iff P b _ _).mp d.property).2⟩
  invFun d := ⟨extendPosRoots s d.val, (isKostantPartition_iff P b _ _).mpr
    ⟨fun _ hi ↦ mem_posRoots_of_extendPosRoots_ne_zero hi, by
      rw [sum_posRootsFinset_smul_root_eq hA]
      simp_rw [extendPosRoots_apply_coe]
      rw [mem_vectorPartitions.mp d.property]⟩⟩
  left_inv d :=
    Subtype.ext (extendPosRoots_comp ((isKostantPartition_iff P b _ _).mp d.property).1)
  right_inv d := Subtype.ext (funext (extendPosRoots_apply_coe s d.val))

/-- The vector partition attached to a Kostant partition is its restriction to the positive
roots. -/
@[simp]
theorem coe_kostantPartitionEquivVectorPartitions_apply
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (c : κ → ℤ)
    (d : {d : ι → ℕ // IsKostantPartition P b (∑ k, c k • P.root (r k)) d}) (p : ι') :
    (kostantPartitionEquivVectorPartitions hA c d : ι' → ℕ) p = d.val (s p) :=
  (rfl)

/-- The Kostant partition attached to a vector partition `d` takes the value `d p` at the positive
root `s p`. -/
@[simp]
theorem coe_kostantPartitionEquivVectorPartitions_symm_apply
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (c : κ → ℤ) (d : A.vectorPartitions c)
    (p : ι') : ((kostantPartitionEquivVectorPartitions hA c).symm d : ι → ℕ) (s p) = d.val p :=
  extendPosRoots_apply_coe s d.val p

/-- **The Kostant partition function is a vector partition function.** If the column `p` of `A` is
the column of simple-root coefficients of the positive root `s p`, with rows labelled by the simple
roots along `r`, then `P(∑ₖ cₖ α_{r k})` is the number of vectors `d` of natural numbers with
`A *ᵥ d = c`. -/
theorem kostantPartition_eq_vectorPartitionCount
    (hA : ∀ k p, A k p = b.rootCoefficients (s p) (r k)) (c : κ → ℤ) :
    kostantPartition P b (∑ k, c k • P.root (r k)) = A.vectorPartitionCount c := by
  rw [kostantPartition_def, vectorPartitionCount_def]
  exact Nat.card_congr (kostantPartitionEquivVectorPartitions hA c)

end TauCeti
