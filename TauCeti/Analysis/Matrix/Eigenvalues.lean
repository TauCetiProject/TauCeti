/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.Matrix.EntrywiseOpNorm

/-!
# Perturbation bounds and rank cutoffs for sorted matrix eigenvalues

For a Hermitian matrix over `RCLike`, an entrywise perturbation of size `ε` changes each
sorted eigenvalue by at most `card ι * ε`. An entrywise bound on the matrix itself gives the
same a-priori bound on the absolute values of its eigenvalues. These estimates connect
coordinatewise error bounds to spectral error bounds for random matrices.

A perturbation smaller than the distance of a sorted eigenvalue from a real threshold
preserves its membership in `[c, ∞)`. Thus perturbations smaller than a spectral gap
preserve the number of eigenvalues above the threshold, counted with multiplicity.
This is the rank stability used when selecting a spectral subspace by a fixed threshold.
The norm in these threshold results is the Euclidean operator norm, selected by
`Matrix.Norms.L2Operator`.

All statements use Mathlib's decreasing enumeration `Matrix.IsHermitian.eigenvalues₀`,
including multiplicities. For positive-semidefinite matrices its nonzero entries form an
initial segment of length equal to the rank. Thus a rank bound is equivalent to vanishing
of the corresponding sorted tail. Arbitrary finite index types, including empty ones, are
allowed.

The perturbation estimate combines the operator Weyl inequality in
`TauCeti.Analysis.InnerProductSpace.CourantFischer` with the entrywise operator bound in
`TauCeti.Analysis.Matrix.EntrywiseOpNorm`. The rank count reindexes Mathlib's
`Matrix.IsHermitian.rank_eq_card_non_zero_eigs` to the sorted enumeration.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 4.3.1 (Weyl's perturbation inequality).
* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018),
  Chapter 4 (matrix norm bounds and spectral estimates).
-/

public section

namespace TauCeti

open Matrix
open scoped ComplexOrder

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {A B : Matrix ι ι 𝕜}

/-- Entrywise perturbations of size `ε` change every sorted eigenvalue of a Hermitian matrix
by at most `card ι * ε`. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalues₀_sub_le_of_entry_le
    (hA : A.IsHermitian) (hB : B.IsHermitian) {ε : ℝ}
    (hentry : ∀ i j, ‖A i j - B i j‖ ≤ ε) (k : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ (Fintype.card ι : ℝ) * ε := by
  -- Unfold only the sorted enumeration to use its defining operator-level API.
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (fun x ↦ ?_) k
  simpa only [map_sub] using
    norm_toEuclideanLin_le_of_entry_le_square (A := A - B) hentry x

/-- An entrywise bound on a Hermitian matrix bounds the absolute value of each sorted
eigenvalue by the matrix size times that bound. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalues₀_le_of_entry_le (hA : A.IsHermitian) {β : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ β) (k : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ k| ≤ (Fintype.card ι : ℝ) * β := by
  have hZ : (0 : Matrix ι ι 𝕜).IsHermitian := isHermitian_zero
  have hzero : hZ.eigenvalues₀ k = 0 := by
    -- Unfold the matrix-indexed enumeration to reindex Mathlib's zero-eigenvalue result.
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply, Pi.zero_apply] using
      congrFun (hZ.eigenvalues_eq_zero_iff.mpr rfl)
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) k)
  simpa only [hzero, sub_zero] using hA.abs_eigenvalues₀_sub_le_of_entry_le hZ
    (by simpa only [Matrix.zero_apply, sub_zero] using hentry) k

section

open scoped Matrix.Norms.L2Operator

/-- A Hermitian perturbation smaller than the distance of a sorted eigenvalue from `c`
preserves whether that eigenvalue belongs to `[c, ∞)`. The norm is the Euclidean operator
norm. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues₀_iff_of_norm_sub_lt
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {c : ℝ} (i : Fin (Fintype.card ι))
    (hgap : ‖A - B‖ < |hA.eigenvalues₀ i - c|) :
    c ≤ hB.eigenvalues₀ i ↔ c ≤ hA.eigenvalues₀ i := by
  have hweyl : |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
    -- The matrix enumeration is defined using the symmetric Euclidean operator.
    simp only [Matrix.IsHermitian.eigenvalues₀]
    simpa only [coe_toEuclideanCLM_eq_toEuclideanLin, ← map_sub,
      l2_opNorm_toEuclideanCLM] using
      LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm
        (T := toEuclideanCLM (𝕜 := 𝕜) A) (S := toEuclideanCLM (𝕜 := 𝕜) B)
        (by simpa only [coe_toEuclideanCLM_eq_toEuclideanLin] using
          isSymmetric_toEuclideanLin_iff.mpr hA)
        (by simpa only [coe_toEuclideanCLM_eq_toEuclideanLin] using
          isSymmetric_toEuclideanLin_iff.mpr hB)
        finrank_euclideanSpace i
  obtain ⟨hlower, hupper⟩ := abs_le.mp hweyl
  by_cases hside : c ≤ hA.eigenvalues₀ i
  · rw [abs_of_nonneg (sub_nonneg.mpr hside)] at hgap
    exact iff_of_true (by linarith) hside
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hside))] at hgap
    exact iff_of_false (by linarith) hside

/-- Hermitian perturbations of Euclidean operator norm less than a spectral gap around
`c` preserve the number of eigenvalues in `[c, ∞)`, with multiplicity. The gap bound may
be attained, and the matrix index type may be empty. -/
theorem _root_.Matrix.IsHermitian.card_eigenvalues₀_ge_eq_of_norm_sub_lt
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {c δ : ℝ} (hgap : ∀ i, δ ≤ |hA.eigenvalues₀ i - c|) (hpert : ‖A - B‖ < δ) :
    Nat.card {i : Fin (Fintype.card ι) // c ≤ hB.eigenvalues₀ i} =
      Nat.card {i : Fin (Fintype.card ι) // c ≤ hA.eigenvalues₀ i} := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i ↦
    hA.le_eigenvalues₀_iff_of_norm_sub_lt hB i (hpert.trans_le (hgap i)))

end

/-- Reindexing a sorted eigenvalue by the canonical finite equivalence gives the
corresponding matrix-indexed eigenvalue. -/
@[simp]
theorem _root_.Matrix.IsHermitian.eigenvalues_apply_equivOfCardEq (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) i) =
      hA.eigenvalues₀ i := by
  simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- The rank of a Hermitian matrix counts its nonzero sorted eigenvalues, with multiplicity. -/
theorem _root_.Matrix.IsHermitian.rank_eq_card_non_zero_eigenvalues₀ (hA : A.IsHermitian) :
    A.rank = Fintype.card {i : Fin (Fintype.card ι) // hA.eigenvalues₀ i ≠ 0} := by
  classical
  rw [hA.rank_eq_card_non_zero_eigs]
  exact Fintype.card_congr
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm.subtypeEquiv
      (fun _ ↦ by rw [← hA.eigenvalues_apply_equivOfCardEq, Equiv.apply_symm_apply]))

/-- Every entry of the sorted eigenvalue list of a positive-semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.eigenvalues₀_nonneg
    (hA : A.PosSemidef) (i : Fin (Fintype.card ι)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  simpa only [hA.isHermitian.eigenvalues_apply_equivOfCardEq] using
    hA.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) i)

/-- A sorted eigenvalue of a positive-semidefinite matrix vanishes from the rank onward. -/
theorem _root_.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le
    (hA : A.PosSemidef) {d : ℕ} (hrank : A.rank ≤ d)
    (i : Fin (Fintype.card ι)) (hi : d ≤ (i : ℕ)) : hA.isHermitian.eigenvalues₀ i = 0 := by
  classical
  by_contra hne
  have hpos : 0 < hA.isHermitian.eigenvalues₀ i :=
    lt_of_le_of_ne (hA.eigenvalues₀_nonneg i) (Ne.symm hne)
  have hcard : i.val < A.rank := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigenvalues₀, Fintype.card_subtype]
    simpa only [fun j ↦ (hA.eigenvalues₀_nonneg j).lt_iff_ne, ne_comm] using
      (Tuple.lt_card_gt_iff_apply_gt_of_antitone
        hA.isHermitian.eigenvalues₀_antitone).mpr hpos
  omega

/-- A positive-semidefinite matrix has rank at most `d` exactly when its sorted eigenvalues
vanish at all indices at least `d`. The criterion also applies when `d` exceeds the size. -/
theorem _root_.Matrix.PosSemidef.rank_le_iff_eigenvalues₀_eq_zero (hA : A.PosSemidef)
    (d : ℕ) :
    A.rank ≤ d ↔ ∀ i : Fin (Fintype.card ι), d ≤ (i : ℕ) →
      hA.isHermitian.eigenvalues₀ i = 0 := by
  classical
  refine ⟨fun h i hi ↦ hA.eigenvalues₀_eq_zero_of_rank_le h i hi, fun h ↦ ?_⟩
  rw [hA.isHermitian.rank_eq_card_non_zero_eigenvalues₀]
  let f : {i : Fin (Fintype.card ι) // hA.isHermitian.eigenvalues₀ i ≠ 0} → Fin d :=
    fun i ↦ ⟨i.1.val, lt_of_not_ge fun hi ↦ i.2 (h i.1 hi)⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (Fin.ext (congrArg (fun x : Fin d ↦ x.val) hij))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end TauCeti
