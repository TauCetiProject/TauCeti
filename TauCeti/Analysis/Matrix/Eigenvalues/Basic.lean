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
import TauCeti.LinearAlgebra.Matrix.Rank

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

Weyl's additive inequalities `λₖ(A + B) ≤ λᵢ(A) + λⱼ(B)` for `i + j ≤ k`, and their lower
counterpart, are the matrix forms of the operator inequalities in
`TauCeti.Analysis.InnerProductSpace.CourantFischer`. A Hermitian matrix of rank at most `r` has
at most `r` positive eigenvalues, so a perturbation `A - B` of rank at most `r` gives the rank
interlacing `λ_{i+r}(A) ≤ λᵢ(B)`. Consequently the numbers of eigenvalues of `A` and `B` in
`(-∞, t]`, counted with multiplicity, differ by at most `rank (A - B)` for every `t`. Divided by
the size, this is the uniform bound on the difference of the distribution functions of the
empirical spectral measures that drives truncation arguments for random matrices.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 4.3.1 (Weyl's perturbation inequality).
* R. Bhatia, *Matrix Analysis*, Springer (1997), Theorem III.2.1 (Weyl's inequalities).
* Z. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer (2010), Theorem A.43 (the rank inequality for spectral distribution functions).
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

/-- **Weyl's perturbation bound** for ordered eigenvalues of Hermitian matrices: corresponding
eigenvalues differ by at most the Euclidean operator norm of the matrix difference. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalues₀_sub_le_norm
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
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

/-- A Hermitian perturbation smaller than the distance of a sorted eigenvalue from `c`
preserves whether that eigenvalue belongs to `[c, ∞)`. The norm is the Euclidean operator
norm. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues₀_iff_of_norm_sub_lt
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {c : ℝ} (i : Fin (Fintype.card ι))
    (hgap : ‖A - B‖ < |hA.eigenvalues₀ i - c|) :
    c ≤ hB.eigenvalues₀ i ↔ c ≤ hA.eigenvalues₀ i := by
  have hweyl := hA.abs_eigenvalues₀_sub_le_norm hB i
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

/-! ### Weyl's additive inequalities and rank perturbations -/

/-- **Weyl's additive inequality** for Hermitian matrices, upper form: if `i + j ≤ k`, then
`λₖ(A + B) ≤ λᵢ(A) + λⱼ(B)` for the decreasing enumerations `eigenvalues₀`. For `k = i + j`
this is the classical `λ_{i+j-1}(A + B) ≤ λᵢ(A) + λⱼ(B)` in one-based indexing. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_add_le (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j k : Fin (Fintype.card ι)} (hk : (i : ℕ) + j ≤ k) :
    (hA.add hB).eigenvalues₀ k ≤ hA.eigenvalues₀ i + hB.eigenvalues₀ j := by
  have hA' := isSymmetric_toEuclideanLin_iff.mpr hA
  have hB' := isSymmetric_toEuclideanLin_iff.mpr hB
  have h := hA'.eigenvalues_add_le hB' finrank_euclideanSpace hk
  rw [LinearMap.IsSymmetric.eigenvalues_congr (map_add toEuclideanLin A B).symm (hA'.add hB')
    (isSymmetric_toEuclideanLin_iff.mpr (hA.add hB))] at h
  -- The matrix enumeration is defined using the symmetric Euclidean operator.
  simpa only [Matrix.IsHermitian.eigenvalues₀] using h

/-- **Weyl's additive inequality** for Hermitian matrices, lower form: if
`k + card ι ≤ i + j + 1`, then `λᵢ(A) + λⱼ(B) ≤ λₖ(A + B)` for the decreasing enumerations
`eigenvalues₀`. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues₀_add (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j k : Fin (Fintype.card ι)} (hk : (k : ℕ) + Fintype.card ι ≤ i + j + 1) :
    hA.eigenvalues₀ i + hB.eigenvalues₀ j ≤ (hA.add hB).eigenvalues₀ k := by
  have hA' := isSymmetric_toEuclideanLin_iff.mpr hA
  have hB' := isSymmetric_toEuclideanLin_iff.mpr hB
  have h := hA'.le_eigenvalues_add hB' finrank_euclideanSpace hk
  rw [LinearMap.IsSymmetric.eigenvalues_congr (map_add toEuclideanLin A B).symm (hA'.add hB')
    (isSymmetric_toEuclideanLin_iff.mpr (hA.add hB))] at h
  -- The matrix enumeration is defined using the symmetric Euclidean operator.
  simpa only [Matrix.IsHermitian.eigenvalues₀] using h

/-- A Hermitian matrix of rank at most `r` has at most `r` positive eigenvalues: its sorted
eigenvalues are nonpositive from index `r` on. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_nonpos_of_rank_le (hA : A.IsHermitian) {r : ℕ}
    (hrank : A.rank ≤ r) (i : Fin (Fintype.card ι)) (hi : r ≤ (i : ℕ)) :
    hA.eigenvalues₀ i ≤ 0 := by
  classical
  by_contra! hpos
  -- The eigenvalues at indices `0, …, i` are all positive, hence nonzero.
  have hcard : (i : ℕ) < A.rank := by
    rw [hA.rank_eq_card_non_zero_eigenvalues₀, Fintype.card_subtype]
    refine ((Tuple.lt_card_gt_iff_apply_gt_of_antitone hA.eigenvalues₀_antitone).mpr hpos).trans_le
      (Finset.card_le_card fun j hj ↦ ?_)
    simp only [Finset.mem_filter_univ] at hj ⊢
    exact hj.ne'
  omega

/-- **Rank interlacing.** If `A - B` has rank at most `r`, then `λ_{i+r}(A) ≤ λᵢ(B)`: a
Hermitian perturbation of rank at most `r` raises each sorted eigenvalue no higher than the one
`r` places before it. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_of_rank_sub_le (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℕ} (hrank : (A - B).rank ≤ r) {i k : Fin (Fintype.card ι)}
    (hk : (i : ℕ) + r ≤ k) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ i := by
  obtain ⟨C, rfl⟩ : ∃ C, A = B + C := ⟨A - B, (add_sub_cancel B A).symm⟩
  have hC : C.IsHermitian := by simpa using hA.sub hB
  rw [add_sub_cancel_left] at hrank
  have hr : r < Fintype.card ι := by omega
  calc hA.eigenvalues₀ k
      -- Both sides enumerate the eigenvalues of `B + C`; only the Hermitian proofs differ.
      = (hB.add hC).eigenvalues₀ k := rfl
    _ ≤ hB.eigenvalues₀ i + hC.eigenvalues₀ ⟨r, hr⟩ := hB.eigenvalues₀_add_le hC hk
    _ ≤ hB.eigenvalues₀ i :=
        add_le_of_nonpos_right (hC.eigenvalues₀_nonpos_of_rank_le hrank _ le_rfl)

open Finset in
/-- **Rank perturbation of eigenvalue counts.** Passing from `B` to `A` increases the number of
sorted eigenvalues in `(-∞, t]`, counted with multiplicity, by at most `rank (A - B)`. -/
theorem _root_.Matrix.IsHermitian.card_eigenvalues₀_le_le_card_add_rank (hA : A.IsHermitian)
    (hB : B.IsHermitian) (t : ℝ) :
    #{i | hA.eigenvalues₀ i ≤ t} ≤ #{i | hB.eigenvalues₀ i ≤ t} + (A - B).rank := by
  set r := (A - B).rank
  have hrank : (B - A).rank ≤ r := by rw [← neg_sub, Matrix.rank_neg]
  -- Shift the indices of `A` by `r`: by rank interlacing those staying below the size index
  -- eigenvalues of `B` in `(-∞, t]`, and at most `r` of them overshoot.
  calc #{i | hA.eigenvalues₀ i ≤ t}
      = #(({i | hA.eigenvalues₀ i ≤ t} : Finset _).image fun i : Fin _ ↦ (i : ℕ) + r) :=
        (card_image_of_injective _ fun i j h ↦ Fin.ext (by simpa using h)).symm
    _ ≤ #((({i | hB.eigenvalues₀ i ≤ t} : Finset _).image Fin.val) ∪
          Ico (Fintype.card ι) (Fintype.card ι + r)) := by
        refine card_le_card fun m hm ↦ ?_
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
        rw [mem_filter_univ] at hi
        rw [mem_union, mem_image, mem_Ico]
        by_cases h : (i : ℕ) + r < Fintype.card ι
        · refine Or.inl ⟨⟨i + r, h⟩, ?_, rfl⟩
          rw [mem_filter_univ]
          exact (hB.eigenvalues₀_le_of_rank_sub_le hA hrank le_rfl).trans hi
        · exact Or.inr ⟨by omega, by omega⟩
    _ ≤ #({i | hB.eigenvalues₀ i ≤ t} : Finset _) + r := by
        refine (card_union_le _ _).trans ?_
        rw [card_image_of_injective _ Fin.val_injective, Nat.card_Ico]
        omega

open Finset in
/-- **Rank perturbation bound for eigenvalue counts.** The numbers of sorted eigenvalues of two
Hermitian matrices in `(-∞, t]`, counted with multiplicity, differ by at most the rank of their
difference. -/
theorem _root_.Matrix.IsHermitian.abs_card_eigenvalues₀_le_sub_card_le_rank (hA : A.IsHermitian)
    (hB : B.IsHermitian) (t : ℝ) :
    |(#{i | hA.eigenvalues₀ i ≤ t} : ℤ) - #{i | hB.eigenvalues₀ i ≤ t}| ≤ (A - B).rank := by
  have hAB := hA.card_eigenvalues₀_le_le_card_add_rank hB t
  have hBA := hB.card_eigenvalues₀_le_le_card_add_rank hA t
  rw [← neg_sub, Matrix.rank_neg] at hBA
  rw [abs_le]
  constructor <;> omega

end TauCeti
