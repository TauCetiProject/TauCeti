/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import TauCeti.Data.Fintype.Fiber

/-!
# Monomials in the entries of a lower-triangular Gram matrix

For a lower-triangular matrix `L`, the entry `(L * Lᵀ) i j` is the sum of `L i k * L j k` over
the columns `k ≤ min i j`. Hence a monomial `∏ (L * Lᵀ) i j ^ n (i, j)` expands into a finite sum
of monomials in the entries of `L`. The expansion is indexed by choosing one such column for every
occurrence of every entry `(i, j)`. The multi-index of the resulting monomial in `L` counts how
often each entry of `L` is selected, and it is supported on or below the diagonal.

This reduces moments of entries of `L * Lᵀ` to moments of monomials in the entries of `L`, for
any lower-triangular factor.

## Main results

* `TauCeti.mulTransposeExpansionChoice`: the column choices indexing the expansion.
* `TauCeti.mulTransposeExpansionPower`: the multi-index in `L` of the term for one choice.
* `Matrix.IsLowerTriangular.prod_mul_transpose_apply_pow_eq_sum`: the monomial expansion.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- A choice, for every occurrence of every entry `(i, j)` in a monomial in the entries of
`L * Lᵀ`, of a column `k ≤ min i j` of the lower-triangular factor `L`. -/
abbrev mulTransposeExpansionChoice (n : ι × ι → ℕ) :=
  (ij : ι × ι) → Fin (n ij) → {k : ι // k ≤ min ij.1 ij.2}

/-- The entry of `L` selected by one side of one occurrence: occurrence `r` of `(i, j)` with
chosen column `k` contributes the factors `L i k` and `L j k`. -/
private def mulTransposeExpansionIndex {n : ι × ι → ℕ} (c : mulTransposeExpansionChoice n)
    (a : (Σ ij, Fin (n ij)) × Fin 2) : ι × ι :=
  (if a.2 = 0 then a.1.1.1 else a.1.1.2, c a.1.1 a.1.2)

omit [Fintype ι] in
@[simp]
private theorem mulTransposeExpansionIndex_zero {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (a : Σ ij, Fin (n ij)) :
    mulTransposeExpansionIndex c (a, 0) = (a.1.1, (c a.1 a.2 : ι)) := by
  simp [mulTransposeExpansionIndex]

omit [Fintype ι] in
@[simp]
private theorem mulTransposeExpansionIndex_one {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (a : Σ ij, Fin (n ij)) :
    mulTransposeExpansionIndex c (a, 1) = (a.1.2, (c a.1 a.2 : ι)) := by
  simp [mulTransposeExpansionIndex]

omit [Fintype ι] in
private theorem mulTransposeExpansionIndex_snd_le {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (a : (Σ ij, Fin (n ij)) × Fin 2) :
    (mulTransposeExpansionIndex c a).2 ≤ (mulTransposeExpansionIndex c a).1 := by
  have h := (c a.1.1 a.1.2).property
  unfold mulTransposeExpansionIndex
  split_ifs
  · exact h.trans (min_le_left _ _)
  · exact h.trans (min_le_right _ _)

/-- The multi-index in the entries of `L` of the term of the expansion of a monomial in the
entries of `L * Lᵀ` given by a column choice. -/
def mulTransposeExpansionPower {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (q : ι × ι) : ℕ :=
  ∑ ij, ∑ r : Fin (n ij),
    ((if (ij.1, (c ij r : ι)) = q then 1 else 0) +
      if (ij.2, (c ij r : ι)) = q then 1 else 0)

/-- The multi-index counts, over all occurrences, how often `q` is the left factor `(i, k)` or
the right factor `(j, k)` selected by the chosen column `k`. -/
theorem mulTransposeExpansionPower_eq_sum {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (q : ι × ι) :
    mulTransposeExpansionPower c q =
      ∑ ij, ∑ r : Fin (n ij),
        ((if (ij.1, (c ij r : ι)) = q then 1 else 0) +
          if (ij.2, (c ij r : ι)) = q then 1 else 0) := by
  unfold mulTransposeExpansionPower
  rfl

private theorem mulTransposeExpansionPower_eq_occCount {n : ι × ι → ℕ}
    (c : mulTransposeExpansionChoice n) (q : ι × ι) :
    mulTransposeExpansionPower c q = Function.occCount (mulTransposeExpansionIndex c) q := by
  rw [mulTransposeExpansionPower_eq_sum]
  symm
  rw [Function.occCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ fun ij ↦ Fintype.sum_congr _ _ fun r ↦ ?_
  simp only [Fin.sum_univ_two, mulTransposeExpansionIndex_zero,
    mulTransposeExpansionIndex_one]

/-- The multi-index vanishes above the diagonal. -/
@[simp]
theorem mulTransposeExpansionPower_of_lt {n : ι × ι → ℕ} (c : mulTransposeExpansionChoice n)
    {q : ι × ι} (hq : q.1 < q.2) : mulTransposeExpansionPower c q = 0 :=
  mulTransposeExpansionPower_eq_occCount c q |>.trans <|
    Function.occCount_of_notMem_range _ _ fun ⟨a, ha⟩ ↦
      (mulTransposeExpansionIndex_snd_le c a).not_gt (ha ▸ hq)

/-- The empty monomial expands to the single term with zero multi-index. -/
@[simp]
theorem mulTransposeExpansionPower_zero (c : mulTransposeExpansionChoice (0 : ι × ι → ℕ)) :
    mulTransposeExpansionPower c = 0 := by
  funext q
  simp [mulTransposeExpansionPower]

/-- A term of the expansion, written as paired factors `L i k * L j k`, is the monomial in the
entries of `L` with multi-index `mulTransposeExpansionPower c`. -/
private theorem prod_apply_mul_apply_eq_prod_pow {M : Type*} [CommMonoid M]
    (L : Matrix ι ι M) {n : ι × ι → ℕ} (c : mulTransposeExpansionChoice n) :
    (∏ a : Σ ij, Fin (n ij), L a.1.1 (c a.1 a.2) * L a.1.2 (c a.1 a.2)) =
      ∏ q, L q.1 q.2 ^ mulTransposeExpansionPower c q := by
  simp_rw [mulTransposeExpansionPower_eq_occCount]
  rw [Function.prod_occCount_pow (T := Finset.univ) _ (fun _ ↦ Finset.mem_univ _)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro ij _
  simp only [Fin.prod_univ_two, mulTransposeExpansionIndex_zero,
    mulTransposeExpansionIndex_one]

end TauCeti

namespace Matrix.IsLowerTriangular

open TauCeti

variable {ι R : Type*} [LinearOrder ι] [Fintype ι]

/-- A monomial in the entries of `L * Lᵀ` for lower-triangular `L` is the finite sum, over all
choices of a column `k ≤ min i j` for each occurrence of each entry `(i, j)`, of the
corresponding monomials in the entries of `L`. -/
theorem prod_mul_transpose_apply_pow_eq_sum [CommSemiring R] {L : Matrix ι ι R}
    (hL : L.IsLowerTriangular) (n : ι × ι → ℕ) :
    (∏ ij, (L * Lᵀ) ij.1 ij.2 ^ n ij) =
      ∑ c : mulTransposeExpansionChoice n, ∏ q, L q.1 q.2 ^ mulTransposeExpansionPower c q := by
  let _ : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic' ι (fun i ↦ Finset.univ.filter (· ≤ i)) (by simp)
  have hentry (ij : ι × ι) :
      (L * Lᵀ) ij.1 ij.2 ^ n ij =
        ∑ c : Fin (n ij) → {k : ι // k ≤ min ij.1 ij.2},
          ∏ r, L ij.1 (c r) * L ij.2 (c r) := by
    rw [hL.mul_transpose_apply_eq_sum_Iic,
      Finset.sum_subtype (Finset.Iic (min ij.1 ij.2)) (fun _ ↦ Finset.mem_Iic), Fintype.sum_pow]
  simp_rw [hentry]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← prod_apply_mul_apply_eq_prod_pow L c, Fintype.prod_sigma]

end Matrix.IsLowerTriangular
