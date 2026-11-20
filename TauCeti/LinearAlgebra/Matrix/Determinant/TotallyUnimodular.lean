/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Order.Interval.Set.OrdConnected
public import TauCeti.LinearAlgebra.Matrix.SuperdiagonalShift

/-!
# Totally unimodular matrices: signed incidence and interval matrices

This file proves two classical sufficient criteria for `Matrix.IsTotallyUnimodular`.

1. **Signed incidence matrices.** If every column of `A` has the form
   `P.indicator 1 - N.indicator 1` with `P` and `N` subsingletons, that is, every column
   has at most one entry `1`, at most one entry `-1` and zeros elsewhere, then `A` is totally
   unimodular. The incidence matrix of a directed graph is the basic example. The proof is
   Poincaré's induction: a square submatrix either has a column with at most one nonzero
   entry, along which one expands, or all its columns sum to zero, so its determinant
   vanishes.
2. **Interval matrices.** If the rows of `A` are indexed by a linear order and every column of
   `A` is the indicator of an order-connected set of rows (the *consecutive-ones property* for
   columns), then `A` is totally unimodular. After sorting the rows of a square submatrix, its
   columns are indicators of intervals; the row-difference operator
   `1 - TauCeti.superdiagonalShift k`, which has determinant one, turns each such column into
   one with at most one `1` and at most one `-1`, and the first criterion applies.

Interval matrices are the constraint matrices of the type-A Kostant partition function in
simple-root coordinates, where total unimodularity is one of the hypotheses under which vector
partition counts are piecewise polynomial.

## Main results

* `Matrix.isTotallyUnimodular_of_col_eq_indicator_sub_indicator`: matrices whose columns have at
  most one `1`, at most one `-1` and zeros elsewhere are totally unimodular.
* `Matrix.isTotallyUnimodular_of_col_eq_indicator_ordConnected`: matrices whose columns are
  indicators of order-connected sets of rows are totally unimodular.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §19.3.
* S. Billey, V. Guillemin and E. Rassart, *A vector partition function for the multiplicities
  of `sl_k ℂ`*, J. Algebra **278** (2004), 251–293, Lemma 1.6.
-/

public section

open Function

namespace Matrix

variable {m n R : Type*} [CommRing R]

/-- A column of the form `P.indicator 1 - N.indicator 1` with `P`, `N` subsingletons is preserved
by restricting the rows along an injective map. -/
private theorem exists_col_eq_indicator_sub_indicator_comp {k : Type*} {f : k → m}
    (hf : Injective f) {c : m → R}
    (hc : ∃ P N : Set m, P.Subsingleton ∧ N.Subsingleton ∧
      ∀ i, c i = P.indicator 1 i - N.indicator 1 i) :
    ∃ P N : Set k, P.Subsingleton ∧ N.Subsingleton ∧
      ∀ i, c (f i) = P.indicator 1 i - N.indicator 1 i := by
  obtain ⟨P, N, hP, hN, hc⟩ := hc
  refine ⟨f ⁻¹' P, f ⁻¹' N, hP.preimage hf, hN.preimage hf, fun i ↦ ?_⟩
  simp only [hc, ← Set.indicator_comp_right, Pi.one_comp]

/-- A column of the form `P.indicator 1 - N.indicator 1` with `P`, `N` nonempty subsingletons sums
to zero. -/
private theorem sum_indicator_sub_indicator_eq_zero {k : Type*} [Fintype k] {P N : Set k}
    (hP : P.Subsingleton) (hN : N.Subsingleton) (hP₀ : P.Nonempty) (hN₀ : N.Nonempty) :
    ∑ i, (P.indicator (1 : k → R) i - N.indicator 1 i) = 0 := by
  classical
  obtain ⟨a, rfl⟩ := (hP.eq_empty_or_singleton.resolve_left hP₀.ne_empty)
  obtain ⟨b, rfl⟩ := (hN.eq_empty_or_singleton.resolve_left hN₀.ne_empty)
  simp [Finset.sum_sub_distrib]

/-- If one column of a square matrix vanishes outside one row and the corresponding entry and
complementary minor have determinant in the range of `SignType.cast`, so does the matrix. -/
private theorem det_mem_range_signType_cast_of_col {k : ℕ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) R}
    {a j : Fin (k + 1)} (hcol : ∀ i, i ≠ a → M i j = 0) (ha : M a j ∈ Set.range SignType.cast)
    (hminor : (M.submatrix a.succAbove j.succAbove).det ∈ Set.range SignType.cast) :
    M.det ∈ Set.range SignType.cast := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hminor
  rw [det_succ_column M j, Fintype.sum_eq_single a fun i hi ↦ by simp [hcol i hi]]
  exact ⟨(-1) ^ ((a : ℕ) + j) * s * t, by simp [hs, ht]⟩

/-- The square case of `isTotallyUnimodular_of_col_eq_indicator_sub_indicator`, by induction on
the size: either some column has at most one nonzero entry, and one expands along it, or every
column sums to zero and the determinant vanishes. -/
private theorem det_mem_range_signType_cast_of_col_eq_indicator_sub_indicator :
    ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) R),
      (∀ j, ∃ P N : Set (Fin k), P.Subsingleton ∧ N.Subsingleton ∧
        ∀ i, M i j = P.indicator 1 i - N.indicator 1 i) →
      M.det ∈ Set.range SignType.cast
  | 0, M, _ => ⟨1, by simp⟩
  | k + 1, M, hM => by
    choose P N hP hN hPN using hM
    by_cases hall : ∀ j, (P j).Nonempty ∧ (N j).Nonempty
    · -- every column sums to zero, so the all-ones vector lies in the kernel of `Mᵀ`
      refine ⟨0, Eq.symm ?_⟩
      rw [← det_transpose]
      refine det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := fun _ ↦ 1) (i := 0)
        (funext fun j ↦ ?_) (one_mem _)
      simp only [mulVec, dotProduct, transpose_apply, mul_one, Pi.zero_apply, hPN]
      exact sum_indicator_sub_indicator_eq_zero (hP j) (hN j) (hall j).1 (hall j).2
    · -- some column is `±` the indicator of a subsingleton: expand along it
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨S, ε, hS, hcol⟩ : ∃ (S : Set (Fin (k + 1))) (ε : SignType), S.Subsingleton ∧
          ∀ i, M i j = ε * S.indicator 1 i := by
        by_cases hPj : (P j).Nonempty
        · refine ⟨P j, 1, hP j, fun i ↦ ?_⟩
          rw [hPN, hj hPj]
          simp
        · refine ⟨N j, -1, hN j, fun i ↦ ?_⟩
          rw [hPN, Set.not_nonempty_iff_eq_empty.1 hPj]
          simp
      obtain ⟨a, haS⟩ : ∃ a, S ⊆ {a} := by
        rcases hS.eq_empty_or_singleton with rfl | ⟨a, rfl⟩
        exacts [⟨0, Set.empty_subset _⟩, ⟨a, subset_rfl⟩]
      refine det_mem_range_signType_cast_of_col (a := a) (j := j)
        (fun i hi ↦ by rw [hcol, Set.indicator_of_notMem fun h ↦ hi (haS h), mul_zero]) ?_ ?_
      · by_cases haS' : a ∈ S
        · exact ⟨ε, by simp [hcol, haS']⟩
        · exact ⟨0, by simp [hcol, haS']⟩
      · refine det_mem_range_signType_cast_of_col_eq_indicator_sub_indicator k _ fun j' ↦ ?_
        exact exists_col_eq_indicator_sub_indicator_comp Fin.succAbove_right_injective
          ⟨P _, N _, hP _, hN _, hPN _⟩

/-- **Signed incidence matrices are totally unimodular.** A matrix each of whose columns has at
most one entry `1`, at most one entry `-1`, and zeros elsewhere, is totally unimodular. Each
column is written as `P.indicator 1 - N.indicator 1` for subsingletons `P` and `N` of rows; the
incidence matrix of a directed graph has this form. -/
theorem isTotallyUnimodular_of_col_eq_indicator_sub_indicator {A : Matrix m n R}
    (hA : ∀ j, ∃ P N : Set m, P.Subsingleton ∧ N.Subsingleton ∧
      ∀ i, A i j = P.indicator 1 i - N.indicator 1 i) :
    A.IsTotallyUnimodular := fun k _ g hf _ ↦
  det_mem_range_signType_cast_of_col_eq_indicator_sub_indicator k _ fun j ↦
    exists_col_eq_indicator_sub_indicator_comp hf (hA (g j))

/-- The difference of the indicators of an order-connected set `t ⊆ Fin k` at consecutive
positions `i` and `i + 1` (the latter read as `0` past the end) has the form
`P.indicator 1 - N.indicator 1` for subsingletons `P` and `N`: `P` is the last element of `t`
and `N` the position just before the first one. -/
private theorem exists_indicator_sub_indicator_succ {k : ℕ} {t : Set (Fin k)}
    (ht : t.OrdConnected) :
    ∃ P N : Set (Fin k), P.Subsingleton ∧ N.Subsingleton ∧ ∀ i : Fin k,
      t.indicator (1 : Fin k → R) i -
          (if h : (i : ℕ) + 1 < k then t.indicator 1 ⟨i + 1, h⟩ else 0) =
        P.indicator 1 i - N.indicator 1 i := by
  classical
  refine ⟨{i | i ∈ t ∧ ∀ h : (i : ℕ) + 1 < k, (⟨i + 1, h⟩ : Fin k) ∉ t},
    {i | i ∉ t ∧ ∃ h : (i : ℕ) + 1 < k, (⟨i + 1, h⟩ : Fin k) ∈ t}, ?_, ?_, fun i ↦ ?_⟩
  · -- two distinct last elements `x < y` of `t` would put `x + 1 ∈ [x, y] ⊆ t`
    have key : ∀ x y : Fin k, x ∈ t → (∀ h : (x : ℕ) + 1 < k, (⟨x + 1, h⟩ : Fin k) ∉ t) →
        y ∈ t → ¬ x < y := fun x y hx hx' hy hxy ↦
      hx' (by omega) (ht.out hx hy ⟨Fin.le_def.2 (by simp), Fin.le_def.2 (by simp; omega)⟩)
    exact fun x hx y hy ↦ le_antisymm (not_lt.1 (key y x hy.1 hy.2 hx.1))
      (not_lt.1 (key x y hx.1 hx.2 hy.1))
  · -- two distinct predecessors `x < y` of first elements of `t` would put `y ∈ [x + 1, y + 1] ⊆ t`
    have key : ∀ x y : Fin k, (∃ h : (x : ℕ) + 1 < k, (⟨x + 1, h⟩ : Fin k) ∈ t) → y ∉ t →
        (∃ h : (y : ℕ) + 1 < k, (⟨y + 1, h⟩ : Fin k) ∈ t) → ¬ x < y :=
      fun x y ⟨_, hx⟩ hy ⟨_, hy'⟩ hxy ↦
        hy (ht.out hx hy' ⟨Fin.le_def.2 (by simp; omega), Fin.le_def.2 (by simp)⟩)
    exact fun x hx y hy ↦ le_antisymm (not_lt.1 (key y x hy.2 hx.1 hx.2))
      (not_lt.1 (key x y hx.2 hy.1 hy.2))
  · by_cases hi : i ∈ t <;> by_cases h : (i : ℕ) + 1 < k
    · by_cases hs : (⟨i + 1, h⟩ : Fin k) ∈ t <;> simp [Set.indicator, hi, h, hs]
    · simp [Set.indicator, hi, h]
    · by_cases hs : (⟨i + 1, h⟩ : Fin k) ∈ t <;> simp [Set.indicator, hi, h, hs]
    · simp [Set.indicator, hi, h]

/-- The square case of `isTotallyUnimodular_of_col_eq_indicator_ordConnected` with sorted rows:
the row-difference operator `1 - superdiagonalShift k` has determinant one and makes every column
a difference of indicators of subsingletons. -/
private theorem det_mem_range_signType_cast_of_col_eq_indicator_ordConnected {k : ℕ}
    (B : Matrix (Fin k) (Fin k) R)
    (hB : ∀ j, ∃ t : Set (Fin k), t.OrdConnected ∧ ∀ i, B i j = t.indicator 1 i) :
    B.det ∈ Set.range SignType.cast := by
  have hD : (1 - TauCeti.superdiagonalShift k : Matrix (Fin k) (Fin k) R).det = 1 := by
    simpa using (TauCeti.isUpperUnitriangular_one_sub_smul_superdiagonalShift k (1 : R)).det_eq_one
  have hC := isTotallyUnimodular_of_col_eq_indicator_sub_indicator
    (A := (1 - (TauCeti.superdiagonalShift k : Matrix (Fin k) (Fin k) R)) * B) fun j ↦ by
      obtain ⟨t, ht, hBt⟩ := hB j
      obtain ⟨P, N, hP, hN, hPN⟩ := exists_indicator_sub_indicator_succ (R := R) ht
      refine ⟨P, N, hP, hN, fun i ↦ ?_⟩
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, TauCeti.superdiagonalShift_mul_apply,
        ← hPN, hBt]
      split_ifs <;> simp [hBt]
  simpa [det_mul, hD] using (isTotallyUnimodular_iff _).1 hC k id id

/-- **Interval matrices are totally unimodular.** If the rows are indexed by a linear order and
every column is the indicator of an order-connected set of rows (the consecutive-ones property
for columns), the matrix is totally unimodular. -/
theorem isTotallyUnimodular_of_col_eq_indicator_ordConnected [LinearOrder m] {A : Matrix m n R}
    (hA : ∀ j, ∃ s : Set m, s.OrdConnected ∧ ∀ i, A i j = s.indicator 1 i) :
    A.IsTotallyUnimodular := by
  rw [isTotallyUnimodular_iff]
  intro k f g
  -- sort the rows: `f ∘ σ` is monotone, and the columns of the sorted submatrix are indicators
  -- of order-connected subsets of `Fin k`
  set σ := Tuple.sort f
  have hsorted : (A.submatrix (f ∘ σ) g).det ∈ Set.range SignType.cast :=
    det_mem_range_signType_cast_of_col_eq_indicator_ordConnected _ fun j ↦ by
      obtain ⟨s, hs, hAs⟩ := hA (g j)
      refine ⟨(f ∘ σ) ⁻¹' s, hs.preimage_mono (Tuple.monotone_sort f), fun i ↦ ?_⟩
      rw [submatrix_apply, hAs, ← Set.indicator_comp_right (g := (1 : m → R)), Pi.one_comp]
  have hperm : A.submatrix f g = (A.submatrix (f ∘ σ) g).submatrix σ.symm id := by
    simp [submatrix_submatrix, Function.comp_assoc]
  obtain ⟨s, hs⟩ := hsorted
  rw [hperm, det_permute, ← hs]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h
  · exact ⟨s, by simp [h]⟩
  · exact ⟨-s, by simp [h]⟩

end Matrix
