/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization

import Mathlib.Tactic.LinearCombination

/-!
# Degree mutation and column-annihilating gradings

Given an extended integer matrix `B : Matrix I K ℤ` along `row : K ↪ I` and a family of degrees
`g : I → G` in an additive commutative group, a column-annihilating grading satisfies
`∑ i, B i j • g i = 0` for every mutable column `j`, or more generally
`∑ i, (B i j / r j) • g i = 0` when positive exchange degrees `r j` divide their columns.

Mutating `g` in direction `k` replaces `g (row k)` by
`-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i` and fixes all other coordinates.
When `B (row k) k = 0` and column `k` has degree zero, replacing `(-B i k)⁺` by `(B i k)⁺` gives
the same mutated family, and mutating twice in direction `k` recovers `g`. When `B (row k) k = 0`,
degree mutation preserves both divided-column and ordinary column annihilation without any
finiteness assumption on `K`. For finite `K`, the divided matrix `β i j = B i j / r j` satisfies
`Eε * β' = β * F_{r, ε}` for the integral right factor `F_{r, ε} = D_r * Fε * D_r⁻¹`, whose
off-diagonal entries in row `k` are `r k * (ε * (B (row k) j / r j))⁺`.

Iterating along finite mutation words propagates any initial grading while keeping all coordinates
outside `Set.range row` fixed.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §6, Proposition 6.1, for homogeneity and `g`-vector recurrences.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §6,
  for gradings on quantum cluster algebras.
-/

public section

namespace TauCeti

open Matrix

section DividedFactor

variable {I K : Type*} [DecidableEq I] [DecidableEq K]

/-- The integral right mutation factor `D_r * Fε * D_r⁻¹` for divided columns `B i j / r j`:
the identity with row `k` replaced by `-1` on its diagonal and
`r k * (ε * (B (row k) j / r j))⁺` elsewhere. -/
def dividedMatrixMutationRight (row : K ↪ I) (B : Matrix I K ℤ) (r : K → ℤ)
    (k : K) (ε : ℤ) : Matrix K K ℤ :=
  (1 : Matrix K K ℤ).updateRow k fun j ↦
    if j = k then -1 else r k * (ε * (B (row k) j / r j))⁺

variable (row : K ↪ I) (B : Matrix I K ℤ) (r : K → ℤ) (k : K) (ε : ℤ)

omit [DecidableEq I] in
/-- Entrywise formula for the divided right mutation factor. -/
theorem dividedMatrixMutationRight_apply (i j : K) :
    dividedMatrixMutationRight row B r k ε i j =
      if i = k then (if j = k then -1 else r k * (ε * (B (row k) j / r j))⁺)
      else (1 : Matrix K K ℤ) i j := by
  simp [dividedMatrixMutationRight, updateRow_apply]

omit [DecidableEq I] in
@[simp]
theorem dividedMatrixMutationRight_apply_row (j : K) :
    dividedMatrixMutationRight row B r k ε k j =
      if j = k then -1 else r k * (ε * (B (row k) j / r j))⁺ := by
  simp [dividedMatrixMutationRight_apply]

omit [DecidableEq I] in
@[simp]
theorem dividedMatrixMutationRight_apply_of_ne {i : K} (hi : i ≠ k) (j : K) :
    dividedMatrixMutationRight row B r k ε i j = (1 : Matrix K K ℤ) i j := by
  simp [dividedMatrixMutationRight_apply, hi]

omit [DecidableEq I] in
/-- Unit exchange degrees recover the ordinary right mutation factor. -/
@[simp]
theorem dividedMatrixMutationRight_one :
    dividedMatrixMutationRight row B 1 k ε = matrixMutationRight row B k ε := by
  ext i j
  simp [dividedMatrixMutationRight_apply, matrixMutationRight_apply]

omit [DecidableEq I] in
/-- Divided right mutation factors commute with injective restriction of mutable indices and
compatible relabelling of rows. -/
theorem dividedMatrixMutationRight_submatrix {I' K' : Type*} [DecidableEq K'] {row' : K' ↪ I'}
    {f : I' → I} {g : K' → K} (hg : Function.Injective g) (h : ∀ a, f (row' a) = row (g a))
    (k : K') :
    dividedMatrixMutationRight row' (B.submatrix f g) (r ∘ g) k ε =
      (dividedMatrixMutationRight row B r (g k) ε).submatrix g g := by
  ext i j
  simp only [dividedMatrixMutationRight_apply, submatrix_apply, Matrix.one_apply,
    Function.comp_apply, hg.eq_iff, h]

omit [DecidableEq I] in
/-- Negating a matrix whose mutable row `row k` is divisible by the column degrees exchanges the
sign of the divided right factor. -/
theorem dividedMatrixMutationRight_neg (hdvd : ∀ j, r j ∣ B (row k) j) :
    dividedMatrixMutationRight row (-B) r k ε = dividedMatrixMutationRight row B r k (-ε) := by
  ext i j
  simp [dividedMatrixMutationRight_apply, Int.neg_ediv_of_dvd (hdvd j)]

/-- After mutation in direction `k`, the divided right factor uses the opposite sign at the
original matrix when row `row k` is divisible by the column degrees. -/
theorem dividedMatrixMutationRight_matrixMutation (hdvd : ∀ j, r j ∣ B (row k) j) :
    dividedMatrixMutationRight row (matrixMutation row B k) r k ε =
      dividedMatrixMutationRight row B r k (-ε) := by
  ext i j
  simp [dividedMatrixMutationRight_apply, matrixMutation_apply_row, Int.neg_ediv_of_dvd (hdvd j)]

section FiniteK

variable [Fintype K]

omit [DecidableEq I] in
/-- Right multiplication by the divided right factor negates column `k` and adds a multiple of
column `k` to every other column. -/
theorem mul_dividedMatrixMutationRight_apply {J : Type*} (A : Matrix J K ℤ) (i : J) (j : K) :
    (A * dividedMatrixMutationRight row B r k ε) i j =
      if j = k then -A i j else A i j + A i k * (r k * (ε * (B (row k) j / r j))⁺) := by
  by_cases hj : j = k
  · subst j
    simp +contextual [Matrix.mul_apply, dividedMatrixMutationRight_apply, mul_ite]
  · have hcol (l : K) : dividedMatrixMutationRight row B r k ε l j =
        (1 : Matrix K K ℤ) l j + if l = k then r k * (ε * (B (row k) j / r j))⁺ else 0 := by
      by_cases hl : l = k <;> simp_all [Matrix.one_apply, eq_comm]
    simp [Matrix.mul_apply, hcol, mul_add, Finset.sum_add_distrib, mul_ite, hj, Matrix.one_apply]

omit [DecidableEq I] in
/-- The divided right mutation factor is an involution, for all degree and sign parameters. -/
@[simp]
theorem dividedMatrixMutationRight_mul_self :
    dividedMatrixMutationRight row B r k ε * dividedMatrixMutationRight row B r k ε = 1 := by
  ext i j
  rw [mul_dividedMatrixMutationRight_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp_all [dividedMatrixMutationRight_apply, Matrix.one_apply, eq_comm]

omit [DecidableEq I] in
/-- The divided right mutation factor has determinant `-1`. -/
@[simp]
theorem det_dividedMatrixMutationRight :
    (dividedMatrixMutationRight row B r k ε).det = -1 := by
  rw [← det_transpose, dividedMatrixMutationRight, ← updateCol_transpose, transpose_one]
  have h := det_updateCol_sum (1 : Matrix K K ℤ) k fun j ↦
    if j = k then -1 else r k * (ε * (B (row k) j / r j))⁺
  simpa only [smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, det_one] using h

omit [DecidableEq I] in
/-- Positive column degrees dividing row `row k` intertwine the divided right factor with the
ordinary right factor via `F_{r, ε} * diagonal r = diagonal r * Fε`. -/
theorem dividedMatrixMutationRight_mul_diagonal (hr : ∀ j, 0 < r j)
    (hdvd : ∀ j, r j ∣ B (row k) j) :
    dividedMatrixMutationRight row B r k ε * diagonal r =
      diagonal r * matrixMutationRight row B k ε := by
  ext i j
  simp only [mul_diagonal, diagonal_mul, dividedMatrixMutationRight_apply,
    matrixMutationRight_apply]
  by_cases hi : i = k
  · subst i
    by_cases hj : j = k
    · simp [hj]
    · simp only [hj, ite_false, ite_true, mul_assoc]
      congr 1
      rw [posPart_def, posPart_def, max_mul_of_nonneg _ _ (hr j).le, zero_mul,
        mul_assoc, Int.ediv_mul_cancel (hdvd j)]
  · by_cases hj : j = k <;> by_cases hij : i = j <;>
      simp [hi, hj, hij, Matrix.one_apply]

/-- Intertwining identity `Eε * β' = β * F_{r, ε}` for the divided matrix `β i j = B i j / r j`
when `B (row k) k = 0` and positive degrees `r j` divide every column. -/
theorem matrixMutationLeft_mul_ediv [Fintype I] (hr : ∀ j, 0 < r j)
    (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) (hε : ε = 1 ∨ ε = -1) :
    matrixMutationLeft row B k ε * of (fun i j ↦ matrixMutation row B k i j / r j) =
      of (fun i j ↦ B i j / r j) * dividedMatrixMutationRight row B r k ε := by
  set β : Matrix I K ℤ := of fun i j ↦ B i j / r j
  set β' : Matrix I K ℤ := of fun i j ↦ matrixMutation row B k i j / r j
  have hB : β * diagonal r = B := by
    ext i j
    simp [β, mul_diagonal, Int.ediv_mul_cancel (hdvd i j)]
  have hB' : β' * diagonal r = matrixMutation row B k := by
    ext i j
    simp [β', mul_diagonal, Int.ediv_mul_cancel (dvd_matrixMutation (hdvd · j) k i)]
  have hinj : (matrixMutationLeft row B k ε * β') * diagonal r =
      (β * dividedMatrixMutationRight row B r k ε) * diagonal r := by
    calc
      (matrixMutationLeft row B k ε * β') * diagonal r
        = matrixMutationLeft row B k ε * matrixMutation row B k := by
          rw [Matrix.mul_assoc, hB']
      _ = (matrixMutationLeft row B k ε * matrixMutationLeft row B k ε) * B *
          matrixMutationRight row B k ε := by
          rw [matrixMutation_eq_mul row B k ε hkk hε]
          simp only [Matrix.mul_assoc]
      _ = B * matrixMutationRight row B k ε := by
          rw [matrixMutationLeft_mul_self, Matrix.one_mul]
      _ = (β * diagonal r) * matrixMutationRight row B k ε := by
          congr 1
          exact hB.symm
      _ = (β * dividedMatrixMutationRight row B r k ε) * diagonal r := by
          rw [Matrix.mul_assoc,
            ← dividedMatrixMutationRight_mul_diagonal row B r k ε hr (hdvd (row k)),
            Matrix.mul_assoc]
  ext i j
  apply mul_right_cancel₀ (hr j).ne'
  simpa only [mul_diagonal] using congrFun (congrFun hinj i) j

/-- Signed factorization `β' = Eε * β * F_{r, ε}` of the divided mutated matrix. -/
theorem ediv_matrixMutation_eq_mul [Fintype I] (hr : ∀ j, 0 < r j)
    (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) (hε : ε = 1 ∨ ε = -1) :
    of (fun i j ↦ matrixMutation row B k i j / r j) =
      matrixMutationLeft row B k ε * of (fun i j ↦ B i j / r j) *
        dividedMatrixMutationRight row B r k ε := by
  calc
    of (fun i j ↦ matrixMutation row B k i j / r j)
      = (matrixMutationLeft row B k ε * matrixMutationLeft row B k ε) *
          of (fun i j ↦ matrixMutation row B k i j / r j) := by
        rw [matrixMutationLeft_mul_self, Matrix.one_mul]
    _ = matrixMutationLeft row B k ε *
          (matrixMutationLeft row B k ε * of (fun i j ↦ matrixMutation row B k i j / r j)) := by
        rw [Matrix.mul_assoc]
    _ = matrixMutationLeft row B k ε * of (fun i j ↦ B i j / r j) *
          dividedMatrixMutationRight row B r k ε := by
        rw [matrixMutationLeft_mul_ediv row B r k ε hr hdvd hkk hε, Matrix.mul_assoc]

end FiniteK

end DividedFactor

section DegreeMutation

variable {I K I' K' G H : Type*} [DecidableEq I] [Fintype I] [AddCommGroup G] [AddCommGroup H]

/-- Mutate a grading `g : I → G` in direction `k` along `B`: coordinate `row k` becomes
`-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i` and all other coordinates
are unchanged. -/
def degreeMutation (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (g : I → G) : I → G :=
  Function.update g (row k)
    (-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i)

variable (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (g g₁ g₂ : I → G)

/-- Definitional presentation of degree mutation via `Function.update`. -/
theorem degreeMutation_def :
    degreeMutation row B k g =
      Function.update g (row k)
        (-g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i) :=
  (rfl)

/-- Entrywise formula for degree mutation. -/
theorem degreeMutation_apply (j : I) :
    degreeMutation row B k g j =
      if j = row k then -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i
      else g j := by
  simp [degreeMutation, Function.update_apply]

@[simp]
theorem degreeMutation_apply_row :
    degreeMutation row B k g (row k) =
      -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (-B i k)⁺ • g i := by
  simp [degreeMutation]

@[simp]
theorem degreeMutation_apply_of_ne {j : I} (hj : j ≠ row k) :
    degreeMutation row B k g j = g j := by
  simp [degreeMutation, hj]

/-- Coordinates outside the mutable rows are fixed by every degree mutation. -/
@[simp]
theorem degreeMutation_apply_of_notMem_range {j : I} (hj : j ∉ Set.range row) :
    degreeMutation row B k g j = g j :=
  degreeMutation_apply_of_ne row B k g fun h ↦ hj ⟨k, h.symm⟩

/-- When `B (row k) k = 0`, the sum in `degreeMutation` extends over all row indices. -/
theorem degreeMutation_apply_row_of_eq_zero (hkk : B (row k) k = 0) :
    degreeMutation row B k g (row k) = -g (row k) + ∑ i, (-B i k)⁺ • g i := by
  rw [degreeMutation_apply_row, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp [hkk]

/-- Degree mutation acts by the columns of the positive-sign left mutation factor `E₁`. -/
theorem degreeMutation_eq_sum_matrixMutationLeft_smul (j : I) :
    degreeMutation row B k g j = ∑ i, matrixMutationLeft row B k 1 i j • g i := by
  by_cases hj : j = row k
  · subst j
    rw [degreeMutation_apply_row,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
    simp only [matrixMutationLeft_apply_col, ite_true, neg_one_smul, neg_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp [(Finset.mem_erase.mp hi).1]
  · simp [hj, Matrix.one_apply]

@[simp]
theorem degreeMutation_zero : degreeMutation row B k (0 : I → G) = 0 := by
  ext j
  by_cases hj : j = row k <;> simp [degreeMutation_apply, hj]

theorem degreeMutation_add :
    degreeMutation row B k (g₁ + g₂) =
      degreeMutation row B k g₁ + degreeMutation row B k g₂ := by
  ext j
  by_cases hj : j = row k
  · subst j
    simp only [degreeMutation_apply_row, Pi.add_apply, smul_add, Finset.sum_add_distrib, neg_add]
    abel
  · simp [hj]

@[simp]
theorem degreeMutation_neg :
    degreeMutation row B k (-g) = -degreeMutation row B k g := by
  ext j
  by_cases hj : j = row k
  · subst j
    simp only [degreeMutation_apply_row, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib, neg_neg]
    abel
  · simp [hj]

theorem degreeMutation_sub :
    degreeMutation row B k (g₁ - g₂) =
      degreeMutation row B k g₁ - degreeMutation row B k g₂ := by
  simp only [sub_eq_add_neg, degreeMutation_add, degreeMutation_neg]

/-- Additive group homomorphisms commute with degree mutation. -/
theorem comp_degreeMutation (φ : G →+ H) :
    φ ∘ degreeMutation row B k g = degreeMutation row B k (φ ∘ g) := by
  ext j
  by_cases hj : j = row k
  · subst j
    simp [Function.comp_apply, map_sum, map_zsmul]
  · simp [hj]

/-- Evaluating an additive homomorphism on a mutated degree equals mutating the mapped degrees. -/
theorem map_degreeMutation_apply (φ : G →+ H) (j : I) :
    φ (degreeMutation row B k g j) = degreeMutation row B k (φ ∘ g) j :=
  congrFun (comp_degreeMutation row B k g φ) j

/-- When `B (row k) k = 0` and column `k` has total degree zero, either signed left factor `Eε`
(`ε = ±1`) computes degree mutation. -/
theorem degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero
    (hkk : B (row k) k = 0) (hcol : ∑ i, B i k • g i = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (j : I) :
    degreeMutation row B k g j = ∑ i, matrixMutationLeft row B k ε i j • g i := by
  rcases hε with rfl | rfl
  · exact degreeMutation_eq_sum_matrixMutationLeft_smul row B k g j
  · rw [degreeMutation_eq_sum_matrixMutationLeft_smul]
    by_cases hj : j = row k
    · subst j
      apply sub_eq_zero.mp
      rw [← Finset.sum_sub_distrib]
      have hd (i : I) :
          matrixMutationLeft row B k 1 i (row k) • g i -
            matrixMutationLeft row B k (-1) i (row k) • g i = -(B i k • g i) := by
        rw [← sub_smul, matrixMutationLeft_apply_col, matrixMutationLeft_apply_col]
        by_cases hi : i = row k
        · simp [hi, hkk]
        · simp only [hi, ite_false, neg_mul, one_mul, neg_neg, posPart_neg]
          have hsub : (B i k)⁻ - (B i k)⁺ = -B i k := by
            linear_combination -(posPart_sub_negPart (B i k))
          rw [hsub, neg_smul]
      simp_rw [hd]
      rw [Finset.sum_neg_distrib, hcol, neg_zero]
    · simp [matrixMutationLeft_apply_of_ne _ _ _ _ _ hj]

/-- When `B (row k) k = 0` and column `k` has total degree zero, degree mutation in direction `k`
uses `(B i k)⁺` interchangeably with `(-B i k)⁺`. -/
theorem degreeMutation_apply_row_posPart (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row B k g (row k) =
      -g (row k) + ∑ i ∈ Finset.univ.erase (row k), (B i k)⁺ • g i := by
  rw [degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero row B k g hkk hcol
    (Or.inr rfl), ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp only [matrixMutationLeft_apply_col, ite_true, neg_one_smul, neg_neg, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp [(Finset.mem_erase.mp hi).1]

/-- Full-sum positive-part formula for degree mutation when `B (row k) k = 0` and column `k`
has total degree zero. -/
theorem degreeMutation_apply_row_posPart_univ (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row B k g (row k) = -g (row k) + ∑ i, (B i k)⁺ • g i := by
  rw [degreeMutation_apply_row_posPart row B k g hkk hcol,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp [hkk]

/-- Negating the matrix fixes degree mutation in direction `k` when `B (row k) k = 0` and
column `k` has total degree zero. -/
theorem degreeMutation_neg_left (hkk : B (row k) k = 0) (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row (-B) k g = degreeMutation row B k g := by
  ext j
  by_cases hj : j = row k
  · subst j
    rw [degreeMutation_apply_row, degreeMutation_apply_row_posPart row B k g hkk hcol]
    simp
  · simp [hj]

/-- Along the mutation column `k`, the mutated matrix pairs with the mutated degrees by the
negative of the original pairing whenever `B (row k) k = 0`. -/
theorem sum_matrixMutation_col_smul_degreeMutation [DecidableEq K] (hkk : B (row k) k = 0) :
    ∑ i, matrixMutation row B k i k • degreeMutation row B k g i = -∑ i, B i k • g i := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k)),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp only [matrixMutation_apply_col, hkk, neg_zero, zero_smul, zero_add,
    neg_smul, Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [degreeMutation_apply_of_ne row B k g (Finset.mem_erase.mp hi).1]

/-- Mutating along `B` and then along `matrixMutation row B k` in the same direction recovers `g`
whenever `B (row k) k = 0` and column `k` has total degree zero. -/
@[simp]
theorem degreeMutation_degreeMutation [DecidableEq K] (hkk : B (row k) k = 0)
    (hcol : ∑ i, B i k • g i = 0) :
    degreeMutation row (matrixMutation row B k) k (degreeMutation row B k g) = g := by
  ext l
  rw [degreeMutation_eq_sum_matrixMutationLeft_smul, matrixMutationLeft_matrixMutation]
  simp_rw [degreeMutation_eq_sum_matrixMutationLeft_smul_of_sum_smul_eq_zero row B k g hkk hcol
    (Or.inr rfl), Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, mul_comm (matrixMutationLeft row B k (-1) _ l)]
  have hmul (i : I) :
      (∑ j, matrixMutationLeft row B k (-1) i j * matrixMutationLeft row B k (-1) j l) =
        (1 : Matrix I I ℤ) i l := by
    simpa only [Matrix.mul_apply] using
      congrFun (congrFun (matrixMutationLeft_mul_self row B k (-1)) i) l
  simp [hmul, Matrix.one_apply]

/-- Degree mutation commutes with bijective relabelling of all rows and any compatible map of
mutable columns. -/
theorem degreeMutation_submatrix [DecidableEq I'] [Fintype I'] {row' : K' ↪ I'}
    {f : I' → I} {hK : K' → K} (hf : Function.Bijective f)
    (h : ∀ a, f (row' a) = row (hK a)) (k : K') :
    degreeMutation row' (B.submatrix f hK) k (g ∘ f) =
      degreeMutation row B (hK k) g ∘ f := by
  let e : I' ≃ I := Equiv.ofBijective f hf
  ext j
  have hrow : j = row' k ↔ f j = row (hK k) := by rw [← h, hf.injective.eq_iff]
  by_cases hj : j = row' k
  · subst j
    simp only [Function.comp_apply, degreeMutation_apply_row, h]
    congr 1
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    have hcomp :
        ∑ x : I', (-B (f x) (hK k))⁺ • g (f x) = ∑ i : I, (-B i (hK k))⁺ • g i :=
      e.sum_comp (fun i ↦ (-B i (hK k))⁺ • g i)
    simp only [submatrix_apply, h, hcomp]
  · have hfj : f j ≠ row (hK k) := mt hrow.mpr hj
    simp [hj, hfj]

section Preservation

variable [DecidableEq K]

/-- Exact transformation of divided-column pairings under simultaneous matrix and degree mutation,
requiring no finiteness assumption on `K`. -/
theorem sum_ediv_matrixMutation_smul_degreeMutation {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) (j : K) :
    ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i =
      if j = k then -∑ i, (B i k / r k) • g i
      else ∑ i, (B i j / r j) • g i +
        (r k * (B (row k) j / r j)⁺) • ∑ i, (B i k / r k) • g i := by
  have hk0 : B (row k) k / r k = 0 := by simp [hkk]
  by_cases hj : j = k
  · subst j
    simp only [ite_true]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k)),
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
    simp only [matrixMutation_apply_col, hkk, neg_zero, Int.zero_ediv, zero_smul, zero_add]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [degreeMutation_apply_of_ne row B k g (Finset.mem_erase.mp hi).1,
      Int.neg_ediv_of_dvd (hdvd i k), neg_smul]
  · simp only [hj, ite_false]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k)),
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k)),
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
    simp only [hk0, zero_smul, zero_add, degreeMutation_apply_row, smul_add, smul_neg,
      Finset.smul_sum, smul_smul]
    have hrowk : matrixMutation row B k (row k) j / r j = -(B (row k) j / r j) := by
      rw [matrixMutation_apply_row, Int.neg_ediv_of_dvd (hdvd (row k) j)]
    rw [hrowk, neg_smul, neg_neg, add_assoc, add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hne : i ≠ row k := (Finset.mem_erase.mp hi).1
    rw [degreeMutation_apply_of_ne row B k g hne,
      matrixMutation_ediv_apply r hr hdvd k i j]
    simp only [hne, hj, or_self, ite_false, posPart_neg]
    rw [← add_smul, ← add_smul]
    congr 1
    have hbk : (B i k)⁻ = r k * (B i k / r k)⁻ := by
      simp only [negPart_def, mul_max_of_nonneg _ _ (hr k).le, mul_zero,
        mul_neg, Int.mul_ediv_cancel' (hdvd i k)]
    rw [hbk]
    linear_combination
      r k * ((B i k / r k)⁻ * posPart_sub_negPart (B (row k) j / r j) +
        (B (row k) j / r j)⁺ * posPart_sub_negPart (B i k / r k))

/-- Simultaneous matrix and degree mutation preserves divided-column annihilation
`∑ i, (B i j / r j) • g i = 0` when `B (row k) k = 0` and positive degrees `r j` divide every
column. -/
theorem sum_ediv_matrixMutation_smul_degreeMutation_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0)
    (hg : ∀ j, ∑ i, (B i j / r j) • g i = 0) (j : K) :
    ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i = 0 := by
  rw [sum_ediv_matrixMutation_smul_degreeMutation row B k g hr hdvd hkk j]
  simp [hg]

/-- Divided-column annihilation is preserved and reflected by simultaneous matrix and degree
mutation when `B (row k) k = 0` and positive degrees divide every column. -/
theorem forall_sum_ediv_matrixMutation_smul_degreeMutation_eq_zero_iff {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (hkk : B (row k) k = 0) :
    (∀ j, ∑ i, (matrixMutation row B k i j / r j) • degreeMutation row B k g i = 0) ↔
      ∀ j, ∑ i, (B i j / r j) • g i = 0 := by
  refine ⟨fun h' ↦ ?_, fun h ↦
    sum_ediv_matrixMutation_smul_degreeMutation_eq_zero row B k g hr hdvd hkk h⟩
  have hdvd' : ∀ i j, r j ∣ matrixMutation row B k i j :=
    fun i j ↦ dvd_matrixMutation (hdvd · j) k i
  have hkk' : matrixMutation row B k (row k) k = 0 := by simp [hkk]
  have hcol' : ∑ i, matrixMutation row B k i k • degreeMutation row B k g i = 0 := by
    have hdiv := h' k
    have heq (i : I) :
        matrixMutation row B k i k • degreeMutation row B k g i =
          r k • ((matrixMutation row B k i k / r k) • degreeMutation row B k g i) := by
      rw [← mul_smul, Int.mul_ediv_cancel' (hdvd' i k)]
    simp_rw [heq]
    rw [← Finset.smul_sum, hdiv, smul_zero]
  have hcol : ∑ i, B i k • g i = 0 := by
    rw [sum_matrixMutation_col_smul_degreeMutation row B k g hkk, neg_eq_zero] at hcol'
    exact hcol'
  intro j
  have hh := sum_ediv_matrixMutation_smul_degreeMutation_eq_zero row (matrixMutation row B k)
    k (degreeMutation row B k g) hr hdvd' hkk' h' j
  simpa only [matrixMutation_matrixMutation, degreeMutation_degreeMutation row B k g hkk hcol]
    using hh

/-- Simultaneous matrix and degree mutation preserves ordinary column annihilation
`∑ i, B i j • g i = 0` when `B (row k) k = 0`. -/
theorem sum_matrixMutation_smul_degreeMutation_eq_zero (hkk : B (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) (j : K) :
    ∑ i, matrixMutation row B k i j • degreeMutation row B k g i = 0 := by
  simpa using sum_ediv_matrixMutation_smul_degreeMutation_eq_zero row B k g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) hkk (by simpa using hg) j

/-- Ordinary column annihilation is preserved and reflected by simultaneous matrix and degree
mutation when `B (row k) k = 0`. -/
theorem forall_sum_matrixMutation_smul_degreeMutation_eq_zero_iff (hkk : B (row k) k = 0) :
    (∀ j, ∑ i, matrixMutation row B k i j • degreeMutation row B k g i = 0) ↔
      ∀ j, ∑ i, B i j • g i = 0 := by
  simpa using forall_sum_ediv_matrixMutation_smul_degreeMutation_eq_zero_iff row B k g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) hkk

end Preservation

end DegreeMutation

section BlockSum

variable {I₁ I₂ K₁ K₂ G : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [Fintype I₁] [Fintype I₂] [AddCommGroup G]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)
  (g₁ : I₁ → G) (g₂ : I₂ → G)

/-- Mutating a block-diagonal matrix in the first summand mutates the first degree family and
fixes the second. -/
@[simp]
theorem degreeMutation_fromBlocks_inl (k : K₁) :
    degreeMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inl k) (Sum.elim g₁ g₂) =
      Sum.elim (degreeMutation row₁ B₁ k g₁) g₂ := by
  have hrow : (row₁.sumMap row₂) (Sum.inl k) = Sum.inl (row₁ k) := rfl
  ext (i | i)
  · by_cases hi : i = row₁ k
    · subst i
      rw [Sum.elim_inl, ← hrow, degreeMutation_apply_row, degreeMutation_apply_row, hrow]
      simp only [Sum.elim_inl]
      congr 1
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ _),
        Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_sum_type]
      simp
    · have hne : (Sum.inl i : I₁ ⊕ I₂) ≠ (row₁.sumMap row₂) (Sum.inl k) := by
        rw [hrow]; simp [hi]
      simp [degreeMutation_apply_of_ne _ _ _ _ hne, hi]
  · have hne : (Sum.inr i : I₁ ⊕ I₂) ≠ (row₁.sumMap row₂) (Sum.inl k) := by rw [hrow]; simp
    simp [degreeMutation_apply_of_ne _ _ _ _ hne]

/-- Mutating a block-diagonal matrix in the second summand mutates the second degree family and
fixes the first. -/
@[simp]
theorem degreeMutation_fromBlocks_inr (k : K₂) :
    degreeMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inr k) (Sum.elim g₁ g₂) =
      Sum.elim g₁ (degreeMutation row₂ B₂ k g₂) := by
  have hrow : (row₁.sumMap row₂) (Sum.inr k) = Sum.inr (row₂ k) := rfl
  ext (i | i)
  · have hne : (Sum.inl i : I₁ ⊕ I₂) ≠ (row₁.sumMap row₂) (Sum.inr k) := by rw [hrow]; simp
    simp [degreeMutation_apply_of_ne _ _ _ _ hne]
  · by_cases hi : i = row₂ k
    · subst i
      rw [Sum.elim_inr, ← hrow, degreeMutation_apply_row, degreeMutation_apply_row, hrow]
      simp only [Sum.elim_inr]
      congr 1
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ _),
        Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_sum_type]
      simp
    · have hne : (Sum.inr i : I₁ ⊕ I₂) ≠ (row₁.sumMap row₂) (Sum.inr k) := by
        rw [hrow]; simp [hi]
      simp [degreeMutation_apply_of_ne _ _ _ _ hne, hi]

end BlockSum

section Word

variable {I K I' K' G H : Type*} [DecidableEq I] [DecidableEq K] [Fintype I]
  [AddCommGroup G] [AddCommGroup H]

/-- Propagate a grading `g : I → G` along a finite mutation word in reading order, mutating the
underlying matrix simultaneously at each step. -/
def degreeMutationWord (row : K ↪ I) (B : Matrix I K ℤ) (g : I → G) : List K → I → G
  | [] => g
  | k :: w => degreeMutationWord row (matrixMutation row B k) (degreeMutation row B k g) w

variable (row : K ↪ I) (B : Matrix I K ℤ) (g g₁ g₂ : I → G)

@[simp]
theorem degreeMutationWord_nil : degreeMutationWord row B g [] = g :=
  (rfl)

@[simp]
theorem degreeMutationWord_cons (k : K) (w : List K) :
    degreeMutationWord row B g (k :: w) =
      degreeMutationWord row (matrixMutation row B k) (degreeMutation row B k g) w :=
  (rfl)

theorem degreeMutationWord_singleton (k : K) :
    degreeMutationWord row B g [k] = degreeMutation row B k g :=
  (rfl)

/-- Concatenation applies the left word to both the matrix and the grading, followed by the
right word. -/
@[simp]
theorem degreeMutationWord_append (u v : List K) :
    degreeMutationWord row B g (u ++ v) =
      degreeMutationWord row (matrixMutationWord row B u) (degreeMutationWord row B g u) v := by
  induction u generalizing B g with
  | nil => simp
  | cons k u ih =>
    simpa only [List.cons_append, degreeMutationWord_cons, matrixMutationWord_cons] using
      ih (matrixMutation row B k) (degreeMutation row B k g)

/-- Coordinates outside `Set.range row` are fixed along every mutation word. -/
@[simp]
theorem degreeMutationWord_apply_of_notMem_range {j : I} (hj : j ∉ Set.range row) (w : List K) :
    degreeMutationWord row B g w j = g j := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih =>
    rw [degreeMutationWord_cons, ih, degreeMutation_apply_of_notMem_range row B k g hj]

@[simp]
theorem degreeMutationWord_zero (w : List K) :
    degreeMutationWord row B (0 : I → G) w = 0 := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih => simp [ih]

theorem degreeMutationWord_add (w : List K) :
    degreeMutationWord row B (g₁ + g₂) w =
      degreeMutationWord row B g₁ w + degreeMutationWord row B g₂ w := by
  induction w generalizing B g₁ g₂ with
  | nil => rfl
  | cons k w ih => rw [degreeMutationWord_cons, degreeMutation_add, ih]; rfl

@[simp]
theorem degreeMutationWord_neg (w : List K) :
    degreeMutationWord row B (-g) w = -degreeMutationWord row B g w := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih => rw [degreeMutationWord_cons, degreeMutation_neg, ih]; rfl

theorem degreeMutationWord_sub (w : List K) :
    degreeMutationWord row B (g₁ - g₂) w =
      degreeMutationWord row B g₁ w - degreeMutationWord row B g₂ w := by
  simp [sub_eq_add_neg, degreeMutationWord_add]

/-- Additive group homomorphisms commute with `degreeMutationWord`. -/
theorem comp_degreeMutationWord (φ : G →+ H) (w : List K) :
    φ ∘ degreeMutationWord row B g w = degreeMutationWord row B (φ ∘ g) w := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih =>
    rw [degreeMutationWord_cons, degreeMutationWord_cons, ← comp_degreeMutation, ih]

/-- Bijective row relabelling and compatible mutable-column mapping commute with
`degreeMutationWord`. -/
theorem degreeMutationWord_submatrix [DecidableEq I'] [DecidableEq K'] [Fintype I']
    {row' : K' ↪ I'} {f : I' → I} {hK : K' → K} (hf : Function.Bijective f)
    (h : ∀ a, f (row' a) = row (hK a)) (w : List K') :
    degreeMutationWord row' (B.submatrix f hK) (g ∘ f) w =
      degreeMutationWord row B g (w.map hK) ∘ f := by
  induction w generalizing B g with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons, degreeMutationWord_cons]
    rw [matrixMutation_submatrix hf.injective h B k,
      degreeMutation_submatrix row B g hf h k, ih]

/-- Divided-column annihilation persists along any word whose prefix matrices have zero diagonal
at each step's mutation direction. -/
theorem sum_ediv_matrixMutationWord_smul_degreeMutationWord_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B i j) (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, (B i j / r j) • g i = 0) (j : K) :
    ∑ i, (matrixMutationWord row B w i j / r j) • degreeMutationWord row B g w i = 0 := by
  induction w generalizing B g with
  | nil => simpa using hg j
  | cons k w ih =>
    have hkk : B (row k) k = 0 := by simpa using hdiag [] k w rfl
    have hdvd' : ∀ i l, r l ∣ matrixMutation row B k i l :=
      fun i l ↦ dvd_matrixMutation (hdvd · l) k i
    have hg' : ∀ l, ∑ i, (matrixMutation row B k i l / r l) • degreeMutation row B k g i = 0 :=
      sum_ediv_matrixMutation_smul_degreeMutation_eq_zero row B k g hr hdvd hkk hg
    simp only [matrixMutationWord_cons, degreeMutationWord_cons]
    exact ih (matrixMutation row B k) (degreeMutation row B k g) hdvd'
      (fun u l v hw ↦ by
        simpa only [List.cons_append, matrixMutationWord_cons] using
          hdiag (k :: u) l v (by simp [hw])) hg'

/-- Ordinary column annihilation persists along any word whose prefix matrices have zero diagonal
at each step's mutation direction. -/
theorem sum_matrixMutationWord_smul_degreeMutationWord_eq_zero (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) (j : K) :
    ∑ i, matrixMutationWord row B w i j • degreeMutationWord row B g w i = 0 := by
  simpa using sum_ediv_matrixMutationWord_smul_degreeMutationWord_eq_zero row B g
    (r := 1) (fun _ ↦ Int.zero_lt_one) (fun _ _ ↦ one_dvd _) w hdiag (by simpa using hg) j

/-- Reversing a mutation word undoes its action on any column-annihilating grading when each
step's mutable diagonal entry vanishes. -/
theorem degreeMutationWord_reverse (w : List K)
    (hdiag : ∀ u k v, w = u ++ k :: v → matrixMutationWord row B u (row k) k = 0)
    (hg : ∀ j, ∑ i, B i j • g i = 0) :
    degreeMutationWord row (matrixMutationWord row B w) (degreeMutationWord row B g w)
      w.reverse = g := by
  induction w generalizing B g with
  | nil => simp
  | cons k w ih =>
    have hkk : B (row k) k = 0 := by simpa using hdiag [] k w rfl
    have hg' : ∀ j, ∑ i, matrixMutation row B k i j • degreeMutation row B k g i = 0 :=
      sum_matrixMutation_smul_degreeMutation_eq_zero row B k g hkk hg
    have hdiag' : ∀ u l v, w = u ++ l :: v →
        matrixMutationWord row (matrixMutation row B k) u (row l) l = 0 :=
      fun u l v hw ↦ by
        simpa only [matrixMutationWord_cons] using hdiag (k :: u) l v (by simp [hw])
    rw [List.reverse_cons, degreeMutationWord_append]
    simp only [matrixMutationWord_cons, degreeMutationWord_cons]
    rw [ih _ _ hdiag' hg', matrixMutationWord_matrixMutationWord_reverse,
      degreeMutationWord_nil, degreeMutation_degreeMutation row B k g hkk (hg k)]

end Word

namespace ExchangeMatrix

variable {I K G : Type*} [DecidableEq I] [DecidableEq K] [Fintype I]
  [AddCommGroup G] {row : K ↪ I} (B : ExchangeMatrix row)

/-- Every mutation word on a bundled exchange matrix preserves divided-column annihilation of
positive exchange degrees. -/
theorem sum_ediv_mutationWord_smul_degreeMutationWord_eq_zero {r : K → ℤ}
    (hr : ∀ j, 0 < r j) (hdvd : ∀ i j, r j ∣ B.matrix i j) {g : I → G}
    (hg : ∀ j, ∑ i, (B.matrix i j / r j) • g i = 0) (w : List K) (j : K) :
    ∑ i, ((B.mutationWord w).matrix i j / r j) • degreeMutationWord row B.matrix g w i = 0 := by
  rw [B.mutationWord_matrix]
  exact sum_ediv_matrixMutationWord_smul_degreeMutationWord_eq_zero row B.matrix g hr hdvd w
    (fun u k _ _ ↦ by
      rw [← B.mutationWord_matrix]
      exact (B.mutationWord u).matrix_row_self k) hg j

/-- Every mutation word on a bundled exchange matrix preserves ordinary column annihilation. -/
theorem sum_mutationWord_smul_degreeMutationWord_eq_zero {g : I → G}
    (hg : ∀ j, ∑ i, B.matrix i j • g i = 0) (w : List K) (j : K) :
    ∑ i, (B.mutationWord w).matrix i j • degreeMutationWord row B.matrix g w i = 0 := by
  rw [B.mutationWord_matrix]
  exact sum_matrixMutationWord_smul_degreeMutationWord_eq_zero row B.matrix g w
    (fun u k _ _ ↦ by
      rw [← B.mutationWord_matrix]
      exact (B.mutationWord u).matrix_row_self k) hg j

/-- Reversing a word on a bundled exchange matrix inverts its action on any column-annihilating
grading. -/
theorem degreeMutationWord_mutationWord_reverse {g : I → G}
    (hg : ∀ j, ∑ i, B.matrix i j • g i = 0) (w : List K) :
    degreeMutationWord row (B.mutationWord w).matrix
        (degreeMutationWord row B.matrix g w) w.reverse = g := by
  rw [B.mutationWord_matrix]
  exact degreeMutationWord_reverse row B.matrix g w
    (fun u k _ _ ↦ by
      rw [← B.mutationWord_matrix]
      exact (B.mutationWord u).matrix_row_self k) hg

end ExchangeMatrix

/-- For unequal column degrees `(3, 2)` on an extended `3 × 2` matrix, divided-column annihilation
holds initially for `g = ![0, 1, 1]` and persists after mutating in direction `0`, where `g`
updates to `![3, 1, 1]`. -/
example : degreeMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0
    (![0, 1, 1] : Fin 3 → ℤ) = ![3, 1, 1] := by
  decide

example : ∀ j : Fin 2, ∑ i : Fin 3,
    (matrixMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0 i j /
      (![3, 2] : Fin 2 → ℤ) j) •
      degreeMutation (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0
        (![0, 1, 1] : Fin 3 → ℤ) i = 0 := by
  apply sum_ediv_matrixMutation_smul_degreeMutation_eq_zero
    (Fin.castSuccEmb (n := 2)) !![0, 2; -3, 0; 3, 0] 0 ![0, 1, 1]
    (by decide) (fun a b ↦ by fin_cases a <;> fin_cases b <;> decide)
    (by decide) (by decide)

end TauCeti
