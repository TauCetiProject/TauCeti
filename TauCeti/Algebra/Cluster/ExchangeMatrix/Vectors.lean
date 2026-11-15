/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility
public import TauCeti.Algebra.Cluster.ExchangeMatrix.DegreeMutation

import Mathlib.Tactic.LinearCombination

/-!
# Principal `c`- and `g`-matrices and tropical duality

Starting from a square integer matrix `B₀ : Matrix K K ℤ`, mutating the principal extension
`fromRows B₀ 1` along a finite word `w : List K` produces a mutable top block
`matrixMutationWord (Function.Embedding.refl K) B₀ w` and a frozen bottom block `cMatrix B₀ w`,
whose columns `cVector B₀ w j` are the `c`-vectors along `w`.

For finite `K`, the principal `g`-matrix `gMatrix B₀ w` starts at the identity matrix and updates
column `k` at step `w ↦ w ++ [k]` by
`g'_k = -g_k + G_w [b_{•, k; w}]₊ - B₀ [c_{•, k; w}]₊`, leaving all other columns fixed. When the
mutable diagonal entry vanishes at every step along `w`, the columns of `gMatrix B₀ w` coincide
with the mutable part of `degreeMutationWord` started from `Sum.elim 1.col (-B₀.col)` on
`fromRows B₀ 1`, yielding the fundamental relation
`gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w = B₀ * cMatrix B₀ w`.

When column `k` of `cMatrix B₀ w` has coherent sign `ε ∈ {1, -1}` (`∀ i, 0 ≤ ε * cMatrix B₀ w i k`),
the step recurrences factor through the mutable mutation matrices as
`cMatrix B₀ (w ++ [k]) = cMatrix B₀ w * Fε` and `gMatrix B₀ (w ++ [k]) = gMatrix B₀ w * Eε`.
Along any column-sign-coherent word from a matrix with skew-symmetrizer `s`, induction gives
`(gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s`, determinant `(-1) ^ w.length` for
both matrices, invertibility over `ℤ`, and nonvanishing of every row and column.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §§2, 6, Proposition 6.6 and (6.14).
* T. Nakanishi and A. Zelevinsky, *On tropical dualities in cluster algebras*, Contemp. Math. 565
  (2012), Theorem 1.2, Proposition 1.3 and (2.7).
-/

public section

namespace TauCeti

open Matrix

section CMatrix

variable {K K' K₁ K₂ : Type*} [DecidableEq K]

/-- The principal `c`-matrix after mutating `fromRows B₀ 1` along `w` in reading order: the
frozen bottom block on `Sum.inr` rows. -/
def cMatrix (B₀ : Matrix K K ℤ) (w : List K) : Matrix K K ℤ :=
  (matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w).submatrix Sum.inr id

/-- The `j`-th `c`-vector along `w`: column `j` of `cMatrix B₀ w`. -/
def cVector (B₀ : Matrix K K ℤ) (w : List K) (j : K) : K → ℤ :=
  (cMatrix B₀ w).col j

variable (B₀ : Matrix K K ℤ) (w : List K)

/-- Definitional presentation of `cMatrix` as the frozen submatrix of the mutated principal
extension. -/
theorem cMatrix_def :
    cMatrix B₀ w =
      (matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w).submatrix Sum.inr id :=
  (rfl)

/-- Definitional presentation of `cVector` as a column of `cMatrix`. -/
theorem cVector_def (j : K) : cVector B₀ w j = (cMatrix B₀ w).col j :=
  (rfl)

/-- Entrywise formula for `cMatrix` via the `Sum.inr` rows of the mutated principal extension. -/
theorem cMatrix_apply (i j : K) :
    cMatrix B₀ w i j =
      matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w (Sum.inr i) j :=
  (rfl)

@[simp]
theorem cVector_apply (j i : K) : cVector B₀ w j i = cMatrix B₀ w i j :=
  (rfl)

/-- Mutating `fromRows B₀ 1` along `w` produces
`matrixMutationWord (Function.Embedding.refl K) B₀ w` in the mutable rows and `cMatrix B₀ w` in
the frozen rows. -/
@[simp]
theorem matrixMutationWord_fromRows_one :
    matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w =
      fromRows (matrixMutationWord (Function.Embedding.refl K) B₀ w) (cMatrix B₀ w) := by
  have hsub : (fromRows B₀ (1 : Matrix K K ℤ)).submatrix Function.Embedding.inl id = B₀ := by
    ext i j
    rfl
  have htop := matrixMutationWord_refl_submatrix_row Function.Embedding.inl
    (fromRows B₀ (1 : Matrix K K ℤ)) w
  rw [hsub] at htop
  ext (i | i) j
  · exact congrArg (fun M ↦ M i j) htop.symm
  · rfl

@[simp]
theorem cMatrix_nil : cMatrix B₀ [] = 1 := by
  ext i j
  simp only [cMatrix_apply, matrixMutationWord_nil, fromRows_apply_inr]

@[simp]
theorem cVector_nil (j : K) : cVector B₀ [] j = (1 : Matrix K K ℤ).col j := by
  ext i
  simp

/-- Single-step recurrence for `cMatrix` on appending a direction `k`. -/
theorem cMatrix_append_singleton_apply (k i j : K) :
    cMatrix B₀ (w ++ [k]) i j =
      if j = k then -cMatrix B₀ w i k
      else cMatrix B₀ w i j +
        (cMatrix B₀ w i k)⁺ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁺ -
        (cMatrix B₀ w i k)⁻ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁻ := by
  rw [cMatrix_apply, matrixMutationWord_append, matrixMutationWord_fromRows_one,
    matrixMutationWord_cons, matrixMutationWord_nil, matrixMutation_apply]
  by_cases hj : j = k <;> simp [hj]

@[simp]
theorem cMatrix_append_singleton_col (k i : K) :
    cMatrix B₀ (w ++ [k]) i k = -cMatrix B₀ w i k := by
  rw [cMatrix_append_singleton_apply]
  simp

@[simp]
theorem cVector_append_singleton_self (k : K) :
    cVector B₀ (w ++ [k]) k = -cVector B₀ w k := by
  ext i
  simp

theorem cMatrix_append_singleton_of_ne (k i : K) {j : K} (hj : j ≠ k) :
    cMatrix B₀ (w ++ [k]) i j =
      cMatrix B₀ w i j +
        (cMatrix B₀ w i k)⁺ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁺ -
        (cMatrix B₀ w i k)⁻ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁻ := by
  simp [cMatrix_append_singleton_apply, hj]

/-- Single-step principal `c`-matrix at `[k]` equals the positive-sign right mutation factor
`F₁(B₀, k)`. -/
@[simp]
theorem cMatrix_singleton (k : K) :
    cMatrix B₀ [k] = matrixMutationRight (Function.Embedding.refl K) B₀ k 1 := by
  ext i j
  have h := cMatrix_append_singleton_apply B₀ [] k i j
  simp only [List.nil_append, cMatrix_nil, matrixMutationWord_nil] at h
  rw [h, matrixMutationRight_apply]
  by_cases hj : j = k
  · subst j
    by_cases hi : i = k <;> simp [hi, Matrix.one_apply]
  · by_cases hi : i = k
    · subst i
      simp [hj, Ne.symm hj]
    · simp [hi, hj, Matrix.one_apply]

/-- Equal adjacent directions cancel in `cMatrix`. -/
theorem cMatrix_append_cons_cons_self (u v : List K) (k : K) :
    cMatrix B₀ (u ++ k :: k :: v) = cMatrix B₀ (u ++ v) := by
  simp only [cMatrix_def, matrixMutationWord_append_cons_cons_self]

/-- Simultaneous relabelling of indices transports `cMatrix` along mapped words. -/
theorem cMatrix_reindex [DecidableEq K'] (e : K ≃ K') :
    cMatrix (B₀.reindex e e) (w.map e) = (cMatrix B₀ w).reindex e e := by
  have hsub : fromRows (B₀.reindex e e) (1 : Matrix K' K' ℤ) =
      (fromRows B₀ (1 : Matrix K K ℤ)).submatrix (e.symm.sumCongr e.symm) e.symm := by
    ext (i | i) j <;> simp [Matrix.one_apply]
  have hword := matrixMutationWord_submatrix
    (row := (Function.Embedding.inl : K ↪ K ⊕ K))
    (row' := (Function.Embedding.inl : K' ↪ K' ⊕ K'))
    (f := e.symm.sumCongr e.symm) (g := e.symm)
    (e.symm.sumCongr e.symm).injective (fun _ ↦ rfl) (fromRows B₀ (1 : Matrix K K ℤ)) (w.map e)
  have hmap : (w.map e).map e.symm = w := by simp [List.map_map]
  rw [← hsub, hmap] at hword
  ext i j
  simpa using congrArg (fun M ↦ M (Sum.inr i) j) hword

/-- On a block-diagonal initial matrix, `cMatrix` splits into the `c`-matrices of the blocks
along their projected subwords. -/
theorem cMatrix_fromBlocks [DecidableEq K₁] [DecidableEq K₂]
    (B₁ : Matrix K₁ K₁ ℤ) (B₂ : Matrix K₂ K₂ ℤ) (w : List (K₁ ⊕ K₂)) :
    cMatrix (fromBlocks B₁ 0 0 B₂) w =
      fromBlocks (cMatrix B₁ (w.filterMap Sum.getLeft?)) 0 0
        (cMatrix B₂ (w.filterMap Sum.getRight?)) := by
  let f : (K₁ ⊕ K₁) ⊕ (K₂ ⊕ K₂) ≃ (K₁ ⊕ K₂) ⊕ (K₁ ⊕ K₂) := Equiv.sumSumSumComm K₁ K₁ K₂ K₂
  have hf₁ (i : K₁) : f.symm (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr i) := rfl
  have hf₂ (i : K₂) : f.symm (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr i) := rfl
  have hinit :
      fromRows (fromBlocks B₁ 0 0 B₂) (1 : Matrix (K₁ ⊕ K₂) (K₁ ⊕ K₂) ℤ) =
        (fromBlocks (fromRows B₁ (1 : Matrix K₁ K₁ ℤ)) 0 0
          (fromRows B₂ (1 : Matrix K₂ K₂ ℤ))).submatrix f.symm id := by
    ext ((i | i) | (i | i)) (j | j) <;> simp [f, Matrix.one_apply]
  have hword := matrixMutationWord_submatrix
    (row := (Function.Embedding.inl : K₁ ↪ K₁ ⊕ K₁).sumMap
      (Function.Embedding.inl : K₂ ↪ K₂ ⊕ K₂))
    (row' := (Function.Embedding.inl : K₁ ⊕ K₂ ↪ (K₁ ⊕ K₂) ⊕ (K₁ ⊕ K₂)))
    (f := f.symm) (g := id) f.symm.injective
    (by rintro (k | k) <;> rfl)
    (fromBlocks (fromRows B₁ (1 : Matrix K₁ K₁ ℤ)) 0 0 (fromRows B₂ (1 : Matrix K₂ K₂ ℤ))) w
  simp only [List.map_id, ← hinit, matrixMutationWord_fromBlocks] at hword
  ext (i | i) (j | j)
  · simpa [hf₁] using congrArg (fun M ↦ M (Sum.inr (Sum.inl i)) (Sum.inl j)) hword
  · simpa [hf₁] using congrArg (fun M ↦ M (Sum.inr (Sum.inl i)) (Sum.inr j)) hword
  · simpa [hf₂] using congrArg (fun M ↦ M (Sum.inr (Sum.inr i)) (Sum.inl j)) hword
  · simpa [hf₂] using congrArg (fun M ↦ M (Sum.inr (Sum.inr i)) (Sum.inr j)) hword

end CMatrix

namespace ExchangeMatrix

variable {K : Type*} [DecidableEq K] (B : ExchangeMatrix (Function.Embedding.refl K))

/-- Mutating the bundled principal extension along `w` gives `(B.mutationWord w).matrix` in the
mutable block and `cMatrix B.matrix w` in the frozen block. -/
theorem principalExtension_mutationWord_matrix (w : List K) :
    (B.principalExtension.mutationWord w).matrix =
      fromRows (B.mutationWord w).matrix (cMatrix B.matrix w) := by
  rw [B.principalExtension.mutationWord_matrix, B.principalExtension_matrix,
    matrixMutationWord_fromRows_one, B.mutationWord_matrix]

end ExchangeMatrix

section GMatrix

variable {K K' : Type*} [DecidableEq K] [Fintype K]

private def gMatrixFold (B₀ : Matrix K K ℤ) :
    Matrix (K ⊕ K) K ℤ × Matrix K K ℤ → K → Matrix (K ⊕ K) K ℤ × Matrix K K ℤ
  | (Bext, G), k =>
    (matrixMutation Function.Embedding.inl Bext k,
      G.updateCol k fun i ↦
        -G i k + ∑ l, G i l * (Bext (Sum.inl l) k)⁺ - ∑ l, B₀ i l * (Bext (Sum.inr l) k)⁺)

private theorem gMatrixFold_fst (B₀ : Matrix K K ℤ) (w : List K) :
    (w.foldl (gMatrixFold B₀) (fromRows B₀ 1, 1)).1 =
      matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w := by
  simpa only [matrixMutationWord_eq_foldl] using
    (List.foldl_hom Prod.fst (l := w)
      (init := (fromRows B₀ (1 : Matrix K K ℤ), (1 : Matrix K K ℤ))) (fun _ _ ↦ rfl)).symm

/-- The principal `g`-matrix along a finite mutation word `w` in reading order: `G₀ = 1`, and
appending `k` replaces column `k` by `-g_k + G_w [b_{•, k; w}]₊ - B₀ [c_{•, k; w}]₊` while
keeping all other columns unchanged. -/
def gMatrix (B₀ : Matrix K K ℤ) (w : List K) : Matrix K K ℤ :=
  (w.foldl (gMatrixFold B₀) (fromRows B₀ 1, 1)).2

/-- The `j`-th `g`-vector along `w`: column `j` of `gMatrix B₀ w`. -/
def gVector (B₀ : Matrix K K ℤ) (w : List K) (j : K) : K → ℤ :=
  (gMatrix B₀ w).col j

variable (B₀ : Matrix K K ℤ) (w : List K)

/-- Definitional presentation of `gVector` as a column of `gMatrix`. -/
theorem gVector_def (j : K) : gVector B₀ w j = (gMatrix B₀ w).col j :=
  (rfl)

@[simp]
theorem gVector_apply (j i : K) : gVector B₀ w j i = gMatrix B₀ w i j :=
  (rfl)

@[simp]
theorem gMatrix_nil : gMatrix B₀ [] = 1 :=
  (rfl)

@[simp]
theorem gVector_nil (j : K) : gVector B₀ [] j = (1 : Matrix K K ℤ).col j :=
  (rfl)

/-- Single-step column update of `gMatrix` on appending a direction `k`. -/
theorem gMatrix_append_singleton (k : K) :
    gMatrix B₀ (w ++ [k]) =
      (gMatrix B₀ w).updateCol k fun i ↦
        -gMatrix B₀ w i k +
          ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ -
          ∑ l, B₀ i l * (cMatrix B₀ w l k)⁺ := by
  simp only [gMatrix, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h1 := gMatrixFold_fst B₀ w
  rw [matrixMutationWord_fromRows_one] at h1
  rcases h : w.foldl (gMatrixFold B₀) (fromRows B₀ 1, 1) with ⟨Bext, G⟩
  rw [h] at h1
  dsimp only at h1 ⊢
  rw [gMatrixFold, h1]
  simp only [fromRows_apply_inl, fromRows_apply_inr]

@[simp]
theorem gMatrix_append_singleton_col (k i : K) :
    gMatrix B₀ (w ++ [k]) i k =
      -gMatrix B₀ w i k +
        ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ -
        ∑ l, B₀ i l * (cMatrix B₀ w l k)⁺ := by
  rw [gMatrix_append_singleton, updateCol_self]

@[simp]
theorem gMatrix_append_singleton_of_ne (k i : K) {j : K} (hj : j ≠ k) :
    gMatrix B₀ (w ++ [k]) i j = gMatrix B₀ w i j := by
  rw [gMatrix_append_singleton, updateCol_ne hj]

@[simp]
theorem gVector_append_singleton_of_ne (k : K) {j : K} (hj : j ≠ k) :
    gVector B₀ (w ++ [k]) j = gVector B₀ w j := by
  ext i
  exact gMatrix_append_singleton_of_ne B₀ w k i hj

/-- Vector recurrence `g'_k = -g_k + G_w *ᵥ [b_{•, k; w}]₊ - B₀ *ᵥ [c_{•, k; w}]₊` for the
mutated `g`-vector. -/
theorem gVector_append_singleton_self (k : K) :
    gVector B₀ (w ++ [k]) k =
      -gVector B₀ w k +
        gMatrix B₀ w *ᵥ (fun l ↦ (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺) -
        B₀ *ᵥ (fun l ↦ (cVector B₀ w k l)⁺) := by
  ext i
  simp [mulVec, dotProduct]

/-- When `B₀ k k = 0`, the single-step principal `g`-matrix `gMatrix B₀ [k]` equals the
positive-sign left mutation factor `E₁(B₀, k)`. -/
theorem gMatrix_singleton {k : K} (hkk : B₀ k k = 0) :
    gMatrix B₀ [k] = matrixMutationLeft (Function.Embedding.refl K) B₀ k 1 := by
  have h1 (x : K) : ((if x = k then (1 : ℤ) else 0))⁺ = if x = k then 1 else 0 := by
    by_cases hx : x = k <;> simp [hx]
  have hcol (i : K) :
      gMatrix B₀ [k] i k = -(if i = k then (1 : ℤ) else 0) + (B₀ i k)⁺ - B₀ i k := by
    have hc := gMatrix_append_singleton_col B₀ [] k i
    simpa only [List.nil_append, gMatrix_nil, matrixMutationWord_nil, cMatrix_nil,
      Matrix.one_apply, h1, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hc
  ext i j
  by_cases hj : j = k
  · subst j
    rw [hcol, matrixMutationLeft_apply, Function.Embedding.refl_apply]
    simp only [↓reduceIte]
    by_cases hi : i = k
    · subst i
      simp [hkk]
    · simp only [hi, ↓reduceIte, neg_mul, one_mul, posPart_neg]
      linear_combination posPart_sub_negPart (B₀ i k)
  · have hne := gMatrix_append_singleton_of_ne B₀ [] k i hj
    simpa only [List.nil_append, gMatrix_nil,
      matrixMutationLeft_apply_of_ne (Function.Embedding.refl K) B₀ k 1 i hj] using hne

/-- The initial principal grading `Sum.elim 1.col (-B₀.col)` annihilates every mutable column of
the principal extension `fromRows B₀ 1`. -/
theorem sum_fromRows_one_smul_principalGrading (j : K) :
    ∑ a : K ⊕ K, fromRows B₀ (1 : Matrix K K ℤ) a j •
      Sum.elim (1 : Matrix K K ℤ).col (-B₀.col) a = 0 := by
  ext i
  simp [Fintype.sum_sum_type, Finset.sum_apply, Matrix.col_apply, Matrix.one_apply, mul_ite]

/-- When the mutable diagonal entry vanishes at each step of `w`, propagating the initial principal
grading `Sum.elim 1.col (-B₀.col)` on `fromRows B₀ 1` produces the columns of `gMatrix B₀ w` on
mutable indices and `-B₀.col` on frozen indices. -/
theorem degreeMutationWord_fromRows_one
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0) :
    degreeMutationWord Function.Embedding.inl (fromRows B₀ 1)
        (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) w =
      Sum.elim (gMatrix B₀ w).col (-B₀.col) := by
  have hdiagExt : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) u (Sum.inl k) k = 0 := by
    intro u k v hw
    rw [matrixMutationWord_fromRows_one]
    exact hdiag u k v hw
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    have hdu : ∀ a l b, u = a ++ l :: b →
        matrixMutationWord (Function.Embedding.refl K) B₀ a l l = 0 :=
      fun a l b hu ↦ hdiag a l (b ++ [k]) (by simp [hu])
    have hduExt : ∀ a l b, u = a ++ l :: b →
        matrixMutationWord Function.Embedding.inl
          (fromRows B₀ (1 : Matrix K K ℤ)) a (Sum.inl l) l = 0 :=
      fun a l b hu ↦ hdiagExt a l (b ++ [k]) (by simp [hu])
    have hu := ih hdu fun a l b hu ↦ hduExt a l b hu
    have hann : ∀ j : K,
        ∑ a : K ⊕ K,
          matrixMutationWord Function.Embedding.inl (fromRows B₀ (1 : Matrix K K ℤ)) u a j •
            Sum.elim (gMatrix B₀ u).col (-B₀.col) a = 0 := by
      intro j
      rw [← hu]
      exact sum_matrixMutationWord_smul_degreeMutationWord_eq_zero Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) u hduExt
        (sum_fromRows_one_smul_principalGrading B₀) j
    have hkk :
        matrixMutationWord Function.Embedding.inl
          (fromRows B₀ (1 : Matrix K K ℤ)) u (Sum.inl k) k = 0 :=
      hdiagExt u k [] (by simp)
    rw [degreeMutationWord_append, hu, degreeMutationWord_singleton]
    ext (j | j) i
    · by_cases hjk : j = k
      · subst j
        have hpos := congrFun
          (degreeMutation_apply_row_posPart_univ Function.Embedding.inl
            (matrixMutationWord Function.Embedding.inl (fromRows B₀ (1 : Matrix K K ℤ)) u) k
            (Sum.elim (gMatrix B₀ u).col (-B₀.col)) hkk (hann k)) i
        simp only [Function.Embedding.inl_apply, matrixMutationWord_fromRows_one,
          Fintype.sum_sum_type, fromRows_apply_inl, fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
          Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.col_apply, mul_neg, Finset.sum_neg_distrib] at hpos
        rw [matrixMutationWord_fromRows_one, hpos, Sum.elim_inl, Matrix.col_apply,
          gMatrix_append_singleton_col]
        simp_rw [mul_comm (gMatrix B₀ u i _), mul_comm (B₀ i _)]
        ring
      · simp [hjk]
    · simp

/-- Fundamental relation `G_w * B_w = B₀ * C_w` between the principal `g`-matrix, the mutated
mutable matrix, the initial matrix, and the principal `c`-matrix, assuming only that the mutable
diagonal entry vanishes at each step of `w`. -/
theorem gMatrix_mul_matrixMutationWord
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0) :
    gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w =
      B₀ * cMatrix B₀ w := by
  have hdiagExt : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) u (Sum.inl k) k = 0 := by
    intro u k v hw
    rw [matrixMutationWord_fromRows_one]
    exact hdiag u k v hw
  ext i j
  have hann := congrFun
    (sum_matrixMutationWord_smul_degreeMutationWord_eq_zero Function.Embedding.inl
      (fromRows B₀ (1 : Matrix K K ℤ)) (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) w hdiagExt
      (sum_fromRows_one_smul_principalGrading B₀) j) i
  rw [degreeMutationWord_fromRows_one B₀ w hdiag, matrixMutationWord_fromRows_one] at hann
  simp only [Fintype.sum_sum_type, fromRows_apply_inl, fromRows_apply_inr, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, Matrix.col_apply, mul_neg, Finset.sum_neg_distrib] at hann
  simp only [Matrix.mul_apply]
  simp_rw [mul_comm (gMatrix B₀ w i _), mul_comm (B₀ i _)]
  linear_combination hann

/-- Negative-part recurrence for column `k` of `gMatrix B₀ (w ++ [k])` when the mutable diagonal
entry vanishes at step `k` and `G_w * B_w = B₀ * C_w`. -/
theorem gMatrix_append_singleton_col_negPart (k i : K)
    (hkk : matrixMutationWord (Function.Embedding.refl K) B₀ w k k = 0)
    (hrel : gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w =
      B₀ * cMatrix B₀ w) :
    gMatrix B₀ (w ++ [k]) i k =
      -gMatrix B₀ w i k +
        ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁻ -
        ∑ l, B₀ i l * (cMatrix B₀ w l k)⁻ := by
  have hentry := congrArg (fun M ↦ M i k) hrel
  simp only [Matrix.mul_apply] at hentry
  have hB (l : K) :
      gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ =
        gMatrix B₀ w i l * matrixMutationWord (Function.Embedding.refl K) B₀ w l k +
          gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁻ := by
    linear_combination gMatrix B₀ w i l *
      posPart_sub_negPart (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)
  have hC (l : K) :
      B₀ i l * (cMatrix B₀ w l k)⁺ =
        B₀ i l * cMatrix B₀ w l k + B₀ i l * (cMatrix B₀ w l k)⁻ := by
    linear_combination B₀ i l * posPart_sub_negPart (cMatrix B₀ w l k)
  let _ := hkk
  rw [gMatrix_append_singleton_col]
  simp_rw [hB, hC, Finset.sum_add_distrib]
  linear_combination hentry

/-- Simultaneous relabelling of indices transports `gMatrix` along mapped words. -/
theorem gMatrix_reindex [DecidableEq K'] [Fintype K'] (e : K ≃ K') :
    gMatrix (B₀.reindex e e) (w.map e) = (gMatrix B₀ w).reindex e e := by
  induction w using List.reverseRecOn with
  | nil =>
    ext i j
    simp [Matrix.one_apply]
  | append_singleton u k ih =>
    rw [List.map_append, List.map_singleton]
    have hbw :
        matrixMutationWord (Function.Embedding.refl K') (B₀.reindex e e) (u.map e) =
          (matrixMutationWord (Function.Embedding.refl K) B₀ u).reindex e e := by
      have hsub := matrixMutationWord_submatrix
        (row := Function.Embedding.refl K) (row' := Function.Embedding.refl K')
        (f := e.symm) (g := e.symm) e.symm.injective (fun _ ↦ rfl) B₀ (u.map e)
      simpa [List.map_map] using hsub
    ext i j
    by_cases hjk : j = e k
    · subst j
      rw [gMatrix_append_singleton_col, ih, hbw, cMatrix_reindex B₀ u e]
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        gMatrix_append_singleton_col]
      have hs1 :
          ∑ l : K', gMatrix B₀ u (e.symm i) (e.symm l) *
              (matrixMutationWord (Function.Embedding.refl K) B₀ u (e.symm l) k)⁺ =
            ∑ l : K, gMatrix B₀ u (e.symm i) l *
              (matrixMutationWord (Function.Embedding.refl K) B₀ u l k)⁺ :=
        e.symm.sum_comp fun l ↦
          gMatrix B₀ u (e.symm i) l *
            (matrixMutationWord (Function.Embedding.refl K) B₀ u l k)⁺
      have hs2 :
          ∑ l : K', B₀ (e.symm i) (e.symm l) * (cMatrix B₀ u (e.symm l) k)⁺ =
            ∑ l : K, B₀ (e.symm i) l * (cMatrix B₀ u l k)⁺ :=
        e.symm.sum_comp fun l ↦ B₀ (e.symm i) l * (cMatrix B₀ u l k)⁺
      rw [hs1, hs2]
    · have hne : e.symm j ≠ k := fun h ↦ hjk (by rw [← h, Equiv.apply_symm_apply])
      rw [gMatrix_append_singleton_of_ne _ _ _ _ hjk, ih]
      simp [gMatrix_append_singleton_of_ne _ _ _ _ hne]

/-! ### Signed recurrences and tropical duality -/

/-- When `B_w k k = 0` and column `k` of `cMatrix B₀ w` has coherent sign `ε ∈ {1, -1}`
(`∀ i, 0 ≤ ε * cMatrix B₀ w i k`), `cMatrix` right-multiplies by `Fε(B_w, k)` at step `k`. -/
theorem cMatrix_append_singleton_eq_mul_matrixMutationRight {k : K} {ε : ℤ}
    (hkk : matrixMutationWord (Function.Embedding.refl K) B₀ w k k = 0)
    (hε : ε = 1 ∨ ε = -1) (hsign : ∀ i, 0 ≤ ε * cMatrix B₀ w i k) :
    cMatrix B₀ (w ++ [k]) =
      cMatrix B₀ w *
        matrixMutationRight (Function.Embedding.refl K)
          (matrixMutationWord (Function.Embedding.refl K) B₀ w) k ε := by
  set Bw := matrixMutationWord (Function.Embedding.refl K) B₀ w
  have hfac := matrixMutation_eq_mul Function.Embedding.inl (fromRows Bw (cMatrix B₀ w)) k ε
    (by simpa using hkk) hε
  have hF :
      matrixMutationRight Function.Embedding.inl (fromRows Bw (cMatrix B₀ w)) k ε =
        matrixMutationRight (Function.Embedding.refl K) Bw k ε := by
    ext i j
    simp [matrixMutationRight_apply]
  rw [hF] at hfac
  have hleft :
      (matrixMutationLeft Function.Embedding.inl (fromRows Bw (cMatrix B₀ w)) k ε *
          fromRows Bw (cMatrix B₀ w)).submatrix Sum.inr id =
        cMatrix B₀ w := by
    ext i l
    simp only [submatrix_apply, id_eq, matrixMutationLeft_mul_apply, Function.Embedding.inl_apply,
      reduceCtorEq, ↓reduceIte, fromRows_apply_inr, fromRows_apply_inl]
    have hnp : (-ε * cMatrix B₀ w i k)⁺ = 0 := by
      rw [posPart_eq_zero]
      linarith [hsign i]
    rw [hnp, zero_mul, add_zero]
  ext i j
  have hrow :
      (cMatrix B₀ (w ++ [k])) i j =
        (matrixMutation Function.Embedding.inl (fromRows Bw (cMatrix B₀ w)) k) (Sum.inr i) j := by
    rw [cMatrix_apply, matrixMutationWord_append, matrixMutationWord_fromRows_one,
      matrixMutationWord_cons, matrixMutationWord_nil]
  rw [hrow, hfac, mul_matrixMutationRight_apply, mul_matrixMutationRight_apply]
  have hli := congrArg (fun M ↦ M i) hleft
  have hlj := congrArg (fun M ↦ M i j) hleft
  have hlk := congrArg (fun M ↦ M i k) hleft
  simp only [submatrix_apply, id_eq] at hlj hlk
  let _ := hli
  rw [hlj, hlk]

/-- When `B_w k k = 0`, `G_w * B_w = B₀ * C_w`, and column `k` of `cMatrix B₀ w` has coherent
sign `ε ∈ {1, -1}` (`∀ i, 0 ≤ ε * cMatrix B₀ w i k`), `gMatrix` right-multiplies by `Eε(B_w, k)`
at step `k`. -/
theorem gMatrix_append_singleton_eq_mul_matrixMutationLeft {k : K} {ε : ℤ}
    (hkk : matrixMutationWord (Function.Embedding.refl K) B₀ w k k = 0)
    (hrel : gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w =
      B₀ * cMatrix B₀ w)
    (hε : ε = 1 ∨ ε = -1) (hsign : ∀ i, 0 ≤ ε * cMatrix B₀ w i k) :
    gMatrix B₀ (w ++ [k]) =
      gMatrix B₀ w *
        matrixMutationLeft (Function.Embedding.refl K)
          (matrixMutationWord (Function.Embedding.refl K) B₀ w) k ε := by
  set Bw := matrixMutationWord (Function.Embedding.refl K) B₀ w with hBw
  have hmul (i : K) :
      (gMatrix B₀ w * matrixMutationLeft (Function.Embedding.refl K) Bw k ε) i k =
        -gMatrix B₀ w i k + ∑ l, gMatrix B₀ w i l * (-ε * Bw l k)⁺ := by
    rw [Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    simp only [matrixMutationLeft_apply, Function.Embedding.refl_apply, ↓reduceIte, mul_neg,
      mul_one]
    rw [← Finset.add_sum_erase Finset.univ
      (fun l ↦ gMatrix B₀ w i l * (-ε * Bw l k)⁺) (Finset.mem_univ k)]
    simp only [hkk, mul_zero, posPart_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    simp [(Finset.mem_erase.mp hl).1]
  have hcol_ne (i : K) {j : K} (hj : j ≠ k) :
      (gMatrix B₀ w * matrixMutationLeft (Function.Embedding.refl K) Bw k ε) i j =
        gMatrix B₀ w i j := by
    rw [Matrix.mul_apply]
    simp [matrixMutationLeft_apply_of_ne (Function.Embedding.refl K) Bw k ε _ hj, Matrix.one_apply]
  ext i j
  by_cases hj : j = k
  · subst j
    rw [hmul]
    rcases hε with rfl | rfl
    · rw [gMatrix_append_singleton_col_negPart B₀ w k i hkk hrel, ← hBw]
      have hcn (l : K) : (cMatrix B₀ w l k)⁻ = 0 := by
        rw [negPart_eq_zero]
        simpa using hsign l
      simp only [hcn, mul_zero, Finset.sum_const_zero, sub_zero, neg_mul, one_mul, posPart_neg]
    · rw [gMatrix_append_singleton_col, ← hBw]
      have hcp (l : K) : (cMatrix B₀ w l k)⁺ = 0 := by
        rw [posPart_eq_zero]
        linarith [hsign l]
      simp only [hcp, mul_zero, Finset.sum_const_zero, sub_zero, neg_neg, one_mul]
  · rw [gMatrix_append_singleton_of_ne B₀ w k i hj, hcol_ne i hj]

/-- Along any word whose prefixes have zero mutable diagonal at each step and column-sign-coherent
`c`-vectors at each step, `cMatrix B₀ w` has determinant `(-1) ^ w.length`. -/
theorem det_cMatrix_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (cMatrix B₀ w).det = (-1) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    have hdu : ∀ a l b, u = a ++ l :: b →
        matrixMutationWord (Function.Embedding.refl K) B₀ a l l = 0 :=
      fun a l b hu ↦ hdiag a l (b ++ [k]) (by simp [hu])
    have hcu : ∀ a l b, u = a ++ l :: b →
        (∀ i, 0 ≤ cMatrix B₀ a i l) ∨ ∀ i, cMatrix B₀ a i l ≤ 0 :=
      fun a l b hu ↦ hc a l (b ++ [k]) (by simp [hu])
    have hkk : matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0 :=
      hdiag u k [] (by simp)
    obtain ⟨ε, hε, hsign⟩ :
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε * cMatrix B₀ u i k := by
      rcases hc u k [] (by simp) with hpos | hneg
      · exact ⟨1, Or.inl rfl, fun i ↦ by simpa using hpos i⟩
      · exact ⟨-1, Or.inr rfl, fun i ↦ by linarith [hneg i]⟩
    rw [cMatrix_append_singleton_eq_mul_matrixMutationRight B₀ u hkk hε hsign,
      det_mul, ih hdu hcu, det_matrixMutationRight, List.length_append, List.length_singleton,
      pow_add, pow_one]

/-- Along any word whose prefixes have zero mutable diagonal at each step and column-sign-coherent
`c`-vectors at each step, `gMatrix B₀ w` has determinant `(-1) ^ w.length`. -/
theorem det_gMatrix_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w).det = (-1) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    have hdu : ∀ a l b, u = a ++ l :: b →
        matrixMutationWord (Function.Embedding.refl K) B₀ a l l = 0 :=
      fun a l b hu ↦ hdiag a l (b ++ [k]) (by simp [hu])
    have hcu : ∀ a l b, u = a ++ l :: b →
        (∀ i, 0 ≤ cMatrix B₀ a i l) ∨ ∀ i, cMatrix B₀ a i l ≤ 0 :=
      fun a l b hu ↦ hc a l (b ++ [k]) (by simp [hu])
    have hkk : matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0 :=
      hdiag u k [] (by simp)
    have hrel := gMatrix_mul_matrixMutationWord B₀ u hdu
    obtain ⟨ε, hε, hsign⟩ :
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε * cMatrix B₀ u i k := by
      rcases hc u k [] (by simp) with hpos | hneg
      · exact ⟨1, Or.inl rfl, fun i ↦ by simpa using hpos i⟩
      · exact ⟨-1, Or.inr rfl, fun i ↦ by linarith [hneg i]⟩
    rw [gMatrix_append_singleton_eq_mul_matrixMutationLeft B₀ u hkk hrel hε hsign,
      det_mul, ih hdu hcu, det_matrixMutationLeft, List.length_append, List.length_singleton,
      pow_add, pow_one]

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, `cMatrix B₀ w`
is unimodular over `ℤ`. -/
theorem isUnit_cMatrix_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (cMatrix B₀ w) := by
  rw [isUnit_iff_isUnit_det, det_cMatrix_of_signCoherent B₀ w hdiag hc]
  exact IsUnit.pow _ isUnit_neg_one

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, `gMatrix B₀ w`
is unimodular over `ℤ`. -/
theorem isUnit_gMatrix_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (gMatrix B₀ w) := by
  rw [isUnit_iff_isUnit_det, det_gMatrix_of_signCoherent B₀ w hdiag hc]
  exact IsUnit.pow _ isUnit_neg_one

omit [Fintype K] in
/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, no `c`-vector
vanishes. -/
theorem cVector_ne_zero_of_signCoherent [Finite K]
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (j : K) :
    cVector B₀ w j ≠ 0 := by
  let := Fintype.ofFinite K
  intro hz
  have hdet : (cMatrix B₀ w).det = 0 :=
    det_eq_zero_of_column_eq_zero j fun i ↦ congrFun hz i
  rw [det_cMatrix_of_signCoherent B₀ w hdiag hc] at hdet
  exact pow_ne_zero w.length (by decide : (-1 : ℤ) ≠ 0) hdet

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, no `g`-vector
vanishes. -/
theorem gVector_ne_zero_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (j : K) :
    gVector B₀ w j ≠ 0 := by
  intro hz
  have hdet : (gMatrix B₀ w).det = 0 :=
    det_eq_zero_of_column_eq_zero j fun i ↦ congrFun hz i
  rw [det_gMatrix_of_signCoherent B₀ w hdiag hc] at hdet
  exact pow_ne_zero w.length (by decide : (-1 : ℤ) ≠ 0) hdet

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, no row of
`gMatrix B₀ w` vanishes. -/
theorem gMatrix_row_ne_zero_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (i : K) :
    gMatrix B₀ w i ≠ 0 := by
  intro hz
  have hdet : (gMatrix B₀ w).det = 0 :=
    det_eq_zero_of_row_eq_zero i fun j ↦ congrFun hz j
  rw [det_gMatrix_of_signCoherent B₀ w hdiag hc] at hdet
  exact pow_ne_zero w.length (by decide : (-1 : ℤ) ≠ 0) hdet

omit [Fintype K] in
/-- Principal exchange-monomial dichotomy: along a column-sign-coherent word with vanishing mutable
diagonal at each step, if `cVector B₀ w j` is itself sign-coherent, then one of its positive-part
and negative-part frozen-exponent vectors vanishes and the other is nonzero. -/
theorem cVector_posPart_eq_zero_or_negPart_eq_zero_of_signCoherent [Finite K]
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) {j : K}
    (hj : (∀ i, 0 ≤ cVector B₀ w j i) ∨ ∀ i, cVector B₀ w j i ≤ 0) :
    ((fun i ↦ (cVector B₀ w j i)⁺) = 0 ∧ (fun i ↦ (cVector B₀ w j i)⁻) ≠ 0) ∨
      ((fun i ↦ (cVector B₀ w j i)⁻) = 0 ∧ (fun i ↦ (cVector B₀ w j i)⁺) ≠ 0) := by
  have hne := cVector_ne_zero_of_signCoherent B₀ w hdiag hc j
  rcases hj with hpos | hneg
  · refine Or.inr ⟨funext fun i ↦ ?_, fun hp ↦ hne (funext fun i ↦ ?_)⟩
    · rw [Pi.zero_apply, ← posPart_neg, posPart_eq_zero]
      linarith [hpos i]
    · have hi : (cVector B₀ w j i)⁺ = 0 := congrFun hp i
      rw [posPart_eq_zero] at hi
      rw [Pi.zero_apply]
      linarith [hpos i]
  · refine Or.inl ⟨funext fun i ↦ ?_, fun hn ↦ hne (funext fun i ↦ ?_)⟩
    · rw [Pi.zero_apply, posPart_eq_zero]
      exact hneg i
    · have hi : (cVector B₀ w j i)⁻ = 0 := congrFun hn i
      rw [← posPart_neg, posPart_eq_zero] at hi
      rw [Pi.zero_apply]
      linarith [hneg i]

end GMatrix

end TauCeti

namespace Matrix.IsSkewSymmetrizer

open TauCeti

variable {K : Type*} [DecidableEq K] [Fintype K] {B₀ : Matrix K K ℤ} {s : K → ℤ}

/-- For a skew-symmetrizable initial matrix `B₀`, `gMatrix B₀ w * B_w = B₀ * cMatrix B₀ w` holds
for every mutation word `w`, without assuming sign-coherence. -/
theorem gMatrix_mul_matrixMutationWord (hs : B₀.IsSkewSymmetrizer s) (w : List K) :
    gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w =
      B₀ * cMatrix B₀ w :=
  TauCeti.gMatrix_mul_matrixMutationWord B₀ w fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k

/-- Tropical duality `(gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s` along any
column-sign-coherent word from a matrix with skew-symmetrizer `s`. -/
theorem transpose_gMatrix_mul_diagonal_mul_cMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    have hcu : ∀ a l b, u = a ++ l :: b →
        (∀ i, 0 ≤ cMatrix B₀ a i l) ∨ ∀ i, cMatrix B₀ a i l ≤ 0 :=
      fun a l b hu ↦ hc a l (b ++ [k]) (by simp [hu])
    have hsu := hs.matrixMutationWord u
    have hkk : matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0 := hsu.apply_self k
    have hrel := hs.gMatrix_mul_matrixMutationWord u
    obtain ⟨ε, hε, hsign⟩ :
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε * cMatrix B₀ u i k := by
      rcases hc u k [] (by simp) with hpos | hneg
      · exact ⟨1, Or.inl rfl, fun i ↦ by simpa using hpos i⟩
      · exact ⟨-1, Or.inr rfl, fun i ↦ by linarith [hneg i]⟩
    rw [cMatrix_append_singleton_eq_mul_matrixMutationRight B₀ u hkk hε hsign,
      gMatrix_append_singleton_eq_mul_matrixMutationLeft B₀ u hkk hrel hε hsign]
    set E := matrixMutationLeft (Function.Embedding.refl K)
      (matrixMutationWord (Function.Embedding.refl K) B₀ u) k ε
    set F := matrixMutationRight (Function.Embedding.refl K)
      (matrixMutationWord (Function.Embedding.refl K) B₀ u) k ε
    calc
      (gMatrix B₀ u * E)ᵀ * diagonal s * (cMatrix B₀ u * F)
        = Eᵀ * ((gMatrix B₀ u)ᵀ * diagonal s * cMatrix B₀ u) * F := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Eᵀ * diagonal s * F := by rw [ih hcu]
      _ = diagonal s :=
          hsu.transpose_matrixMutationLeft_mul_diagonal_mul_matrixMutationRight k ε

/-- Transposed tropical duality `(cMatrix B₀ w)ᵀ * diagonal s * gMatrix B₀ w = diagonal s`
along any column-sign-coherent word from a matrix with skew-symmetrizer `s`. -/
theorem transpose_cMatrix_mul_diagonal_mul_gMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (cMatrix B₀ w)ᵀ * diagonal s * gMatrix B₀ w = diagonal s := by
  have h := congrArg Matrix.transpose (hs.transpose_gMatrix_mul_diagonal_mul_cMatrix w hc)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc] using h

/-- For a skew-symmetric matrix (`s = 1`), `(gMatrix B₀ w)ᵀ` is the left inverse of `cMatrix B₀ w`
along any column-sign-coherent word. -/
theorem transpose_gMatrix_mul_cMatrix (hs : B₀.IsSkewSymmetrizer 1) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w)ᵀ * cMatrix B₀ w = 1 := by
  simpa using hs.transpose_gMatrix_mul_diagonal_mul_cMatrix w hc

/-- For a skew-symmetric matrix (`s = 1`), `cMatrix B₀ w * (gMatrix B₀ w)ᵀ = 1` along any
column-sign-coherent word. -/
theorem cMatrix_mul_transpose_gMatrix (hs : B₀.IsSkewSymmetrizer 1) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    cMatrix B₀ w * (gMatrix B₀ w)ᵀ = 1 :=
  mul_eq_one_comm.mp (hs.transpose_gMatrix_mul_cMatrix w hc)

/-- Determinant of `cMatrix` along any column-sign-coherent word for a skew-symmetrizable matrix. -/
theorem det_cMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (cMatrix B₀ w).det = (-1) ^ w.length :=
  det_cMatrix_of_signCoherent B₀ w (fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k) hc

/-- Determinant of `gMatrix` along any column-sign-coherent word for a skew-symmetrizable matrix. -/
theorem det_gMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w).det = (-1) ^ w.length :=
  det_gMatrix_of_signCoherent B₀ w (fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k) hc

/-- Unimodularity of `cMatrix` over `ℤ` along any column-sign-coherent word for a
skew-symmetrizable matrix. -/
theorem isUnit_cMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (cMatrix B₀ w) :=
  isUnit_cMatrix_of_signCoherent B₀ w (fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k) hc

/-- Unimodularity of `gMatrix` over `ℤ` along any column-sign-coherent word for a
skew-symmetrizable matrix. -/
theorem isUnit_gMatrix (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (gMatrix B₀ w) :=
  isUnit_gMatrix_of_signCoherent B₀ w (fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k) hc

end Matrix.IsSkewSymmetrizer

namespace TauCeti

open Matrix

/-- In rank one with zero initial matrix, the first mutation sends both `cMatrix` and `gMatrix`
to `(-1)`. -/
example : cMatrix (0 : Matrix (Fin 1) (Fin 1) ℤ) [0] = !![-1] ∧
    gMatrix (0 : Matrix (Fin 1) (Fin 1) ℤ) [0] = !![-1] := by
  constructor
  · ext i j
    fin_cases i
    fin_cases j
    simp
  · rw [gMatrix_singleton (0 : Matrix (Fin 1) (Fin 1) ℤ) rfl]
    ext i j
    fin_cases i
    fin_cases j
    simp [matrixMutationLeft_apply]

/-- For the skew-symmetrizable matrix `((0, 1), (-2, 0))` with symmetrizer `(2, 1)`, mutating in
the first direction gives `C' = ((-1, 1), (0, 1))`, `G' = ((-1, 0), (2, 1))`, and
`G'ᵀ * diag(2, 1) * C' = diag(2, 1)`. -/
example : cMatrix !![0, 1; -2, 0] [0] = !![-1, 1; 0, 1] ∧
    gMatrix !![0, 1; -2, 0] [0] = !![-1, 0; 2, 1] ∧
    (gMatrix !![0, 1; -2, 0] [0])ᵀ * diagonal ![2, 1] * cMatrix !![0, 1; -2, 0] [0] =
      diagonal ![2, 1] := by
  set B₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -2, 0]
  have hc : cMatrix B₀ [0] = !![-1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀]
  have hg : gMatrix B₀ [0] = !![-1, 0; 2, 1] := by
    rw [gMatrix_singleton B₀ rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, matrixMutationLeft_apply]
  refine ⟨hc, hg, ?_⟩
  rw [hc, hg]
  decide

/-- Along the two-step type `A₂` word `[0, 1]` from `((0, 1), (-1, 0))`, one obtains
`C = ((0, -1), (1, -1))` (with negative second `c`-vector `![-1, -1]`),
`G = ((-1, -1), (1, 0))`, and `Gᵀ * C = 1`. -/
example : cMatrix !![0, 1; -1, 0] [0, 1] = !![0, -1; 1, -1] ∧
    gMatrix !![0, 1; -1, 0] [0, 1] = !![-1, -1; 1, 0] ∧
    (gMatrix !![0, 1; -1, 0] [0, 1])ᵀ * cMatrix !![0, 1; -1, 0] [0, 1] = 1 := by
  set B₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
  have h01 : ([0, 1] : List (Fin 2)) = [0] ++ [1] := rfl
  have hB₁ : matrixMutationWord (Function.Embedding.refl (Fin 2)) B₀ [0] = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, matrixMutation_apply]
  have hc₁ : cMatrix B₀ [0] = !![-1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀]
  have hg₁ : gMatrix B₀ [0] = !![-1, 0; 1, 1] := by
    rw [gMatrix_singleton B₀ rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, matrixMutationLeft_apply]
  have hc₂ : cMatrix B₀ ([0] ++ [1]) = !![0, -1; 1, -1] := by
    ext i j
    rw [cMatrix_append_singleton_apply, hc₁, hB₁]
    fin_cases i <;> fin_cases j <;> decide
  have hg₂ : gMatrix B₀ ([0] ++ [1]) = !![-1, -1; 1, 0] := by
    ext i j
    by_cases hj : j = 1
    · subst j
      rw [gMatrix_append_singleton_col, hg₁, hc₁, hB₁]
      fin_cases i <;> simp [B₀, Fin.sum_univ_two]
    · rw [gMatrix_append_singleton_of_ne B₀ [0] 1 i hj, hg₁]
      fin_cases i <;> fin_cases j <;> simp at hj ⊢
  rw [h01]
  refine ⟨hc₂, hg₂, ?_⟩
  rw [hc₂, hg₂]
  decide

end TauCeti
