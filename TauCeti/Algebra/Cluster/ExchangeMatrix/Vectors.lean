/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility
public import TauCeti.Algebra.Cluster.ExchangeMatrix.DegreeMutation

import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Order.Module.Sign
import TauCeti.Data.List.Infix

/-!
# Principal `c`- and `g`-matrices and tropical duality

Starting from a square integer matrix `B₀ : Matrix K K ℤ`, mutating the principal extension
`fromRows B₀ 1` along a finite word `w : List K` produces a mutable top block
`matrixMutationWord (Function.Embedding.refl K) B₀ w` and a frozen bottom block `cMatrix B₀ w`,
whose columns `cVector B₀ w j` are the `c`-vectors along `w`. In cluster algebras with principal
coefficients, `c`-vectors record the tropical initial-coefficient exponents in principal exchange
relations and `Y`-seed patterns, while `g`-vectors record the multi-degrees and leading
Laurent-monomial exponents of principal cluster variables in the separation formula.

For finite `K`, the principal `g`-matrix `gMatrix B₀ w` starts at the identity matrix and updates
column `k` at step `w ↦ w ++ [k]` by
`g'_k = -g_k + G_w [b_{•, k; w}]₊ - B₀ [c_{•, k; w}]₊`, leaving all other columns fixed. When the
mutable diagonal entry vanishes at every step along `w`, the columns of `gMatrix B₀ w` coincide
with the mutable part of `degreeMutationWord` started from `Sum.elim 1.col (-B₀.col)` on
`fromRows B₀ 1`, yielding the fundamental relation
`gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w = B₀ * cMatrix B₀ w`.

Every row of `cMatrix B₀ w` is unconditionally nonzero. When column `k` of `cMatrix B₀ w` has
coherent sign `ε ∈ {1, -1}` (`∀ i, 0 ≤ ε * cMatrix B₀ w i k`), for finite `K`, `cMatrix`
right-multiplies by `Fε` with no diagonal hypothesis, and when `B_w k k = 0` and
`G_w * B_w = B₀ * C_w` also hold, `gMatrix` right-multiplies by `Eε`. Along any
column-sign-coherent word, the `c`-vectors are linearly independent over `ℤ` (hence nonzero) for
arbitrary `K`, any terminal `c`-vector that is itself sign-coherent satisfies the principal
exchange-monomial exponent dichotomy, and for finite `K`, `cMatrix B₀ w` has determinant
`(-1) ^ w.length` and is unimodular over `ℤ`. When the mutable diagonal also vanishes at each step
along a column-sign-coherent word, `gMatrix B₀ w` likewise has determinant `(-1) ^ w.length`, is
unimodular over `ℤ` with nonzero rows and `g`-vectors, and satisfies Nakanishi–Zelevinsky tropical
duality `(gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s` for any skew-symmetrizer `s`
of `B₀`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compositio Mathematica 143
  (2007), §§2, 6, Proposition 6.6 and (6.14).
* T. Nakanishi and A. Zelevinsky, *On tropical dualities in cluster algebras*, Contemporary
  Mathematics 565 (2012), Theorem 1.2, Proposition 1.3 and (2.7).
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
theorem cMatrix_def : cMatrix B₀ w =
    (matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w).submatrix Sum.inr id := (rfl)

/-- Definitional presentation of `cVector` as a column of `cMatrix`. -/
theorem cVector_def (j : K) : cVector B₀ w j = (cMatrix B₀ w).col j := (rfl)

/-- Entrywise formula for `cMatrix` via the `Sum.inr` rows of the mutated principal extension. -/
theorem cMatrix_apply (i j : K) : cMatrix B₀ w i j =
    matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w (Sum.inr i) j := (rfl)

@[simp]
theorem cVector_apply (j i : K) : cVector B₀ w j i = cMatrix B₀ w i j := (rfl)

/-- Mutating `fromRows B₀ 1` along `w` produces
`matrixMutationWord (Function.Embedding.refl K) B₀ w` in the mutable rows and `cMatrix B₀ w` in
the frozen rows. -/
@[simp]
theorem matrixMutationWord_fromRows_one :
    matrixMutationWord Function.Embedding.inl (fromRows B₀ 1) w =
      fromRows (matrixMutationWord (Function.Embedding.refl K) B₀ w) (cMatrix B₀ w) := by
  have hsub : (fromRows B₀ (1 : Matrix K K ℤ)).submatrix Function.Embedding.inl id = B₀ := by
    ext; simp
  have htop := matrixMutationWord_refl_submatrix_row Function.Embedding.inl
    (fromRows B₀ (1 : Matrix K K ℤ)) w
  rw [hsub] at htop
  ext (i | i) j
  · simpa using (congrArg (fun M ↦ M i j) htop).symm
  · simp [cMatrix_apply]

@[simp]
theorem cMatrix_nil : cMatrix B₀ [] = 1 := by
  ext i j; simp only [cMatrix_apply, matrixMutationWord_nil, fromRows_apply_inr]

@[simp]
theorem cVector_nil (j : K) : cVector B₀ [] j = Pi.single j 1 := by
  ext i; by_cases h : i = j <;> simp [h]

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
theorem cMatrix_append_singleton_apply_col (k i : K) :
    cMatrix B₀ (w ++ [k]) i k = -cMatrix B₀ w i k := by simp [cMatrix_append_singleton_apply]

@[simp]
theorem cVector_append_singleton_self (k : K) : cVector B₀ (w ++ [k]) k = -cVector B₀ w k := by
  ext i; simp

theorem cMatrix_append_singleton_apply_of_ne (k i : K) {j : K} (hj : j ≠ k) :
    cMatrix B₀ (w ++ [k]) i j =
      cMatrix B₀ w i j +
        (cMatrix B₀ w i k)⁺ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁺ -
        (cMatrix B₀ w i k)⁻ * (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁻ := by
  simp [cMatrix_append_singleton_apply, hj]

/-- Vector recurrence for `cVector` at a non-mutated index `j ≠ k`. -/
theorem cVector_append_singleton_of_ne (k : K) {j : K} (hj : j ≠ k) :
    cVector B₀ (w ++ [k]) j =
      cVector B₀ w j +
        (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁺ • (cVector B₀ w k)⁺ -
        (matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁻ • (cVector B₀ w k)⁻ := by
  ext i
  simp only [cVector_apply, cMatrix_append_singleton_apply_of_ne B₀ w k i hj,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.posPart_apply, Pi.negPart_apply, smul_eq_mul]
  ring

/-- Single-step principal `c`-matrix at `[k]` equals the positive-sign right mutation factor
`F₁(B₀, k)`. -/
@[simp]
theorem cMatrix_singleton (k : K) :
    cMatrix B₀ [k] = matrixMutationRight (Function.Embedding.refl K) B₀ k 1 := by
  ext i j
  have h := cMatrix_append_singleton_apply B₀ [] k i j
  simp only [List.nil_append, cMatrix_nil, matrixMutationWord_nil] at h
  rw [h, matrixMutationRight_apply]
  by_cases hj : j = k <;> by_cases hi : i = k <;> simp [hi, hj, Ne.symm, Matrix.one_apply]

/-- Equal adjacent directions cancel in `cMatrix`. -/
theorem cMatrix_append_cons_cons_self (u v : List K) (k : K) :
    cMatrix B₀ (u ++ k :: k :: v) = cMatrix B₀ (u ++ v) := by
  simp only [cMatrix_def, matrixMutationWord_append_cons_cons_self]

/-- Every row of `cMatrix B₀ w` is nonzero, with no assumptions on `B₀` or `K`. -/
theorem cMatrix_row_ne_zero (i : K) : cMatrix B₀ w i ≠ 0 := by
  induction w using List.reverseRecOn with
  | nil => exact fun h0 ↦ by simpa using congrFun h0 i
  | append_singleton u k ih =>
    refine fun h0 ↦ ih (funext fun j ↦ ?_)
    have hk : cMatrix B₀ u i k = 0 := by simpa using congrFun h0 k
    by_cases hj : j = k
    · simpa [hj] using hk
    · simpa [cMatrix_append_singleton_apply_of_ne B₀ u k i hj, hk] using congrFun h0 j

/-- Simultaneous relabelling of indices transports `cMatrix` along mapped words. -/
theorem cMatrix_reindex [DecidableEq K'] (e : K ≃ K') :
    cMatrix (B₀.reindex e e) (w.map e) = (cMatrix B₀ w).reindex e e := by
  have hsub : fromRows (B₀.reindex e e) (1 : Matrix K' K' ℤ) =
      (fromRows B₀ (1 : Matrix K K ℤ)).submatrix (e.symm.sumCongr e.symm) e.symm := by
    ext (i | i) j <;> simp [Matrix.one_apply]
  have hword := matrixMutationWord_submatrix (row := (Function.Embedding.inl : K ↪ K ⊕ K))
    (row' := (Function.Embedding.inl : K' ↪ K' ⊕ K')) (f := e.symm.sumCongr e.symm) (g := e.symm)
    (e.symm.sumCongr e.symm).injective (fun _ ↦ rfl) (fromRows B₀ (1 : Matrix K K ℤ)) (w.map e)
  have hmap : (w.map e).map e.symm = w := by simp [List.map_map]
  rw [← hsub, hmap, matrixMutationWord_fromRows_one, matrixMutationWord_fromRows_one] at hword
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
  have hf₁ (i : K₁) : f.symm (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr i) := by simp [f]
  have hf₂ (i : K₂) : f.symm (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr i) := by simp [f]
  have hinit : fromRows (fromBlocks B₁ 0 0 B₂) (1 : Matrix (K₁ ⊕ K₂) (K₁ ⊕ K₂) ℤ) =
      (fromBlocks (fromRows B₁ (1 : Matrix K₁ K₁ ℤ)) 0 0
        (fromRows B₂ (1 : Matrix K₂ K₂ ℤ))).submatrix f.symm id := by
    ext ((i | i) | (i | i)) (j | j) <;> simp [f, Matrix.one_apply]
  have hword := matrixMutationWord_submatrix
    (row := (Function.Embedding.inl : K₁ ↪ K₁ ⊕ K₁).sumMap (Function.Embedding.inl : K₂ ↪ K₂ ⊕ K₂))
    (row' := (Function.Embedding.inl : K₁ ⊕ K₂ ↪ (K₁ ⊕ K₂) ⊕ (K₁ ⊕ K₂)))
    (f := f.symm) (g := id) f.symm.injective (by rintro (k | k) <;> simp [f])
    (fromBlocks (fromRows B₁ (1 : Matrix K₁ K₁ ℤ)) 0 0 (fromRows B₂ (1 : Matrix K₂ K₂ ℤ))) w
  simp only [List.map_id, ← hinit, matrixMutationWord_fromBlocks,
    matrixMutationWord_fromRows_one] at hword
  ext (i | i) (j | j)
  · simpa [hf₁] using congrArg (fun M ↦ M (Sum.inr (Sum.inl i)) (Sum.inl j)) hword
  · simpa [hf₁] using congrArg (fun M ↦ M (Sum.inr (Sum.inl i)) (Sum.inr j)) hword
  · simpa [hf₂] using congrArg (fun M ↦ M (Sum.inr (Sum.inr i)) (Sum.inl j)) hword
  · simpa [hf₂] using congrArg (fun M ↦ M (Sum.inr (Sum.inr i)) (Sum.inr j)) hword

/-- Signed entrywise step recurrence for `cMatrix` when column `k` has coherent sign `ε ∈ {1, -1}`
(`∀ i, 0 ≤ ε * cMatrix B₀ w i k`), requiring no finiteness or diagonal hypothesis. -/
theorem cMatrix_append_singleton_apply_of_sign {k : K} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hsign : ∀ i, 0 ≤ ε * cMatrix B₀ w i k) (i j : K) :
    cMatrix B₀ (w ++ [k]) i j =
      if j = k then -cMatrix B₀ w i k
      else cMatrix B₀ w i j +
        cMatrix B₀ w i k * (ε * matrixMutationWord (Function.Embedding.refl K) B₀ w k j)⁺ := by
  rw [cMatrix_append_singleton_apply]
  by_cases hj : j = k
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    rcases hε with rfl | rfl
    · have hp : 0 ≤ cMatrix B₀ w i k := by simpa using hsign i
      simp [posPart_eq_self.mpr hp, negPart_eq_zero.mpr hp]
    · have hn : cMatrix B₀ w i k ≤ 0 := by linarith [hsign i]
      simp [posPart_eq_zero.mpr hn, negPart_eq_neg.mpr hn, posPart_neg]

private theorem signCoherent_append_singleton {B₀ : Matrix K K ℤ} {u : List K} {k : K}
    (hc : ∀ a l b, u ++ [k] = a ++ l :: b →
      (∀ i, 0 ≤ cMatrix B₀ a i l) ∨ ∀ i, cMatrix B₀ a i l ≤ 0) :
    (∀ a l b, u = a ++ l :: b → (∀ i, 0 ≤ cMatrix B₀ a i l) ∨ ∀ i, cMatrix B₀ a i l ≤ 0) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε * cMatrix B₀ u i k :=
  ⟨(List.prefix_append u [k]).forall_append_cons hc, by
    simpa only [smul_eq_mul] using
      (exists_eq_one_or_neg_one_and_forall_smul_nonneg_iff ℤ (cMatrix B₀ u · k)).mpr
        (hc u k [] (by simp))⟩

/-- Along any column-sign-coherent word, the family of `c`-vectors `cVector B₀ w` is linearly
independent over `ℤ`, with no finiteness or vanishing-diagonal hypothesis. -/
theorem linearIndependent_cVector_of_signCoherent
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    LinearIndependent ℤ (cVector B₀ w) := by
  induction w using List.reverseRecOn with
  | nil => simpa [funext (cVector_nil B₀)] using Pi.linearIndependent_single_one K ℤ
  | append_singleton u k ih =>
    obtain ⟨hcu, ε, hε, hsign⟩ := signCoherent_append_singleton hc
    let m : K → ℤ := fun j ↦ (ε * matrixMutationWord (Function.Embedding.refl K) B₀ u k j)⁺
    have hstep : cVector B₀ (u ++ [k]) =
        Function.update (1 : K → ℤˣ) k (-1) •
          (cVector B₀ u + fun j ↦ Function.update m k 0 j • cVector B₀ u k) := by
      ext j i
      rw [cVector_apply, cMatrix_append_singleton_apply_of_sign B₀ u hε hsign]
      by_cases hj : j = k <;> simp [hj, mul_comm, m]
    rw [hstep]
    exact ((linearIndependent_add_smul_iff (Function.update_self k 0 m)).mpr (ih hcu)).units_smul _

/-- Along any column-sign-coherent word, no `c`-vector vanishes. -/
theorem cVector_ne_zero_of_signCoherent
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (j : K) :
    cVector B₀ w j ≠ 0 :=
  (linearIndependent_cVector_of_signCoherent B₀ w hc).ne_zero j

/-- Principal exchange-monomial dichotomy: along a column-sign-coherent word, if `cVector B₀ w j`
is itself sign-coherent, then one of its positive-part and negative-part frozen-exponent vectors
vanishes and the other is nonzero. -/
theorem cVector_posPart_eq_zero_or_negPart_eq_zero_of_signCoherent
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) {j : K}
    (hj : (∀ i, 0 ≤ cVector B₀ w j i) ∨ ∀ i, cVector B₀ w j i ≤ 0) :
    ((cVector B₀ w j)⁺ = 0 ∧ (cVector B₀ w j)⁻ ≠ 0) ∨
      ((cVector B₀ w j)⁻ = 0 ∧ (cVector B₀ w j)⁺ ≠ 0) := by
  have hne := cVector_ne_zero_of_signCoherent B₀ w hc j
  rcases hj with hpos | hneg
  · exact Or.inr ⟨negPart_eq_zero.mpr hpos,
      fun hp ↦ hne ((posPart_eq_self.mpr hpos).symm.trans hp)⟩
  · exact Or.inl ⟨posPart_eq_zero.mpr hneg,
      fun hn ↦ hne (neg_eq_zero.mp ((negPart_eq_neg.mpr hneg).symm.trans hn))⟩

end CMatrix

namespace ExchangeMatrix

variable {K : Type*} (B : ExchangeMatrix (Function.Embedding.refl K))

/-- Mutating the bundled principal extension along `w` gives `(B.mutationWord w).matrix` in the
mutable block and `cMatrix B.matrix w` in the frozen block. -/
theorem mutationWord_principalExtension_matrix [DecidableEq K] (w : List K) :
    (B.principalExtension.mutationWord w).matrix =
      fromRows (B.mutationWord w).matrix (cMatrix B.matrix w) := by
  rw [B.principalExtension.mutationWord_matrix, B.principalExtension_matrix,
    matrixMutationWord_fromRows_one, B.mutationWord_matrix]

end ExchangeMatrix

section GMatrix

variable {K K' K₁ K₂ : Type*} [DecidableEq K] [Fintype K]

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
theorem gVector_def (j : K) : gVector B₀ w j = (gMatrix B₀ w).col j := (rfl)

@[simp]
theorem gVector_apply (j i : K) : gVector B₀ w j i = gMatrix B₀ w i j := (rfl)

@[simp]
theorem gMatrix_nil : gMatrix B₀ [] = 1 := (rfl)

@[simp]
theorem gVector_nil (j : K) : gVector B₀ [] j = Pi.single j 1 := by
  ext i; by_cases h : i = j <;> simp [h]

/-- Single-step column update of `gMatrix` on appending a direction `k`. -/
theorem gMatrix_append_singleton (k : K) :
    gMatrix B₀ (w ++ [k]) =
      (gMatrix B₀ w).updateCol k fun i ↦
        -gMatrix B₀ w i k +
          ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ -
          ∑ l, B₀ i l * (cMatrix B₀ w l k)⁺ := by
  simp only [gMatrix, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rcases h : w.foldl (gMatrixFold B₀) (fromRows B₀ 1, 1) with ⟨Bext, G⟩
  have h1 : Bext = fromRows (matrixMutationWord (Function.Embedding.refl K) B₀ w) (cMatrix B₀ w) :=
    by simpa [h] using gMatrixFold_fst B₀ w
  simp [gMatrixFold, h1]

/-- Entrywise recurrence for the mutated column `k` of `gMatrix B₀ (w ++ [k])`. -/
theorem gMatrix_append_singleton_apply_col (k i : K) :
    gMatrix B₀ (w ++ [k]) i k =
      -gMatrix B₀ w i k +
        ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ -
        ∑ l, B₀ i l * (cMatrix B₀ w l k)⁺ := by
  rw [gMatrix_append_singleton, updateCol_self]

@[simp]
theorem gMatrix_append_singleton_apply_of_ne (k i : K) {j : K} (hj : j ≠ k) :
    gMatrix B₀ (w ++ [k]) i j = gMatrix B₀ w i j := by
  rw [gMatrix_append_singleton, updateCol_ne hj]

@[simp]
theorem gVector_append_singleton_of_ne (k : K) {j : K} (hj : j ≠ k) :
    gVector B₀ (w ++ [k]) j = gVector B₀ w j := by
  ext i; exact gMatrix_append_singleton_apply_of_ne B₀ w k i hj

/-- Vector recurrence `g'_k = -g_k + G_w *ᵥ [b_{•, k; w}]₊ - B₀ *ᵥ [c_{k; w}]₊` for the
mutated `g`-vector. -/
theorem gVector_append_singleton_self (k : K) :
    gVector B₀ (w ++ [k]) k =
      -gVector B₀ w k +
        gMatrix B₀ w *ᵥ ((matrixMutationWord (Function.Embedding.refl K) B₀ w).col k)⁺ -
        B₀ *ᵥ (cVector B₀ w k)⁺ := by
  ext i; simp [gMatrix_append_singleton_apply_col, mulVec, dotProduct]

/-- The initial principal grading `Sum.elim 1.col (-B₀.col)` annihilates every mutable column of
the principal extension `fromRows B₀ 1`. -/
theorem sum_fromRows_one_smul_elim_col_eq_zero (j : K) :
    ∑ a : K ⊕ K, fromRows B₀ (1 : Matrix K K ℤ) a j •
      Sum.elim (1 : Matrix K K ℤ).col (-B₀.col) a = 0 := by
  ext i; simp [Fintype.sum_sum_type, Finset.sum_apply, Matrix.col_apply, Matrix.one_apply, mul_ite]

omit [Fintype K] in
private theorem matrixMutationWord_fromRows_one_inl_eq_zero {B₀ : Matrix K K ℤ} {w : List K}
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0) :
    ∀ u k v, w = u ++ k :: v →
      matrixMutationWord Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) u (Sum.inl k) k = 0 :=
  fun u k v hw ↦ by simpa [matrixMutationWord_fromRows_one] using hdiag u k v hw

omit [Fintype K] in
private theorem hdiag_append_singleton {B₀ : Matrix K K ℤ} {u : List K} {k : K}
    (hdiag : ∀ a l b, u ++ [k] = a ++ l :: b →
      matrixMutationWord (Function.Embedding.refl K) B₀ a l l = 0) :
    (∀ a l b, u = a ++ l :: b →
      matrixMutationWord (Function.Embedding.refl K) B₀ a l l = 0) ∧
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0 :=
  ⟨(List.prefix_append u [k]).forall_append_cons hdiag, hdiag u k [] (by simp)⟩

/-- When the mutable diagonal entry vanishes at each step of `w`, propagating `Sum.elim 1.col
(-B₀.col)` on `fromRows B₀ 1` produces `(gMatrix B₀ w).col` on mutable indices and `-B₀.col` on
frozen indices. -/
theorem degreeMutationWord_fromRows_one_elim_col
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0) :
    degreeMutationWord Function.Embedding.inl (fromRows B₀ 1)
        (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) w =
      Sum.elim (gMatrix B₀ w).col (-B₀.col) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    obtain ⟨hdu, hkk⟩ := hdiag_append_singleton hdiag
    have hu := ih hdu
    have hann (j : K) : ∑ a : K ⊕ K,
        matrixMutationWord Function.Embedding.inl (fromRows B₀ (1 : Matrix K K ℤ)) u a j •
          Sum.elim (gMatrix B₀ u).col (-B₀.col) a = 0 := by
      rw [← hu]
      exact sum_matrixMutationWord_smul_degreeMutationWord_eq_zero Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) u
        (matrixMutationWord_fromRows_one_inl_eq_zero hdu)
        (sum_fromRows_one_smul_elim_col_eq_zero B₀) j
    have hkk' : matrixMutationWord Function.Embedding.inl
        (fromRows B₀ (1 : Matrix K K ℤ)) u (Sum.inl k) k = 0 := by
      simpa [matrixMutationWord_fromRows_one] using hkk
    rw [degreeMutationWord_append, hu, degreeMutationWord_singleton]
    ext (j | j) i
    · by_cases hjk : j = k
      · subst j
        have hpos := congrFun (degreeMutation_apply_row_posPart_univ Function.Embedding.inl
          (matrixMutationWord Function.Embedding.inl (fromRows B₀ (1 : Matrix K K ℤ)) u) k
          (Sum.elim (gMatrix B₀ u).col (-B₀.col)) hkk' (hann k)) i
        rw [Function.Embedding.inl_apply] at hpos
        rw [hpos]
        simp [Fintype.sum_sum_type, Finset.sum_apply, gMatrix_append_singleton_apply_col,
          mul_comm, sub_eq_add_neg, add_assoc]
      · simp [hjk]
    · simp

/-- Fundamental relation `G_w * B_w = B₀ * C_w` between the principal `g`-matrix, the mutated
mutable matrix, the initial matrix, and the principal `c`-matrix, assuming only that the mutable
diagonal entry vanishes at each step of `w`. -/
theorem gMatrix_mul_matrixMutationWord
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0) :
    gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w = B₀ * cMatrix B₀ w := by
  ext i j
  have hann := congrFun (sum_matrixMutationWord_smul_degreeMutationWord_eq_zero
    Function.Embedding.inl (fromRows B₀ (1 : Matrix K K ℤ))
    (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) w
    (matrixMutationWord_fromRows_one_inl_eq_zero hdiag)
    (sum_fromRows_one_smul_elim_col_eq_zero B₀) j) i
  rw [degreeMutationWord_fromRows_one_elim_col B₀ w hdiag, matrixMutationWord_fromRows_one] at hann
  simp [Fintype.sum_sum_type, Finset.sum_apply] at hann
  simp only [Matrix.mul_apply]
  simp_rw [mul_comm (gMatrix B₀ w i _), mul_comm (B₀ i _)]
  linear_combination hann

/-- Negative-part recurrence for column `k` of `gMatrix B₀ (w ++ [k])` when
`G_w * B_w = B₀ * C_w`. -/
theorem gMatrix_append_singleton_apply_col_negPart (k i : K)
    (hrel : gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w =
      B₀ * cMatrix B₀ w) :
    gMatrix B₀ (w ++ [k]) i k =
      -gMatrix B₀ w i k +
        ∑ l, gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁻ -
        ∑ l, B₀ i l * (cMatrix B₀ w l k)⁻ := by
  have hentry : ∑ l, gMatrix B₀ w i l * matrixMutationWord (Function.Embedding.refl K) B₀ w l k =
      ∑ l, B₀ i l * cMatrix B₀ w l k := by simpa [Matrix.mul_apply] using congrArg (· i k) hrel
  have hB (l : K) :
      gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁺ =
        gMatrix B₀ w i l * matrixMutationWord (Function.Embedding.refl K) B₀ w l k +
          gMatrix B₀ w i l * (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)⁻ := by
    linear_combination gMatrix B₀ w i l *
      posPart_sub_negPart (matrixMutationWord (Function.Embedding.refl K) B₀ w l k)
  have hC (l : K) : B₀ i l * (cMatrix B₀ w l k)⁺ =
      B₀ i l * cMatrix B₀ w l k + B₀ i l * (cMatrix B₀ w l k)⁻ := by
    linear_combination B₀ i l * posPart_sub_negPart (cMatrix B₀ w l k)
  rw [gMatrix_append_singleton_apply_col]
  simp_rw [hB, hC, Finset.sum_add_distrib]
  linear_combination hentry

/-- Equal adjacent directions `k, k` after prefix `u` cancel in `gMatrix` whenever `B_u k k = 0`
and `G_u * B_u = B₀ * C_u`. -/
theorem gMatrix_append_cons_cons_self (u v : List K) (k : K)
    (hkk : matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hrel : gMatrix B₀ u * matrixMutationWord (Function.Embedding.refl K) B₀ u =
      B₀ * cMatrix B₀ u) :
    gMatrix B₀ (u ++ k :: k :: v) = gMatrix B₀ (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil =>
    have hpair : u ++ [k, k] = (u ++ [k]) ++ [k] := by simp
    rw [hpair, List.append_nil]
    ext i j
    by_cases hj : j = k
    · subst j
      rw [gMatrix_append_singleton_apply_col]
      simp only [matrixMutationWord_append, matrixMutationWord_cons, matrixMutationWord_nil,
        matrixMutation_apply_col, cMatrix_append_singleton_apply_col, posPart_neg]
      have hsumG : ∑ l, gMatrix B₀ (u ++ [k]) i l *
            (matrixMutationWord (Function.Embedding.refl K) B₀ u l k)⁻ =
          ∑ l, gMatrix B₀ u i l * (matrixMutationWord (Function.Embedding.refl K) B₀ u l k)⁻ :=
        Finset.sum_congr rfl fun l _ ↦ by by_cases hlk : l = k <;> simp [hlk, hkk]
      rw [hsumG, gMatrix_append_singleton_apply_col_negPart B₀ u k i hrel]
      ring
    · rw [gMatrix_append_singleton_apply_of_ne B₀ (u ++ [k]) k i hj,
        gMatrix_append_singleton_apply_of_ne B₀ u k i hj]
  | append_singleton v' l ih =>
    have h1 : u ++ k :: k :: (v' ++ [l]) = (u ++ k :: k :: v') ++ [l] := by simp
    have h2 : u ++ (v' ++ [l]) = (u ++ v') ++ [l] := by simp
    rw [h1, h2, gMatrix_append_singleton, gMatrix_append_singleton, ih,
      matrixMutationWord_append_cons_cons_self, cMatrix_append_cons_cons_self]

/-- Simultaneous relabelling of indices transports `gMatrix` along mapped words. -/
theorem gMatrix_reindex [DecidableEq K'] [Fintype K'] (e : K ≃ K') :
    gMatrix (B₀.reindex e e) (w.map e) = (gMatrix B₀ w).reindex e e := by
  induction w using List.reverseRecOn with
  | nil => ext; simp [Matrix.one_apply]
  | append_singleton u k ih =>
    have hbw : matrixMutationWord (Function.Embedding.refl K') (B₀.reindex e e) (u.map e) =
        (matrixMutationWord (Function.Embedding.refl K) B₀ u).reindex e e := by
      simpa [List.map_map] using matrixMutationWord_submatrix
        (row := Function.Embedding.refl K) (row' := Function.Embedding.refl K')
        (f := e.symm) (g := e.symm) e.symm.injective (fun _ ↦ rfl) B₀ (u.map e)
    rw [List.map_append, List.map_singleton, gMatrix_append_singleton, gMatrix_append_singleton,
      Matrix.reindex_updateCol, ih, hbw, cMatrix_reindex B₀ u e]
    congr 1; ext i
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rw [e.symm.sum_comp (fun l ↦ gMatrix B₀ u (e.symm i) l *
        (matrixMutationWord (Function.Embedding.refl K) B₀ u l k)⁺),
      e.symm.sum_comp (fun l ↦ B₀ (e.symm i) l * (cMatrix B₀ u l k)⁺)]

/-- On a block-diagonal initial matrix, `gMatrix` splits into the `g`-matrices of the blocks
along their projected subwords. -/
theorem gMatrix_fromBlocks [DecidableEq K₁] [DecidableEq K₂] [Fintype K₁] [Fintype K₂]
    (B₁ : Matrix K₁ K₁ ℤ) (B₂ : Matrix K₂ K₂ ℤ) (w : List (K₁ ⊕ K₂)) :
    gMatrix (fromBlocks B₁ 0 0 B₂) w =
      fromBlocks (gMatrix B₁ (w.filterMap Sum.getLeft?)) 0 0
        (gMatrix B₂ (w.filterMap Sum.getRight?)) := by
  have hrefl : (Function.Embedding.refl K₁).sumMap (Function.Embedding.refl K₂) =
      Function.Embedding.refl (K₁ ⊕ K₂) := by ext (_ | _) <;> simp
  induction w using List.reverseRecOn with
  | nil => ext (_ | _) (_ | _) <;> simp [Matrix.one_apply]
  | append_singleton u k ih =>
    have hbw : matrixMutationWord (Function.Embedding.refl (K₁ ⊕ K₂)) (fromBlocks B₁ 0 0 B₂) u =
        fromBlocks
          (matrixMutationWord (Function.Embedding.refl K₁) B₁ (u.filterMap Sum.getLeft?)) 0 0
          (matrixMutationWord (Function.Embedding.refl K₂) B₂ (u.filterMap Sum.getRight?)) := by
      rw [← hrefl, matrixMutationWord_fromBlocks]
    cases k with
    | inl k =>
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        Sum.getLeft?_inl, Sum.getRight?_inl, List.append_nil]
      ext i (j | j)
      · by_cases hjk : j = k
        · subst j
          rw [gMatrix_append_singleton_apply_col, ih, hbw, cMatrix_fromBlocks]
          cases i <;> simp [Fintype.sum_sum_type, gMatrix_append_singleton_apply_col]
        · cases i <;> simp [hjk, ih]
      · cases i <;> simp [ih]
    | inr k =>
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        Sum.getLeft?_inr, Sum.getRight?_inr, List.append_nil]
      ext i (j | j)
      · cases i <;> simp [ih]
      · by_cases hjk : j = k
        · subst j
          rw [gMatrix_append_singleton_apply_col, ih, hbw, cMatrix_fromBlocks]
          cases i <;> simp [Fintype.sum_sum_type, gMatrix_append_singleton_apply_col]
        · cases i <;> simp [hjk, ih]

/-! ### Signed recurrences and tropical duality -/

/-- When column `k` of `cMatrix B₀ w` has coherent sign `ε ∈ {1, -1}`
(`∀ i, 0 ≤ ε * cMatrix B₀ w i k`), `cMatrix` right-multiplies by `Fε(B_w, k)` at step `k`. -/
theorem cMatrix_append_singleton_eq_mul_matrixMutationRight {k : K} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hsign : ∀ i, 0 ≤ ε * cMatrix B₀ w i k) :
    cMatrix B₀ (w ++ [k]) =
      cMatrix B₀ w *
        matrixMutationRight (Function.Embedding.refl K)
          (matrixMutationWord (Function.Embedding.refl K) B₀ w) k ε := by
  ext i j
  rw [cMatrix_append_singleton_apply_of_sign B₀ w hε hsign, mul_matrixMutationRight_apply,
    Function.Embedding.refl_apply]
  by_cases hj : j = k <;> simp [hj]

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
  rw [matrixMutationLeft_def, Function.Embedding.refl_apply, Matrix.mul_updateCol, Matrix.mul_one,
    gMatrix_append_singleton]
  congr 1; ext i
  have hmul : (gMatrix B₀ w *ᵥ fun l ↦ if l = k then -1 else (-ε * Bw l k)⁺) i =
      -gMatrix B₀ w i k + ∑ l, gMatrix B₀ w i l * (-ε * Bw l k)⁺ := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase Finset.univ
        (fun l ↦ gMatrix B₀ w i l * (-ε * Bw l k)⁺) (Finset.mem_univ k)]
    simp only [↓reduceIte, mul_neg, mul_one, hkk, mul_zero, posPart_zero, zero_add]
    exact congrArg _ (Finset.sum_congr rfl fun l hl ↦ by simp [(Finset.mem_erase.mp hl).1])
  rw [hmul]
  rcases hε with rfl | rfl
  · have hneg := gMatrix_append_singleton_apply_col_negPart B₀ w k i hrel
    rw [gMatrix_append_singleton_apply_col] at hneg
    have hcn (l : K) : (cMatrix B₀ w l k)⁻ = 0 := negPart_eq_zero.mpr (by simpa using hsign l)
    simp only [hcn, mul_zero, Finset.sum_const_zero, sub_zero, ← hBw] at hneg
    simpa only [neg_mul, one_mul, posPart_neg] using hneg
  · have hcp (l : K) : (cMatrix B₀ w l k)⁺ = 0 := posPart_eq_zero.mpr (by linarith [hsign l])
    simp [hcp, ← hBw]

/-- When `B₀ k k = 0`, the single-step principal `g`-matrix `gMatrix B₀ [k]` equals the
positive-sign left mutation factor `E₁(B₀, k)`. -/
theorem gMatrix_singleton {k : K} (hkk : B₀ k k = 0) :
    gMatrix B₀ [k] = matrixMutationLeft (Function.Embedding.refl K) B₀ k 1 := by
  simpa using gMatrix_append_singleton_eq_mul_matrixMutationLeft B₀ [] (by simpa using hkk)
    (by simp) (Or.inl rfl) fun i ↦ by by_cases h : i = k <;> simp [h]

/-- Along any word with column-sign-coherent `c`-vectors at each step, `cMatrix B₀ w` has
determinant `(-1) ^ w.length`. -/
theorem det_cMatrix_of_signCoherent
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (cMatrix B₀ w).det = (-1) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    obtain ⟨hcu, ε, hε, hsign⟩ := signCoherent_append_singleton hc
    rw [cMatrix_append_singleton_eq_mul_matrixMutationRight B₀ u hε hsign,
      det_mul, ih hcu, det_matrixMutationRight,
      List.length_append, List.length_singleton, pow_add, pow_one]

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
    obtain ⟨hdu, hkk⟩ := hdiag_append_singleton hdiag
    obtain ⟨hcu, ε, hε, hsign⟩ := signCoherent_append_singleton hc
    rw [gMatrix_append_singleton_eq_mul_matrixMutationLeft B₀ u hkk
        (gMatrix_mul_matrixMutationWord B₀ u hdu) hε hsign,
      det_mul, ih hdu hcu, det_matrixMutationLeft,
      List.length_append, List.length_singleton, pow_add, pow_one]

/-- Along any column-sign-coherent word, `cMatrix B₀ w` is unimodular over `ℤ`. -/
theorem isUnit_cMatrix_of_signCoherent
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (cMatrix B₀ w) := by
  rw [isUnit_iff_isUnit_det, det_cMatrix_of_signCoherent B₀ w hc]
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

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, no `g`-vector
vanishes. -/
theorem gVector_ne_zero_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (j : K) :
    gVector B₀ w j ≠ 0 := fun hz ↦
  pow_ne_zero w.length (by decide : (-1 : ℤ) ≠ 0) <|
    (det_gMatrix_of_signCoherent B₀ w hdiag hc).symm.trans
      (det_eq_zero_of_column_eq_zero j (congrFun hz))

/-- Along a column-sign-coherent word with vanishing mutable diagonal at each step, no row of
`gMatrix B₀ w` vanishes. -/
theorem gMatrix_row_ne_zero_of_signCoherent
    (hdiag : ∀ u k v, w = u ++ k :: v →
      matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (i : K) :
    gMatrix B₀ w i ≠ 0 := fun hz ↦
  pow_ne_zero w.length (by decide : (-1 : ℤ) ≠ 0) <|
    (det_gMatrix_of_signCoherent B₀ w hdiag hc).symm.trans
      (det_eq_zero_of_row_eq_zero i (congrFun hz))

end GMatrix

end TauCeti

namespace Matrix.IsSkewSymmetrizer

open TauCeti

variable {K : Type*} [DecidableEq K] [Fintype K] {B₀ : Matrix K K ℤ} {s : K → ℤ}

omit [Fintype K] in
private theorem hdiag (hs : B₀.IsSkewSymmetrizer s) (w : List K) :
    ∀ u k v, w = u ++ k :: v → matrixMutationWord (Function.Embedding.refl K) B₀ u k k = 0 :=
  fun u k _ _ ↦ (hs.matrixMutationWord u).apply_self k

/-- For a skew-symmetrizable initial matrix `B₀`, propagating `Sum.elim 1.col (-B₀.col)` on
`fromRows B₀ 1` along any word `w` produces `(gMatrix B₀ w).col` on mutable indices and `-B₀.col`
on frozen indices. -/
theorem degreeMutationWord_fromRows_one_elim_col (hs : B₀.IsSkewSymmetrizer s) (w : List K) :
    degreeMutationWord Function.Embedding.inl (fromRows B₀ 1)
        (Sum.elim (1 : Matrix K K ℤ).col (-B₀.col)) w =
      Sum.elim (gMatrix B₀ w).col (-B₀.col) :=
  TauCeti.degreeMutationWord_fromRows_one_elim_col B₀ w (hs.hdiag w)

/-- For a skew-symmetrizable initial matrix `B₀`, `gMatrix B₀ w * B_w = B₀ * cMatrix B₀ w` holds
for every mutation word `w`, without assuming sign-coherence. -/
theorem gMatrix_mul_matrixMutationWord (hs : B₀.IsSkewSymmetrizer s) (w : List K) :
    gMatrix B₀ w * matrixMutationWord (Function.Embedding.refl K) B₀ w = B₀ * cMatrix B₀ w :=
  TauCeti.gMatrix_mul_matrixMutationWord B₀ w (hs.hdiag w)

/-- Equal adjacent directions cancel in `gMatrix` for any skew-symmetrizable initial matrix. -/
theorem gMatrix_append_cons_cons_self (hs : B₀.IsSkewSymmetrizer s) (u v : List K) (k : K) :
    gMatrix B₀ (u ++ k :: k :: v) = gMatrix B₀ (u ++ v) :=
  TauCeti.gMatrix_append_cons_cons_self B₀ u v k ((hs.matrixMutationWord u).apply_self k)
    (hs.gMatrix_mul_matrixMutationWord u)

/-- Tropical duality `(gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s` along any
column-sign-coherent word from a matrix with skew-symmetrizer `s`. -/
theorem transpose_gMatrix_mul_diagonal_mul_cMatrix_of_signCoherent
    (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w)ᵀ * diagonal s * cMatrix B₀ w = diagonal s := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u k ih =>
    have hsu := hs.matrixMutationWord u
    obtain ⟨hcu, ε, hε, hsign⟩ := signCoherent_append_singleton hc
    rw [cMatrix_append_singleton_eq_mul_matrixMutationRight B₀ u hε hsign,
      gMatrix_append_singleton_eq_mul_matrixMutationLeft B₀ u (hsu.apply_self k)
        (hs.gMatrix_mul_matrixMutationWord u) hε hsign]
    set E := matrixMutationLeft (Function.Embedding.refl K)
      (matrixMutationWord (Function.Embedding.refl K) B₀ u) k ε
    set F := matrixMutationRight (Function.Embedding.refl K)
      (matrixMutationWord (Function.Embedding.refl K) B₀ u) k ε
    calc
      (gMatrix B₀ u * E)ᵀ * diagonal s * (cMatrix B₀ u * F)
        = Eᵀ * ((gMatrix B₀ u)ᵀ * diagonal s * cMatrix B₀ u) * F := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Eᵀ * diagonal s * F := by rw [ih hcu]
      _ = diagonal s := hsu.transpose_matrixMutationLeft_mul_diagonal_mul_matrixMutationRight k ε

/-- Transposed tropical duality `(cMatrix B₀ w)ᵀ * diagonal s * gMatrix B₀ w = diagonal s`
along any column-sign-coherent word from a matrix with skew-symmetrizer `s`. -/
theorem transpose_cMatrix_mul_diagonal_mul_gMatrix_of_signCoherent
    (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (cMatrix B₀ w)ᵀ * diagonal s * gMatrix B₀ w = diagonal s := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc] using
    congrArg Matrix.transpose (hs.transpose_gMatrix_mul_diagonal_mul_cMatrix_of_signCoherent w hc)

/-- For a skew-symmetric matrix (`s = 1`), `(gMatrix B₀ w)ᵀ` is the left inverse of `cMatrix B₀ w`
along any column-sign-coherent word. -/
theorem transpose_gMatrix_mul_cMatrix_of_signCoherent
    (hs : B₀.IsSkewSymmetrizer 1) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w)ᵀ * cMatrix B₀ w = 1 := by
  simpa using hs.transpose_gMatrix_mul_diagonal_mul_cMatrix_of_signCoherent w hc

/-- For a skew-symmetric matrix (`s = 1`), `cMatrix B₀ w * (gMatrix B₀ w)ᵀ = 1` along any
column-sign-coherent word. -/
theorem cMatrix_mul_transpose_gMatrix_of_signCoherent
    (hs : B₀.IsSkewSymmetrizer 1) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    cMatrix B₀ w * (gMatrix B₀ w)ᵀ = 1 :=
  mul_eq_one_comm.mp (hs.transpose_gMatrix_mul_cMatrix_of_signCoherent w hc)

/-- Determinant of `gMatrix` along any column-sign-coherent word for a skew-symmetrizable
matrix. -/
theorem det_gMatrix_of_signCoherent (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    (gMatrix B₀ w).det = (-1) ^ w.length :=
  TauCeti.det_gMatrix_of_signCoherent B₀ w (hs.hdiag w) hc

/-- Unimodularity of `gMatrix` over `ℤ` along any column-sign-coherent word for a
skew-symmetrizable matrix. -/
theorem isUnit_gMatrix_of_signCoherent (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) :
    IsUnit (gMatrix B₀ w) :=
  TauCeti.isUnit_gMatrix_of_signCoherent B₀ w (hs.hdiag w) hc

/-- Nonvanishing of `g`-vectors along any column-sign-coherent word for a skew-symmetrizable
matrix. -/
theorem gVector_ne_zero_of_signCoherent (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (j : K) :
    gVector B₀ w j ≠ 0 :=
  TauCeti.gVector_ne_zero_of_signCoherent B₀ w (hs.hdiag w) hc j

/-- Row nonvanishing of `gMatrix` along any column-sign-coherent word for a skew-symmetrizable
matrix. -/
theorem gMatrix_row_ne_zero_of_signCoherent (hs : B₀.IsSkewSymmetrizer s) (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B₀ u i k) ∨ ∀ i, cMatrix B₀ u i k ≤ 0) (i : K) :
    gMatrix B₀ w i ≠ 0 :=
  TauCeti.gMatrix_row_ne_zero_of_signCoherent B₀ w (hs.hdiag w) hc i

end Matrix.IsSkewSymmetrizer

namespace TauCeti

open Matrix

namespace ExchangeMatrix

variable {K : Type*} [DecidableEq K] [Fintype K] (B : ExchangeMatrix (Function.Embedding.refl K))

/-- Propagating `Sum.elim 1.col (-B.matrix.col)` on `B.principalExtension.matrix` along `w`
produces `(gMatrix B.matrix w).col` on mutable indices and `-B.matrix.col` on frozen indices. -/
theorem degreeMutationWord_principalExtension_elim_col (w : List K) :
    degreeMutationWord Function.Embedding.inl B.principalExtension.matrix
        (Sum.elim (1 : Matrix K K ℤ).col (-B.matrix.col)) w =
      Sum.elim (gMatrix B.matrix w).col (-B.matrix.col) := by
  rw [B.principalExtension_matrix]
  exact B.matrix_isSkewSymmetrizer.degreeMutationWord_fromRows_one_elim_col w

/-- Fundamental relation `gMatrix B.matrix w * (B.mutationWord w).matrix = B.matrix * cMatrix
B.matrix w` for a bundled square exchange matrix. -/
theorem gMatrix_mul_mutationWord_matrix (w : List K) :
    gMatrix B.matrix w * (B.mutationWord w).matrix = B.matrix * cMatrix B.matrix w := by
  rw [B.mutationWord_matrix]
  exact B.matrix_isSkewSymmetrizer.gMatrix_mul_matrixMutationWord w

/-- Equal adjacent directions cancel in `gMatrix` for a bundled square exchange matrix. -/
theorem gMatrix_append_cons_cons_self (u v : List K) (k : K) :
    gMatrix B.matrix (u ++ k :: k :: v) = gMatrix B.matrix (u ++ v) :=
  B.matrix_isSkewSymmetrizer.gMatrix_append_cons_cons_self u v k

/-- Tropical duality `(gMatrix B.matrix w)ᵀ * diagonal B.symmetrizer * cMatrix B.matrix w =
diagonal B.symmetrizer` along any column-sign-coherent word on a bundled square exchange matrix. -/
theorem transpose_gMatrix_mul_diagonal_mul_cMatrix_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) :
    (gMatrix B.matrix w)ᵀ * diagonal B.symmetrizer * cMatrix B.matrix w =
      diagonal B.symmetrizer :=
  B.matrix_isSkewSymmetrizer.transpose_gMatrix_mul_diagonal_mul_cMatrix_of_signCoherent w hc

/-- Transposed tropical duality `(cMatrix B.matrix w)ᵀ * diagonal B.symmetrizer * gMatrix
B.matrix w = diagonal B.symmetrizer` along any column-sign-coherent word on a bundled square
exchange matrix. -/
theorem transpose_cMatrix_mul_diagonal_mul_gMatrix_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) :
    (cMatrix B.matrix w)ᵀ * diagonal B.symmetrizer * gMatrix B.matrix w =
      diagonal B.symmetrizer :=
  B.matrix_isSkewSymmetrizer.transpose_cMatrix_mul_diagonal_mul_gMatrix_of_signCoherent w hc

/-- Determinant of `gMatrix B.matrix w` along any column-sign-coherent word on a bundled square
exchange matrix. -/
theorem det_gMatrix_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) :
    (gMatrix B.matrix w).det = (-1) ^ w.length :=
  B.matrix_isSkewSymmetrizer.det_gMatrix_of_signCoherent w hc

/-- Unimodularity of `gMatrix B.matrix w` over `ℤ` along any column-sign-coherent word on a bundled
square exchange matrix. -/
theorem isUnit_gMatrix_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) :
    IsUnit (gMatrix B.matrix w) :=
  B.matrix_isSkewSymmetrizer.isUnit_gMatrix_of_signCoherent w hc

/-- Nonvanishing of `g`-vectors along any column-sign-coherent word on a bundled square exchange
matrix. -/
theorem gVector_ne_zero_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) (j : K) :
    gVector B.matrix w j ≠ 0 :=
  B.matrix_isSkewSymmetrizer.gVector_ne_zero_of_signCoherent w hc j

/-- Row nonvanishing of `gMatrix B.matrix w` along any column-sign-coherent word on a bundled
square exchange matrix. -/
theorem gMatrix_row_ne_zero_of_signCoherent (w : List K)
    (hc : ∀ u k v, w = u ++ k :: v →
      (∀ i, 0 ≤ cMatrix B.matrix u i k) ∨ ∀ i, cMatrix B.matrix u i k ≤ 0) (i : K) :
    gMatrix B.matrix w i ≠ 0 :=
  B.matrix_isSkewSymmetrizer.gMatrix_row_ne_zero_of_signCoherent w hc i

end ExchangeMatrix

/-- In rank one with zero initial matrix, the first mutation sends both `cMatrix` and `gMatrix`
to `(-1)`. -/
example : cMatrix (0 : Matrix (Fin 1) (Fin 1) ℤ) [0] = !![-1] ∧
    gMatrix (0 : Matrix (Fin 1) (Fin 1) ℤ) [0] = !![-1] :=
  ⟨by ext i j; fin_cases i; fin_cases j; simp, by
    rw [gMatrix_singleton _ rfl]
    ext i j; fin_cases i; fin_cases j; simp [matrixMutationLeft_apply]⟩

/-- For the skew-symmetrizable matrix `((0, 1), (-2, 0))` with symmetrizer `(2, 1)`, mutating in
the first direction gives `C' = ((-1, 1), (0, 1))`, `G' = ((-1, 0), (2, 1))`, and
`G'ᵀ * diag(2, 1) * C' = diag(2, 1)`. -/
example : cMatrix !![0, 1; -2, 0] [0] = !![-1, 1; 0, 1] ∧
    gMatrix !![0, 1; -2, 0] [0] = !![-1, 0; 2, 1] ∧
    (gMatrix !![0, 1; -2, 0] [0])ᵀ * diagonal ![2, 1] * cMatrix !![0, 1; -2, 0] [0] =
      diagonal ![2, 1] := by
  have hc : cMatrix !![0, 1; -2, 0] [0] = !![-1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hg : gMatrix !![0, 1; -2, 0] [0] = !![-1, 0; 2, 1] := by
    rw [gMatrix_singleton _ rfl]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matrixMutationLeft_apply]
  exact ⟨hc, hg, by rw [hc, hg]; decide⟩

/-- Along the two-step type `A₂` word `[0, 1]` from `((0, 1), (-1, 0))`, one obtains
`C = ((0, -1), (1, -1))` (with negative second `c`-vector `![-1, -1]`),
`G = ((-1, -1), (1, 0))`, and `Gᵀ * C = 1`. -/
example : cMatrix !![0, 1; -1, 0] [0, 1] = !![0, -1; 1, -1] ∧
    gMatrix !![0, 1; -1, 0] [0, 1] = !![-1, -1; 1, 0] ∧
    (gMatrix !![0, 1; -1, 0] [0, 1])ᵀ * cMatrix !![0, 1; -1, 0] [0, 1] = 1 := by
  set B₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
  have h01 : ([0, 1] : List (Fin 2)) = [0] ++ [1] := rfl
  have hB₁ : matrixMutationWord (Function.Embedding.refl (Fin 2)) B₀ [0] = !![0, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B₀, matrixMutation_apply]
  have hc₁ : cMatrix B₀ [0] = !![-1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B₀]
  have hg₁ : gMatrix B₀ [0] = !![-1, 0; 1, 1] := by
    rw [gMatrix_singleton B₀ rfl]
    ext i j; fin_cases i <;> fin_cases j <;> simp [B₀, matrixMutationLeft_apply]
  have hc₂ : cMatrix B₀ ([0] ++ [1]) = !![0, -1; 1, -1] := by
    ext i j; rw [cMatrix_append_singleton_apply, hc₁, hB₁]; fin_cases i <;> fin_cases j <;> decide
  have hg₂ : gMatrix B₀ ([0] ++ [1]) = !![-1, -1; 1, 0] := by
    ext i j; by_cases hj : j = 1
    · subst j; rw [gMatrix_append_singleton_apply_col, hg₁, hc₁, hB₁]
      fin_cases i <;> simp [B₀, Fin.sum_univ_two]
    · rw [gMatrix_append_singleton_apply_of_ne B₀ [0] 1 i hj, hg₁]
      fin_cases i <;> fin_cases j <;> simp at hj ⊢
  rw [h01]
  exact ⟨hc₂, hg₂, by rw [hc₂, hg₂]; decide⟩

end TauCeti
