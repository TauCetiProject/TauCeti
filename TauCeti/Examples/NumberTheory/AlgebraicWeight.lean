/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.AlgebraicWeight.Embedding

/-!
# Checks for embedding-indexed weights and their Hodge–Tate numbers

These examples exercise the dominant-weight coordinates of `GL n` over a number field, the
conjugation condition `(ℤⁿ)_w`, the Hodge–Tate multiset and extreme regularity.

* Over `ℚ` in rank two, the weight `(k - 2, 0)` of a classical eigenform of weight `k ≥ 2` is
  dominant, lies in `(ℤ²)_{k-2}` and has Hodge–Tate numbers `{k - 1, 0}`; for `k = 12` these are
  `{11, 0}`.
* For two conjugate embeddings, the weights `(1, 0)` and `(0, 0)` lie in no `(ℤ²)_w`, and
  `(0, 1)` is not dominant.
* The zero weight has the distinct Hodge–Tate numbers `{0, …, n - 1}`, although its unshifted
  entries repeat.
* `(5, 2, 1, 1)` is extremely regular: its shifted entries `(8, 4, 2, 1)` have distinct subset
  sums.  `(0, 0, 0, 0)` is not: its shifted entries `(3, 2, 1, 0)` have `3 + 0 = 2 + 1`.
* With no embeddings nothing is extremely regular, even in rank zero.
-/

public section

open TauCeti TauCeti.EmbeddingWeight

namespace TauCeti.Examples.NumberTheory.AlgebraicWeight

/-! ### Classical eigenforms -/

/-- The weight `(k - 2, 0)`, at every embedding, for an integer `k ≥ 2`. -/
abbrev eigenformWeight (ι : Type*) (k : ℤ) (hk : 2 ≤ k) : EmbeddingWeight ι 2 :=
  ofAntitone (fun _ => ![k - 2, 0]) fun _ => by
    rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i
    simp
    omega

/-- The eigenform weight `(k - 2, 0)` lies in `(ℤ²)_{k-2}`, for any index map. -/
example (ι : Type*) (c : ι → ι) (k : ℤ) (hk : 2 ≤ k) :
    (eigenformWeight ι k hk).IsConjDual c (k - 2) := by
  rw [isConjDual_iff]
  intro τ i
  fin_cases i <;> simp

/-- The eigenform weight `(k - 2, 0)` has Hodge–Tate numbers `{k - 1, 0}`. -/
example (ι : Type*) (k : ℤ) (hk : 2 ≤ k) (τ : ι) :
    (eigenformWeight ι k hk τ).hodgeMultiset = {k - 1, 0} := by
  rw [DominantWeight.hodgeMultiset_fin_two]
  simp only [ofAntitone_apply_coe]
  congr 1
  simp only [Matrix.cons_val_zero]
  ring

/-- For `k = 12` the Hodge–Tate numbers are `{11, 0}`. -/
example (ι : Type*) (τ : ι) : (eigenformWeight ι 12 (by norm_num) τ).hodgeMultiset = {11, 0} := by
  rw [DominantWeight.hodgeMultiset_fin_two]
  norm_num

/-! ### The conjugation condition -/

/-- Over an imaginary quadratic field, with embeddings `τ` (`true`) and `c τ` (`false`), the
weights `a_τ = (1, 0)` and `a_{c τ} = (0, 0)` give `a_{τ,1} + a_{c τ,2} = 1` but
`a_{τ,2} + a_{c τ,1} = 0`, so they lie in no `(ℤ²)_w`. -/
example (w : ℤ) :
    ¬ (ofAntitone (n := 2) (fun b => if b then ![1, 0] else ![0, 0]) fun b => by
        cases b <;> (rw [Fin.antitone_iff_succ_le]; intro i; fin_cases i; simp)).IsConjDual
      not w := by
  rw [isConjDual_iff]
  intro h
  have h₀ := h true 0
  have h₁ := h true 1
  simp at h₀ h₁
  omega

/-- `(0, 1)` is not dominant: the coordinates of a dominant weight weakly decrease. -/
example : ¬ Antitone ![(0 : ℤ), 1] := fun h => by
  simpa using h (Fin.zero_le (1 : Fin 2))

/-- In rank one the conjugation condition reads `a_τ + a_{c τ} = w`. -/
example (ι : Type*) (a : EmbeddingWeight ι 1) (c : ι → ι) (w : ℤ) :
    a.IsConjDual c w ↔ ∀ τ, (a τ).val 0 + (a (c τ)).val 0 = w :=
  isConjDual_iff_of_rank_one a c w

/-! ### Hodge–Tate numbers -/

/-- The zero weight of `GL 4` has Hodge–Tate numbers `{0, 1, 2, 3}`. -/
example : (0 : DominantWeight 4).hodgeMultiset = {0, 1, 2, 3} := by
  rw [DominantWeight.hodgeMultiset_zero]
  decide

/-- The unshifted entries of the zero weight of `GL 2` repeat, so the shift by `n - 1 - i` is
needed for distinct Hodge–Tate numbers. -/
example : ¬ ((Finset.univ : Finset (Fin 2)).val.map (0 : DominantWeight 2).val).Nodup := by
  simp

/-! ### Extreme regularity -/

/-- The dominant weight `(5, 2, 1, 1)` of `GL 4`. -/
abbrev weight5211 : DominantWeight 4 :=
  ⟨![5, 2, 1, 1], by
    rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp⟩

/-- `(5, 2, 1, 1)` shifts to `(8, 4, 2, 1)`, whose subset sums are all distinct, so it is
extremely regular. -/
example : weight5211.IsExtremelyRegular := by
  rw [DominantWeight.isExtremelyRegular_iff]
  simp only [DominantWeight.hodgeShift_apply]
  decide

/-- The zero weight of `GL 4` shifts to `(3, 2, 1, 0)`, and `3 + 0 = 2 + 1`, so it is not
extremely regular although its Hodge–Tate numbers are distinct. -/
example : ¬ (0 : DominantWeight 4).IsExtremelyRegular := fun h => by
  have := (DominantWeight.isExtremelyRegular_iff _).1 h {0, 3} {1, 2} rfl
    (by simp [DominantWeight.hodgeShift_apply])
  simpa using Finset.ext_iff.1 this 0

/-- In rank one, a weight with a nonempty index is extremely regular. -/
example (ι : Type*) [Nonempty ι] (a : EmbeddingWeight ι 1) : a.IsExtremelyRegular :=
  isExtremelyRegular_of_rank_one a

/-- With no embeddings, even a rank-zero weight is not extremely regular. -/
example (a : EmbeddingWeight Empty 0) : ¬ a.IsExtremelyRegular :=
  not_isExtremelyRegular_of_isEmpty a

end TauCeti.Examples.NumberTheory.AlgebraicWeight
