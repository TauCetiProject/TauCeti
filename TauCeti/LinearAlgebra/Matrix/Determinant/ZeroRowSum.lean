/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Deleting a column of a matrix whose rows sum to zero

Let `M` be a matrix with rows indexed by `ι` and columns indexed by `κ`, where `κ` has one element
more than `ι`, and suppose every row of `M` sums to zero. Deleting any column `j` of `M` and
ordering the remaining columns by an equivalence `ι ≃ {j' // j' ≠ j}` gives a square matrix. Its
determinant is the same for every choice of `j` and of the equivalence, up to sign.

This is the linear algebra behind the independence of a regulator from the place left out of the
logarithmic embedding: the product formula says exactly that the rows of the full matrix of
weighted logarithms sum to zero. Mathlib's
`Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'` is the case
`κ = Fin (n + 1)`, `ι = Fin n`, with the columns ordered by `Fin.succAbove`; here the index types
are arbitrary.

## Main results

* `Matrix.exists_det_submatrix_eq_units_smul_of_injective`: choosing the columns along any injective
  map avoiding a column `j`, instead of along an equivalence `ι ≃ {j' // j' ≠ j}`, changes the
  determinant only by a sign. This holds for any matrix.
* `Matrix.exists_det_submatrix_eq_units_smul_of_sum_eq_zero`: the two determinants agree up to a
  sign `s : ℤˣ`.
* `Matrix.abs_det_submatrix_eq_of_sum_eq_zero`: over a commutative ring with a linear order, such
  as `ℝ`, they have the same absolute value.
-/

public section

open Equiv

namespace Matrix

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing R]

omit [Fintype κ] in
/-- Choosing the columns of `M` along an injective map `g : ι → κ` that avoids `j` gives the same
determinant, up to sign, as choosing them along an equivalence `ι ≃ {j' // j' ≠ j}`. -/
theorem exists_det_submatrix_eq_units_smul_of_injective (M : Matrix ι κ R) {j : κ}
    (e : ι ≃ {j' // j' ≠ j}) {g : ι → κ} (hg : Function.Injective g) (hgj : ∀ k, g k ≠ j) :
    ∃ s : ℤˣ, (M.submatrix id g).det = s • (M.submatrix id fun k ↦ (e k : κ)).det := by
  set σ : ι → ι := fun k ↦ e.symm ⟨g k, hgj k⟩
  have hσ : Function.Injective σ := fun a b h ↦
    hg (congrArg Subtype.val (e.symm.injective h))
  refine ⟨Perm.sign (Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)), ?_⟩
  rw [Units.smul_def, zsmul_eq_mul, ← det_permute', submatrix_submatrix]
  congr 2
  ext k
  simp [σ]

/-- **Deleting a column of a matrix whose rows sum to zero.** If every row of `M` sums to zero,
then deleting the column `j₁` or the column `j₂`, and ordering the remaining columns by any
equivalences `e₁` and `e₂`, gives square matrices whose determinants agree up to a sign. -/
theorem exists_det_submatrix_eq_units_smul_of_sum_eq_zero (M : Matrix ι κ R)
    (hM : ∀ i, ∑ j, M i j = 0) {j₁ j₂ : κ} (e₁ : ι ≃ {j // j ≠ j₁}) (e₂ : ι ≃ {j // j ≠ j₂}) :
    ∃ s : ℤˣ, (M.submatrix id fun k ↦ (e₁ k : κ)).det =
      s • (M.submatrix id fun k ↦ (e₂ k : κ)).det := by
  classical
  have he₁ : Function.Injective fun k ↦ (e₁ k : κ) :=
    Subtype.val_injective.comp e₁.injective
  by_cases h : j₁ = j₂
  · subst h
    exact exists_det_submatrix_eq_units_smul_of_injective M e₂ he₁ fun k ↦ (e₁ k).2
  -- Replace the column `j₂` by `-M · j₁`, the sum of the other columns, without changing the
  -- determinant up to sign. The result chooses its columns along `g`, which avoids `j₂`.
  set k₀ := e₁.symm ⟨j₂, Ne.symm h⟩
  set g : ι → κ := Function.update (fun k ↦ (e₁ k : κ)) k₀ j₁
  have hne {k : ι} (hk : k ≠ k₀) : (e₁ k : κ) ≠ j₂ := fun h' ↦
    hk (e₁.symm_apply_eq.mpr (Subtype.ext h'.symm)).symm
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a = k₀ <;> by_cases hb : b = k₀
    · rw [ha, hb]
    · simp only [g, ha, hb, Function.update_self, ne_eq, not_false_eq_true,
        Function.update_of_ne] at hab
      exact absurd hab.symm (e₁ b).2
    · simp only [g, ha, hb, Function.update_self, ne_eq, not_false_eq_true,
        Function.update_of_ne] at hab
      exact absurd hab (e₁ a).2
    · exact he₁ (by simpa [g, ha, hb] using hab)
  have hgj (k : ι) : g k ≠ j₂ := by
    by_cases hk : k = k₀
    · simpa [g, hk] using h
    · simpa [g, hk] using hne hk
  obtain ⟨s, hs⟩ := exists_det_submatrix_eq_units_smul_of_injective M e₂ hg hgj
  refine ⟨-s, ?_⟩
  have hsum (i : ι) : ∑ k, M i (e₁ k) = -M i j₁ := by
    rw [e₁.sum_comp (fun j ↦ M i j), eq_neg_iff_add_eq_zero, add_comm,
      ← Fintype.sum_eq_add_sum_subtype_ne, hM]
  have hcol : (M.submatrix id fun k ↦ (e₁ k : κ)).updateCol k₀
        (fun i ↦ ∑ k, (1 : R) • (M.submatrix id fun k ↦ (e₁ k : κ)) i k) =
      (M.submatrix id g).updateCol k₀ ((-1 : R) • fun i ↦ M.submatrix id g i k₀) := by
    ext i k
    by_cases hk : k = k₀
    · subst hk
      simp [g, hsum]
    · simp [g, hk]
  have hdet := congrArg det hcol
  rw [det_updateCol_sum, det_updateCol_smul, updateCol_eq_self, one_smul] at hdet
  rw [hdet, hs, Units.neg_smul, neg_one_mul]

/-- **Deleting a column of a matrix whose rows sum to zero**, over a commutative ring with a linear
order such as `ℝ`: the square matrices obtained by deleting any column and ordering the remaining
columns arbitrarily all have determinants of the same absolute value. -/
theorem abs_det_submatrix_eq_of_sum_eq_zero {R : Type*} [CommRing R] [LinearOrder R]
    (M : Matrix ι κ R) (hM : ∀ i, ∑ j, M i j = 0) {j₁ j₂ : κ} (e₁ : ι ≃ {j // j ≠ j₁})
    (e₂ : ι ≃ {j // j ≠ j₂}) :
    |(M.submatrix id fun k ↦ (e₁ k : κ)).det| = |(M.submatrix id fun k ↦ (e₂ k : κ)).det| := by
  obtain ⟨s, hs⟩ := exists_det_submatrix_eq_units_smul_of_sum_eq_zero M hM e₁ e₂
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [hs]

end Matrix
