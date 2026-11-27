/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import TauCeti.Data.Matrix.Mul

/-!
# Block-triangular reduction over pre-valuation rings

Over a pre-valuation ring `A` (a commutative ring in which divisibility is total, including
valuation domains and their quotients such as `ℤ / p^n`), some `W : GL n A` clears a single entry
against a distinct pivot row while preserving rows outside that pair and columns where both rows
vanish. Iterating this clearing step along an embedding `ι : k ↪ n` in order of column weight
`wt : k → α` yields a decomposition `y = U_ι * D` with `U ∈ GL n A`, `D` block upper triangular
for `wt`, and `U⁻¹_ι * y = D`. The decomposition depends on the chosen weight and is noncanonical.
Transposing the row reduction gives a matrix `V ∈ GL n A` that clears all columns of `M * V`
outside `Set.range ι`.

## Main results

* `Matrix.exists_gl_mul_apply_eq_zero_of_preValuationRing`: some `W : GL n A` clears a single
  entry `(i, a)` using a distinct pivot row `i₀`.
* `Matrix.exists_gl_mul_eq_zero_on_of_preValuationRing`: clears an arbitrary finite set `t` of rows
  in column `a` against a pivot row `i₀ ∉ t`.
* `Matrix.exists_eq_submatrix_mul_blockTriangular_of_preValuationRing`: block-triangular
  decomposition `y = U.val.submatrix id ι * D` with `D.BlockTriangular wt` and
  `U⁻¹.val.submatrix ι id * y = D`.
* `Matrix.exists_mul_gl_apply_eq_zero_off_range_of_preValuationRing`: clears all columns of
  `M * V` outside `Set.range ι`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §1 (valuation rings and divisibility).
* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`,
  file `grh/src/Lib/General/LinearAlgebra/HermiteForm.lean`,
  `New.IsValuationPair.hermite` and `New.IsValuationPair.exists_mul_clear_cols`,
  Copyright 2026 Anthropic, PBC, Apache 2.0).
-/

public section

open Finset Matrix

namespace Matrix

section PreValuationRing

variable {A n k : Type*} [CommRing A] [PreValuationRing A] [Fintype n] [DecidableEq n]

/-- Over a pre-valuation ring, given distinct rows `i₀ ≠ i` of a matrix `y` and a column `a`, some
`W : GL n A` clears the entry `(i, a)` of `W * y`, leaves every row other than `i₀` and `i`
unchanged, and leaves every column where both rows `i₀` and `i` vanish unchanged. -/
theorem exists_gl_mul_apply_eq_zero_of_preValuationRing (y : Matrix n k A) {i₀ i : n}
    (hne : i₀ ≠ i) (a : k) :
    ∃ W : GL n A,
      (W.val * y) i a = 0 ∧
      (∀ (r : n) (j : k), r ≠ i₀ → r ≠ i → (W.val * y) r j = y r j) ∧
      ∀ (r : n) (j : k), y i₀ j = 0 → y i j = 0 → (W.val * y) r j = y r j := by
  obtain ⟨z, hz⟩ | ⟨x, hx⟩ := ValuationRing.dvd_total (y i₀ a) (y i a)
  · let W : GL n A := GeneralLinearGroup.transvection i i₀ hne.symm (-z)
    refine ⟨W, ?_, ?_, ?_⟩
    · simp [W, transvection_mul_apply_same, hz, mul_comm]
    · intro r j _ hri
      simp [W, transvection_mul_apply_of_ne _ _ _ _ hri]
    · intro r j hj₀ hji
      rcases eq_or_ne r i with rfl | hri
      · simp [W, transvection_mul_apply_same, hj₀, hji]
      · simp [W, transvection_mul_apply_of_ne _ _ _ _ hri]
  · let W : GL n A :=
      GeneralLinearGroup.transvection i i₀ hne.symm (-1) *
        GeneralLinearGroup.transvection i₀ i hne (1 - x)
    have hrow_i₀ (j : k) : (W.val * y) i₀ j = y i₀ j + (1 - x) * y i j := by
      simp [W, Matrix.mul_assoc, hne]
    have hrow_i (j : k) : (W.val * y) i j = y i j - (y i₀ j + (1 - x) * y i j) := by
      simp [W, Matrix.mul_assoc, hne.symm, sub_eq_add_neg]
    have hother (r : n) (j : k) (hr₀ : r ≠ i₀) (hr : r ≠ i) : (W.val * y) r j = y r j := by
      simp [W, Matrix.mul_assoc, hr₀, hr]
    refine ⟨W, ?_, hother, fun r j hj₀ hji ↦ ?_⟩
    · linear_combination hrow_i a - hx
    · rcases eq_or_ne r i with rfl | hri
      · simp [hrow_i, hj₀, hji]
      · rcases eq_or_ne r i₀ with rfl | hr₀
        · simp [hrow_i₀, hj₀, hji]
        · exact hother r j hr₀ hri

/-- Over a pre-valuation ring, for a matrix `y`, a column `a`, a pivot row `i₀`, and a finite set
`t` of rows with `i₀ ∉ t`, some `W : GL n A` clears column `a` in all rows of `t` and leaves every
column in which `i₀` and all rows of `t` vanish unchanged. -/
theorem exists_gl_mul_eq_zero_on_of_preValuationRing (y : Matrix n k A) (a : k) {i₀ : n}
    {t : Finset n} (hi₀ : i₀ ∉ t) :
    ∃ W : GL n A, (∀ i ∈ t, (W.val * y) i a = 0) ∧
      ∀ j : k, y i₀ j = 0 → (∀ i ∈ t, y i j = 0) → ∀ r : n, (W.val * y) r j = y r j := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i t hi ih =>
    obtain ⟨hne, hi₀⟩ : i₀ ≠ i ∧ i₀ ∉ t := by simpa using hi₀
    obtain ⟨W, W_zero, W_keep⟩ := ih hi₀
    obtain ⟨V, V_zero, V_other, V_keep⟩ :=
      (W.val * y).exists_gl_mul_apply_eq_zero_of_preValuationRing hne a
    refine ⟨V * W, fun r hr ↦ ?_, fun j hj₀ hjt r ↦ ?_⟩ <;>
      rw [Units.val_mul, Matrix.mul_assoc]
    · obtain rfl | hrt := mem_insert.1 hr
      · exact V_zero
      · rw [V_other r a (fun h ↦ hi₀ (h ▸ hrt)) (fun h ↦ hi (h ▸ hrt)), W_zero r hrt]
    · obtain ⟨hji, hjt⟩ : y i j = 0 ∧ ∀ r ∈ t, y r j = 0 := by simpa using hjt
      have W_col : ∀ r : n, (W.val * y) r j = y r j := W_keep j hj₀ hjt
      rw [V_keep r j ((W_col i₀).trans hj₀) ((W_col i).trans hji), W_col]

/-- A single row reduction makes the rows indexed by `ι` block upper triangular and clears
all rows outside the range of `ι`. -/
private theorem exists_gl_mul_blockTriangular_and_eq_zero_off_range_of_preValuationRing
    {α : Type*} [LinearOrder α] (y : Matrix n k A) (ι : k ↪ n) (wt : k → α) :
    ∃ U : GL n A, ((U.val * y).submatrix ι id).BlockTriangular wt ∧
      ∀ (i : n), i ∉ Set.range ι → ∀ j : k, (U.val * y) i j = 0 := by
  classical
  let _ : Fintype k := Fintype.ofInjective ι ι.injective
  -- Reduce columns in order of increasing weight so that in each reduced column `j ∈ s`,
  -- only rows `ι b` with `b ∈ s` and `wt b ≤ wt j` can be nonzero.
  let IsReduced (s : Finset k) (U : GL n A) : Prop :=
    ∀ j ∈ s, ∀ i : n, (∀ b ∈ s, i = ι b → wt j < wt b) → (U.val * y) i j = 0
  have exists_reduced (s : Finset k) : ∃ U : GL n A, IsReduced s U := by
    induction s using Finset.induction_on_max_value wt with
    | empty => exact ⟨1, by simp [IsReduced]⟩
    | insert a s ha hmax ih =>
      obtain ⟨U, hs⟩ := ih
      obtain ⟨W, hcol, hkeep⟩ :=
        (U.val * y).exists_gl_mul_eq_zero_on_of_preValuationRing a (i₀ := ι a)
          (t := ((insert a s).map ι)ᶜ) (by simp)
      have s_cols : ∀ j ∈ s, ∀ r : n, (W.val * (U.val * y)) r j = (U.val * y) r j := by
        intro j hj r
        refine hkeep j (hs j hj (ι a) fun b hb hba ↦ absurd (ι.injective hba.symm) (ha ∘ (· ▸ hb)))
          (fun i hi ↦ hs j hj i fun b hb hib ↦ ?_) r
        simp only [mem_compl, mem_map, mem_insert, not_exists, not_and] at hi
        exact absurd hib.symm (hi b (Or.inr hb))
      refine ⟨W * U, fun j hj r hr ↦ ?_⟩
      rw [Units.val_mul, Matrix.mul_assoc]
      obtain rfl | hjs := mem_insert.1 hj
      · refine hcol r ?_
        simp only [mem_compl, mem_map, mem_insert, not_exists, not_and]
        rintro b (rfl | hbs) hbr
        · exact (hr b (mem_insert_self b s) hbr.symm).false
        · exact (hmax b hbs).not_gt (hr b (mem_insert_of_mem hbs) hbr.symm)
      · refine (s_cols j hjs r).trans (hs j hjs r fun b hb hbr ↦ ?_)
        exact hr b (mem_insert_of_mem hb) hbr
  obtain ⟨U, hzero⟩ := exists_reduced univ
  refine ⟨U, ?_, fun i hi j ↦ hzero j (mem_univ j) i fun b _ h ↦ absurd ⟨b, h.symm⟩ hi⟩
  intro i j hij
  exact hzero j (mem_univ j) (ι i) fun b _ h ↦ by
    cases ι.injective h
    exact hij

/-- Given an embedding `ι : k ↪ n`, an `n × k` matrix `y` over a pre-valuation ring `A`,
and a column weight `wt : k → α` into a linear order `α`, there exist `U : GL n A` and
`D : Matrix k k A` such that `D` is block upper triangular for `wt`,
`y = U.val.submatrix id ι * D`, and `U⁻¹.val.submatrix ι id * y = D`. -/
theorem exists_eq_submatrix_mul_blockTriangular_of_preValuationRing
    [Fintype k] {α : Type*} [LinearOrder α] (y : Matrix n k A) (ι : k ↪ n) (wt : k → α) :
    ∃ (U : GL n A) (D : Matrix k k A),
      D.BlockTriangular wt ∧
      y = U.val.submatrix id ι * D ∧
      U⁻¹.val.submatrix ι id * y = D := by
  obtain ⟨U, htri, hrows⟩ :=
    y.exists_gl_mul_blockTriangular_and_eq_zero_off_range_of_preValuationRing ι wt
  refine ⟨U⁻¹, (U.val * y).submatrix ι id, htri, ?_, ?_⟩
  · calc
      y = (U⁻¹.val * (U.val * y)).submatrix id id := by simp [← Matrix.mul_assoc]
      _ = U⁻¹.val.submatrix id ι * (U.val * y).submatrix ι id :=
        submatrix_mul_of_injective_right U⁻¹.val (U.val * y) id ι id ι.injective
          fun i j hij ↦ by_contra fun hi ↦ hij (hrows i hi j)
  · ext i j
    simp [Matrix.mul_apply]

/-- For a `k × n` matrix `M` over a pre-valuation ring `A` and an embedding `ι : k ↪ n`,
some `V : GL n A` clears all columns of `M * V` outside `Set.range ι`. -/
theorem exists_mul_gl_apply_eq_zero_off_range_of_preValuationRing (M : Matrix k n A) (ι : k ↪ n) :
    ∃ V : GL n A, ∀ (a : k) (j : n), j ∉ Set.range ι → (M * V.val) a j = 0 := by
  obtain ⟨U, -, hrows⟩ :=
    Mᵀ.exists_gl_mul_blockTriangular_and_eq_zero_off_range_of_preValuationRing ι (fun _ ↦ ())
  let V : GL n A := (GeneralLinearGroup.transposeMulEquiv n U).unop
  refine ⟨V, fun a j hj ↦ ?_⟩
  have hV : V.val = U.valᵀ := GeneralLinearGroup.coe_unop_transposeMulEquiv n U
  rw [← transpose_apply (M * V.val), Matrix.transpose_mul, hV, transpose_transpose]
  exact hrows j hj a

end PreValuationRing

end Matrix
