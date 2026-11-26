/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hermite normal form over valuation domains and valued-field matrix integrality

Over a valuation domain `A`, any two elements are comparable by divisibility
(`ValuationRing.dvd_total`). Consequently, elementary row transvections in `GL n A` can clear any
single entry of a column against a pivot row without altering rows outside that pair or columns
where both rows vanish. Iterating this clearing step along an embedding `ι : k ↪ n` ordered by a
column weight `wt : k → ℕ` yields a rectangular Hermite factorization `y = U_ι * D` with
`U ∈ GL n A`, `D` block upper triangular for `wt`, and `U⁻¹_ι * y = D`. Transposing gives a
column-clearing matrix `V ∈ GL n A` killing all columns of `M * V` outside `Set.range ι`.

We also record two companion facts for matrices over valued rings and fields: an entrywise
valuation bound for matrix products (`Matrix.valuation_mul_le`) and the determinant criterion for
an invertible matrix over a valued field `F` to lie in the image of `GL n v.valuationSubring`
(`Matrix.GeneralLinearGroup.mem_range_map_valuationSubring_iff`).

## Main results

* `Matrix.exists_gl_mul_apply_eq_zero`: over a valuation domain, a product of elementary row
  transvections clears a single entry `(i, a)` using a distinct pivot row `i₀`.
* `Matrix.exists_gl_mul_eq_zero_on`: clears an arbitrary finite set `t` of rows in column `a`
  against a pivot row `i₀ ∉ t`.
* `Matrix.exists_hermite_factorization_of_valuationRing`: rectangular Hermite factorization
  `y = U.val.submatrix id ι * D` with `D.BlockTriangular wt` and `U⁻¹.val.submatrix ι id * y = D`.
* `Matrix.exists_mul_gl_eq_zero_of_notMem_range`: transposed form clearing the columns of `M * V`
  outside `Set.range ι`.
* `Matrix.valuation_mul_le`: entrywise valuation bound `v ((A * B) a b) ≤ c * d`.
* `Matrix.GeneralLinearGroup.mem_range_map_valuationSubring_iff`: `g : GL n F` lies in the image
  of `GL n v.valuationSubring` if and only if all entries have valuation at most `1` and
  `v g.val.det = 1`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §1 (valuation rings and divisibility).
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  `New.IsValuationPair.hermite`, `New.IsValuationPair.exists_mul_clear_cols`, `New.v_matrix_mul_le`,
  and `New.mem_intGL_iff_det` in `src/Lib/General/LinearAlgebra/HermiteForm.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open Finset Matrix ValuationRing

namespace Matrix

section ValuationDomain

variable {A n k : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [Fintype n] [DecidableEq n]

/-- Over a valuation domain, given distinct rows `i₀ ≠ i` of a matrix `y` and a column `a`, some
`W : GL n A` clears the entry `(i, a)` of `W * y`, leaves every row other than `i₀` and `i`
unchanged, and leaves every column where both rows `i₀` and `i` vanish unchanged. -/
theorem exists_gl_mul_apply_eq_zero (y : Matrix n k A) {i₀ i : n} (hne : i₀ ≠ i) (a : k) :
    ∃ W : GL n A,
      (W.val * y) i a = 0 ∧
      (∀ (r : n) (j : k), r ≠ i₀ → r ≠ i → (W.val * y) r j = y r j) ∧
      ∀ (r : n) (j : k), y i₀ j = 0 → y i j = 0 → (W.val * y) r j = y r j := by
  obtain ⟨z, hz⟩ | ⟨x, hx⟩ := dvd_total (y i₀ a) (y i a)
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

/-- Over a valuation domain, for a matrix `y`, a column `a`, a pivot row `i₀`, and a finite set
`t` of rows with `i₀ ∉ t`, some `W : GL n A` clears column `a` in all rows of `t` and leaves every
column in which `i₀` and all rows of `t` vanish unchanged. -/
theorem exists_gl_mul_eq_zero_on (y : Matrix n k A) (a : k) {i₀ : n} {t : Finset n} (hi₀ : i₀ ∉ t) :
    ∃ W : GL n A, (∀ i ∈ t, (W.val * y) i a = 0) ∧
      ∀ j : k, y i₀ j = 0 → (∀ i ∈ t, y i j = 0) → ∀ r : n, (W.val * y) r j = y r j := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i t hi ih =>
    obtain ⟨hne, hi₀⟩ : i₀ ≠ i ∧ i₀ ∉ t := by simpa using hi₀
    obtain ⟨W, W_zero, W_keep⟩ := ih hi₀
    obtain ⟨V, V_zero, V_other, V_keep⟩ := (W.val * y).exists_gl_mul_apply_eq_zero hne a
    refine ⟨V * W, fun r hr ↦ ?_, fun j hj₀ hjt r ↦ ?_⟩ <;>
      rw [Units.val_mul, Matrix.mul_assoc]
    · obtain rfl | hrt := mem_insert.1 hr
      · exact V_zero
      · rw [V_other r a (fun h ↦ hi₀ (h ▸ hrt)) (fun h ↦ hi (h ▸ hrt)), W_zero r hrt]
    · obtain ⟨hji, hjt⟩ : y i j = 0 ∧ ∀ r ∈ t, y r j = 0 := by simpa using hjt
      have W_col : ∀ r : n, (W.val * y) r j = y r j := W_keep j hj₀ hjt
      rw [V_keep r j ((W_col i₀).trans hj₀) ((W_col i).trans hji), W_col]

/-- **Rectangular Hermite factorization over a valuation domain.** Given an embedding `ι : k ↪ n`,
an `n × k` matrix `y` over a valuation domain `A`, and a column weight `wt : k → ℕ`, there exist
`U : GL n A` and `D : Matrix k k A` such that `D` is block upper triangular for `wt`,
`y = U.val.submatrix id ι * D`, and `U⁻¹.val.submatrix ι id * y = D`. -/
theorem exists_hermite_factorization_of_valuationRing [Fintype k] (y : Matrix n k A) (ι : k ↪ n)
    (wt : k → ℕ := 0) :
    ∃ (U : GL n A) (D : Matrix k k A),
      D.BlockTriangular wt ∧
      y = U.val.submatrix id ι * D ∧
      U⁻¹.val.submatrix ι id * y = D := by
  classical
  -- Reduce columns in order of increasing weight so that in each reduced column `j ∈ s`,
  -- only rows `ι b` with `b ∈ s` and `wt b ≤ wt j` can be nonzero.
  let IsReduced (s : Finset k) (U : GL n A) : Prop :=
    ∀ j ∈ s, ∀ i : n, (∀ b ∈ s, i = ι b → wt j < wt b) → (U.val * y) i j = 0
  have exists_reduced (s : Finset k) : ∃ U : GL n A, IsReduced s U := by
    induction s using Finset.induction_on_max_value wt with
    | empty => exact ⟨1, by simp [IsReduced]⟩
    | insert a s ha hmax ih =>
      obtain ⟨U, hs⟩ := ih
      obtain ⟨W, hcol, hkeep⟩ := (U.val * y).exists_gl_mul_eq_zero_on a (i₀ := ι a)
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
  refine ⟨U⁻¹, (U.val * y).submatrix ι id,
    fun i j hij ↦ hzero j (mem_univ j) (ι i) fun b _ h ↦ by cases ι.injective h; exact hij, ?_, ?_⟩
  · have hrows (i : n) (hi : i ∉ Set.range ι) (j : k) : (U.val * y) i j = 0 :=
      hzero j (mem_univ j) i fun b _ h ↦ absurd ⟨b, h.symm⟩ hi
    calc
      y = U⁻¹.val * (U.val * y) := by simp [← Matrix.mul_assoc]
      _ = U⁻¹.val.submatrix id ι * (U.val * y).submatrix ι id := ext fun i j ↦
        (Fintype.sum_of_injective ι ι.injective _ _ (by simp +contextual [hrows]) fun _ ↦ rfl).symm
  · ext i j
    simp [Matrix.mul_apply]

/-- **Transposed Hermite reduction over a valuation domain.** For a `k × n` matrix `M` over a
valuation domain `A` and an embedding `ι : k ↪ n`, some `V : GL n A` clears all columns of `M * V`
outside `Set.range ι`. -/
theorem exists_mul_gl_eq_zero_of_notMem_range (M : Matrix k n A) (ι : k ↪ n) :
    ∃ V : GL n A, ∀ (a : k) (j : n), j ∉ Set.range ι → (M * V.val) a j = 0 := by
  let _ : Fintype k := Fintype.ofInjective ι ι.injective
  obtain ⟨U, D, -, h_form, -⟩ := Mᵀ.exists_hermite_factorization_of_valuationRing ι
  have h_rows : U⁻¹.val * Mᵀ = (1 : Matrix n n A).submatrix id ι * D := by
    rw [h_form, ← Matrix.mul_assoc]
    congr 1
    ext i j
    have hmul : (U⁻¹.val * U.val) i (ι j) = (1 : Matrix n n A) i (ι j) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_apply, submatrix_apply, id_eq] at hmul ⊢
    exact hmul
  let V : GL n A :=
    ⟨U⁻¹.valᵀ, U.valᵀ,
      by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel]; simp,
      by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel]; simp⟩
  refine ⟨V, fun a j hj ↦ ?_⟩
  have h_entry : ((1 : Matrix n n A).submatrix id ι * D) j a = 0 := by
    simp only [Matrix.mul_apply, submatrix_apply, id_eq, Matrix.one_apply]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    simp [show j ≠ ι b from fun h ↦ hj ⟨b, h.symm⟩]
  have hMV : (M * V.val) a j = (U⁻¹.val * Mᵀ) j a := by
    simpa [V] using congrFun₂ (Matrix.transpose_mul M V.val) j a
  exact hMV.trans ((congrFun₂ h_rows j a).trans h_entry)

end ValuationDomain

section ValuedMatrix

/-- Entrywise valuation bound for matrix products: if every entry of `A` has valuation at most `c`
and every entry of `B` has valuation at most `d`, then every entry of `A * B` has valuation at most
`c * d`. -/
theorem valuation_mul_le {R Γ₀ m n l : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    [Fintype n] (v : Valuation R Γ₀) {A : Matrix m n R} {B : Matrix n l R} {c d : Γ₀}
    (hA : ∀ (a : m) (b : n), v (A a b) ≤ c) (hB : ∀ (a : n) (b : l), v (B a b) ≤ d)
    (a : m) (b : l) :
    v ((A * B) a b) ≤ c * d :=
  v.map_sum_le fun i _ ↦ (map_mul v _ _).trans_le (mul_le_mul' (hA a i) (hB i b))

/-- **Determinant criterion for integral invertible matrices over a valued field.** An invertible
matrix `g : GL n F` lies in the image of `GL n v.valuationSubring` if and only if all of its
entries have valuation at most `1` and `v g.val.det = 1`. -/
theorem GeneralLinearGroup.mem_range_map_valuationSubring_iff {F Γ₀ n : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Fintype n] [DecidableEq n]
    (v : Valuation F Γ₀) (g : GL n F) :
    g ∈ (GeneralLinearGroup.map v.valuationSubring.subtype).range ↔
      (∀ a b : n, v (g.val a b) ≤ 1) ∧ v g.val.det = 1 := by
  have unit_iff (A : Matrix n n v.valuationSubring) :
      IsUnit A.det ↔ v (v.valuationSubring.subtype.mapMatrix A).det = 1 := by
    rw [← v.valuationSubring.subtype.map_det]
    exact (Valuation.integer.integers v).isUnit_iff_valuation_eq_one
  refine ⟨?_, fun ⟨h_int, h_det⟩ ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact ⟨fun a b ↦ (u.val a b).prop,
      (unit_iff u.val).1 ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)⟩
  · let A : Matrix n n v.valuationSubring := fun a b ↦ ⟨g.val a b, h_int a b⟩
    refine ⟨GeneralLinearGroup.mk'' A ((unit_iff A).2 h_det), ?_⟩
    ext a b
    rfl

end ValuedMatrix

end Matrix
