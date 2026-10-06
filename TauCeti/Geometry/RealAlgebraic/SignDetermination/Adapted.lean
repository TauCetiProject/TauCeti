/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Adapted sign matrices

Any distinct collection of sign columns of the full ternary moment matrix is linearly
independent. Selecting a basis of its rows gives a square invertible matrix, with exactly
one query per candidate sign condition. Its inverse recovers the counts from the selected
polynomial sign sums, provided the candidate columns cover the sample points.

In particular, the realized sign conditions admit such an adapted matrix without any
coverage or invertibility assumption. Empty sample sets and empty query tuples are included.
The root specialization counts distinct roots, including repeated roots; for the zero
polynomial it uses the empty root multiset, rather than its infinite zero set.

## References

C. Cordwell, Y. K. Tan, A. Platzer,
[*A Verified Decision Procedure for Univariate Real Arithmetic with the BKR Algorithm*]
(https://doi.org/10.4230/LIPIcs.ITP.2021.14), ITP 2021, for adapted sign matrices.
S. Basu, R. Pollack, M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, second edition]
(https://doi.org/10.1007/3-540-33099-2), Chapter 10.
-/

public section

open scoped Matrix
open Module

namespace TauCeti.SignDetermination

variable {J C : Type*} [Fintype J] [Fintype C]

omit [Fintype C] in
/-- Restricting the full sign matrix to distinct candidate columns preserves linear
independence, irrespective of whether those sign conditions are realized. -/
theorem linearIndependent_fullMatrix_columns (columns : C → J → SignType)
    (hinj : Function.Injective columns) :
    LinearIndependent ℚ ((fullMatrix J).submatrix id columns).col := by
  classical
  have hfull : LinearIndependent ℚ (fullMatrix J).col := by
    apply Matrix.mulVec_injective_iff.mp
    intro v w h
    have he := congrArg (fun u => fullInverse J *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec, fullInverse_mul_fullMatrix, Matrix.one_mulVec] using he
  exact hfull.comp columns hinj

/-- The matrix of all ternary queries on distinct candidate sign columns has full
column rank. -/
theorem rank_fullMatrix_columns (columns : C → J → SignType)
    (hinj : Function.Injective columns) :
    ((fullMatrix J).submatrix id columns).rank = Fintype.card C := by
  classical
  rw [← Matrix.rank_transpose]
  exact (linearIndependent_fullMatrix_columns columns hinj).rank_matrix

/-- There are as many independent ternary query rows as distinct candidate sign columns.
The resulting square adapted matrix is invertible, also for an empty column set. -/
theorem exists_isUnit_fullMatrix_submatrix [DecidableEq C] (columns : C → J → SignType)
    (hinj : Function.Injective columns) :
    ∃ rows : C ↪ (J → Fin 3), IsUnit ((fullMatrix J).submatrix rows columns) := by
  classical
  let M := (fullMatrix J).submatrix id columns
  -- A maximal independent row family spans all rows of the restricted matrix.
  obtain ⟨s, -, -, hspan, hli⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℚ M.row) (Set.empty_subset Set.univ)
  let N := M.submatrix (Subtype.val : s → (J → Fin 3)) id
  have hrow : N.row = M.row ∘ Subtype.val := rfl
  have hliN : LinearIndependent ℚ N.row := hli
  have hspanN : Submodule.span ℚ (Set.range N.row) =
      Submodule.span ℚ (Set.range M.row) := by
    rw [hrow, Set.range_comp, Subtype.range_coe_subtype]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range M.row s)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hspan ⟨i, Set.mem_univ i, rfl⟩
  -- Full column rank makes this row family the same size as the candidate columns.
  have hcard : Fintype.card s = Fintype.card C := by
    rw [← hliN.rank_matrix, Matrix.rank_eq_finrank_span_row, hspanN,
      ← Matrix.rank_eq_finrank_span_row]
    exact rank_fullMatrix_columns columns hinj
  let e : C ≃ s := Fintype.equivOfCardEq hcard.symm
  refine ⟨⟨Subtype.val ∘ e, Subtype.val_injective.comp e.injective⟩, ?_⟩
  exact Matrix.linearIndependent_rows_iff_isUnit.mp (hliN.comp e e.injective)

end TauCeti.SignDetermination

namespace Finset

open Polynomial TauCeti.SignDetermination

variable {R J C : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype J] [Fintype C] [DecidableEq C]

/-- Inverting an adapted square sign matrix recovers all candidate counts from its
selected sign sums. Distinct candidate columns must cover every sample point. -/
theorem inv_fullMatrix_submatrix_mulVec_signSum (Z : Finset R) (Q : J → R[X])
    (columns : C → J → SignType) (rows : C → J → Fin 3)
    (hinj : Function.Injective columns)
    (cover : ∀ x ∈ Z, ∃ c, columns c = fun j => SignType.sign ((Q j).eval x))
    (hunit : IsUnit ((fullMatrix J).submatrix rows columns)) :
    ((fullMatrix J).submatrix rows columns)⁻¹ *ᵥ
        (fun i => (signSum Z (∏ j, Q j ^ (rows i j).val) : ℚ)) =
      fun c => (signCount Z Q (columns c) : ℚ) := by
  have hm := mulVec_signCount (K := ℚ) Z Q columns (fun i j => (rows i j).val) hinj cover
  have hM : (Matrix.of fun i c => ∏ j, (columns c j : ℚ) ^ (rows i j).val) =
      (fullMatrix J).submatrix rows columns := by
    ext i c
    simp
  rw [hM] at hm
  rw [← hm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mulVec]

open scoped Classical in
/-- The realized sign conditions admit an invertible square query matrix whose inverse
recovers their counts. There is exactly one selected query per realized condition. -/
theorem exists_inv_fullMatrix_submatrix_mulVec_signSum (Z : Finset R) (Q : J → R[X]) :
    ∃ rows : {σ : J → SignType // 0 < signCount Z Q σ} ↪ (J → Fin 3),
      IsUnit ((fullMatrix J).submatrix rows
        (fun σ : {σ : J → SignType // 0 < signCount Z Q σ} => σ.val)) ∧
      ((fullMatrix J).submatrix rows
        (fun σ : {σ : J → SignType // 0 < signCount Z Q σ} => σ.val))⁻¹ *ᵥ
          (fun i => (signSum Z (∏ j, Q j ^ (rows i j).val) : ℚ)) =
        fun σ => (signCount Z Q σ.val : ℚ) := by
  classical
  obtain ⟨rows, hunit⟩ := exists_isUnit_fullMatrix_submatrix
    (Subtype.val : {σ : J → SignType // 0 < signCount Z Q σ} → J → SignType)
    Subtype.val_injective
  refine ⟨rows, hunit, inv_fullMatrix_submatrix_mulVec_signSum Z Q Subtype.val rows
    Subtype.val_injective ?_ hunit⟩
  intro x hx
  exact ⟨⟨fun j => SignType.sign ((Q j).eval x), (signCount_pos Z Q _).mpr ⟨x, hx, fun _ => rfl⟩⟩,
    rfl⟩

end Finset

namespace Polynomial

open TauCeti.SignDetermination

variable {R J : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype J]

open scoped Classical in
/-- Selected Tarski queries recover precisely the realized sign counts at distinct roots.
For `p = 0`, both the root sample and the collection of realized columns are empty. -/
theorem exists_inv_fullMatrix_submatrix_mulVec_tarskiQuery (p : R[X]) (Q : J → R[X]) :
    ∃ rows : {σ : J → SignType // 0 < Finset.signCount p.roots.toFinset Q σ} ↪ (J → Fin 3),
      IsUnit ((fullMatrix J).submatrix rows
        (fun σ : {σ : J → SignType // 0 < Finset.signCount p.roots.toFinset Q σ} => σ.val)) ∧
      ((fullMatrix J).submatrix rows
        (fun σ : {σ : J → SignType // 0 < Finset.signCount p.roots.toFinset Q σ} => σ.val))⁻¹ *ᵥ
          (fun i => (tarskiQuery p (∏ j, Q j ^ (rows i j).val) : ℚ)) =
        fun σ => (Finset.signCount p.roots.toFinset Q σ.val : ℚ) := by
  simpa only [tarskiQuery_eq_signSum] using
    p.roots.toFinset.exists_inv_fullMatrix_submatrix_mulVec_signSum Q

end Polynomial
