/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.RingTheory.Length.Determinant
import TauCeti.RingTheory.OrderOfVanishing

/-!
# Cokernel length of matrix rows modulo a scalar via maximal minors

For a matrix `A : Matrix r k Λ` (with possibly infinitely many rows `r` and finitely many
columns `k`) and a scalar `a : Λ`, `TauCeti.maximalMinors A a` is the set of `|k| × |k|` minors
of the stacked matrix `A.fromRows (a • 1)`, and `TauCeti.rowLattice A a` is the submodule of
`k → O` spanned by the rows of `A` and of `a • 1`.

Over a principal ideal domain `O` with `a ≠ 0`, `rowLattice A a` has full rank and is therefore
spanned by the rows of a square matrix (`TauCeti.exists_span_row_eq_rowLattice`). Over a discrete
valuation ring `O`, the length of the quotient `(k → O) ⧸ rowLattice A a` equals the least
valuation `IsDiscreteValuationRing.addVal O` of an element of `maximalMinors A a`
(`TauCeti.isLeast_length_quotient_rowLattice`).

## Main definitions and results

* `TauCeti.maximalMinors`: the `|k| × |k|` minors of `A.fromRows (a • 1)`.
* `TauCeti.rowLattice`: the `O`-submodule of `k → O` spanned by the rows of `A.fromRows (a • 1)`.
* `TauCeti.image_maximalMinors`: ring homomorphisms map `maximalMinors A a` onto
  `maximalMinors (A.map ev) (ev a)`.
* `TauCeti.exists_span_row_eq_rowLattice`: over a PID with `a ≠ 0`, `rowLattice A a` is spanned
  by the rows of a square matrix `N : Matrix k k O`.
* `TauCeti.isLeast_length_quotient_rowLattice`: over a DVR with `a ≠ 0`, the length of
  `(k → O) ⧸ rowLattice A a` is the least valuation of a maximal minor in `maximalMinors A a`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/General/Algebra/SharpMinors.lean`
(`New.Selmer.maximalMinors`, `New.Selmer.rowLattice`, `New.Selmer.image_maximalMinors`,
`New.Selmer.exists_span_row_eq_rowLattice`, `New.Selmer.isLeast_length_quotient_rowLattice`).
-/

public section

noncomputable section

namespace TauCeti

open Matrix Module Submodule IsDiscreteValuationRing

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [DecidableEq k]

/-- The `|k| × |k|` minors of the matrix formed by stacking `A` over `a • 1`. Repeated row
choices are allowed and contribute the minor `0`. -/
def maximalMinors [Fintype k] (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- The `O`-submodule of `k → O` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

/-- A ring homomorphism `ev : Λ →+* O` maps `maximalMinors A a` onto
`maximalMinors (A.map ev) (ev a)`. -/
theorem image_maximalMinors [Fintype k] (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' maximalMinors A a = maximalMinors (A.map ev) (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [Matrix.one_apply, apply_ite ev]
  simp [maximalMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

/-- Every multiple `a • v` lies in `rowLattice A a`. -/
theorem smul_mem_rowLattice [Finite k] (A : Matrix r k O) (a : O) (v : k → O) :
    a • v ∈ rowLattice A a := by
  cases nonempty_fintype k
  refine span_mono ?_ ((range_vecMulLinear (a • (1 : Matrix k k O))).le ⟨v, by simp⟩)
  exact Set.range_subset_iff.mpr fun j ↦ ⟨.inr j, rfl⟩

/-- Over a principal ideal domain `O` and for `a ≠ 0`, `rowLattice A a` is free of full rank and
therefore spanned by the rows of a square matrix `N : Matrix k k O`. -/
theorem exists_span_row_eq_rowLattice [Finite k] [IsDomain O] [IsPrincipalIdealRing O]
    (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    ∃ N : Matrix k k O, span O (Set.range N.row) = rowLattice A a := by
  cases nonempty_fintype k
  let g : (k → O) →ₗ[O] rowLattice A a :=
    (LinearMap.lsmul O _ a).codRestrict _ (smul_mem_rowLattice A a)
  have h_inj : Function.Injective g := (LinearMap.lsmul_injective ha).codRestrict _
  have h_rank : finrank O (k → O) = finrank O (rowLattice A a) :=
    (g.finrank_le_finrank_of_injective h_inj).antisymm (Submodule.finrank_le _)
  let b : Basis k O (rowLattice A a) := (Pi.basisFun O k).map (.ofFinrankEq _ _ h_rank)
  refine ⟨Matrix.of fun i ↦ (b i : k → O), ?_⟩
  change span O (Set.range ((rowLattice A a).subtype ∘ b)) = rowLattice A a
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, map_subtype_top]

/-- Over a discrete valuation ring `O` and for `a ≠ 0`, the length of `(k → O) ⧸ rowLattice A a`
is the least valuation `addVal O` of a maximal minor in `maximalMinors A a`. -/
theorem isLeast_length_quotient_rowLattice [Fintype k] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    IsLeast (addVal O '' maximalMinors A a) (Module.length O ((k → O) ⧸ rowLattice A a)) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) : ℕ∞ := addVal O (M.submatrix f id).det
  have h_len (B : Matrix k k O) (hB : B.det ≠ 0) :
      Module.length O ((k → O) ⧸ span O (Set.range B.row)) = addVal O B.det := by
    rw [← col_transpose, ← Bᵀ.range_mulVecLin,
      Matrix.length_quotient_range_mulVecLin_eq_ord_det Bᵀ (by simpa), det_transpose,
      Ring.ord_eq_addVal]
  have h_lower (f : k → r ⊕ k) : Module.length O ((k → O) ⧸ rowLattice A a) ≤ v f := by
    rcases eq_or_ne (M.submatrix f id).det 0 with h0 | h0
    · simp [v, h0]
    have h_le : span O (Set.range (M.submatrix f id).row) ≤ rowLattice A a :=
      span_mono (Set.range_comp_subset_range f M.row)
    simpa only [h_len _ h0] using
      Module.length_le_of_surjective _ (Submodule.factor_surjective h_le)
  obtain ⟨N, hN⟩ := exists_span_row_eq_rowLattice A ha
  have hN_det : N.det ≠ 0 := by
    choose C hC using fun i : k ↦
      (range_vecMulLinear N).ge (hN.symm ▸ smul_mem_rowLattice A a (Pi.single i 1))
    have hCN : Matrix.of C * N = a • 1 := Matrix.ext fun i j ↦ by
      simpa [Matrix.mul_apply, vecMul, dotProduct, Matrix.one_apply, Pi.single_apply,
        eq_comm (a := j)] using congrFun (hC i) j
    intro h0
    exact pow_ne_zero (Fintype.card k) ha (by simpa [h0, eq_comm] using congrArg det hCN)
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  let f₀ : k → r ⊕ k := Function.argmin v
  have h_dvd : (M.submatrix f₀ id).det ∣ N.det := Ideal.mem_span_singleton.mp <|
    TauCeti.det_mem_of_mem_span LinearMap.proj (fun i ↦ hN.le (subset_span ⟨i, rfl⟩))
      fun w hw ↦ by
        choose f hf using hw
        obtain rfl : w = M.submatrix f id := (funext hf).symm
        exact Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (Function.argmin_le v f))
  have h_upper : v f₀ ≤ Module.length O ((k → O) ⧸ rowLattice A a) :=
    (addVal_le_iff_dvd.mpr h_dvd).trans_eq (by rw [← hN, h_len N hN_det])
  exact ⟨⟨(M.submatrix f₀ id).det, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩,
    Set.forall_mem_image.mpr (Set.forall_mem_range.mpr h_lower)⟩

end TauCeti
