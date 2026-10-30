/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Factoring matrices through a column range

A matrix `L'` factors as `L * G` whenever each of its columns belongs to the range of
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite. We also
give a criterion, splitting off the top row, for the column range of a matrix to be a given
submodule.

## Main result

* `Matrix.col_mem_range_mulVecLin`: every column of `L` lies in the range of `L.mulVecLin`.
* `Matrix.exists_mul_eq_of_range_le`: construct the right factor from column preimages.
* `Matrix.mul_left_cancel_of_mulVec_injective`: cancel an injective left factor even for
  matrices with an empty output-column index type.
* `Matrix.range_mulVecLin_eq_of_succ`: a matrix with columns in a submodule `L` of `R^(n+1)` has
  column range `L` if it reaches every vector of `L` below the top row and every vector of `L`
  supported on the top row.
-/

public section

namespace Matrix

section LeftCancellation

variable {R m ι κ : Type*} [NonUnitalSemiring R] [Fintype ι]

/-- If matrix-vector multiplication by `L` is injective, multiplication by `L`
cancels on the left, even when the right-hand matrices have no columns. -/
theorem mul_left_cancel_of_mulVec_injective
    {L : Matrix m ι R} (hL : Function.Injective L.mulVec)
    {X Y : Matrix ι κ R} (hXY : L * X = L * Y) : X = Y := by
  classical
  rcases isEmpty_or_nonempty κ with hEmpty | hNonempty
  · ext i j
    exact (hEmpty.false j).elim
  · let : Inhabited κ := ⟨Classical.choice hNonempty⟩
    exact (mul_right_injective_iff_mulVec_injective.mpr hL) hXY

end LeftCancellation

variable {R m ι κ : Type*} [CommSemiring R] [Fintype ι]

/-- Every column of `L` lies in the range of matrix-vector multiplication by `L`. -/
theorem col_mem_range_mulVecLin (L : Matrix m ι R) (j : ι) :
    L.col j ∈ LinearMap.range L.mulVecLin := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]⟩

/-- If every column of `L'` lies in the range of `L`, then `L' = L * G` for some `G`.
The index type of the columns of `L'` need not be finite. -/
theorem exists_mul_eq_of_range_le {L : Matrix m ι R} {L' : Matrix m κ R}
    (h : ∀ j : κ, L'.col j ∈ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix ι κ R, L * G = L' := by
  classical
  have hpre (j : κ) : ∃ v : ι → R, L.mulVec v = L'.col j := h j
  choose v hv using hpre
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hv j) i

section Succ

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A matrix `H` with columns in a submodule `L` of `R^(n+1)` has column range `L` if every vector
of `L` agrees with a vector of the column range below the top row, and every vector of `L`
supported on the top row lies in the column range. -/
theorem range_mulVecLin_eq_of_succ {n : ℕ} {L : Submodule R (Fin (n + 1) → R)}
    {H : Matrix (Fin (n + 1)) ι R} (hcol : ∀ j, H.col j ∈ L)
    (htail : ∀ x ∈ L, ∃ c, ∀ i : Fin n, (H *ᵥ c) i.succ = x i.succ)
    (hsingle : ∀ a, Pi.single 0 a ∈ L → Pi.single 0 a ∈ LinearMap.range H.mulVecLin) :
    LinearMap.range H.mulVecLin = L := by
  have hle : LinearMap.range H.mulVecLin ≤ L := by
    rw [range_mulVecLin, Submodule.span_le, Set.range_subset_iff]
    exact hcol
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := htail x hx
  -- The difference of `x` and `H *ᵥ c` is supported on the top row.
  have hy : x - H *ᵥ c = Pi.single 0 ((x - H *ᵥ c) 0) := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [hc i]
  have hmem := hsingle _ (hy ▸ sub_mem hx (hle ⟨c, rfl⟩))
  rw [← hy] at hmem
  simpa using add_mem hmem (LinearMap.mem_range_self H.mulVecLin c)

end Succ

end Matrix
