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
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite.

## Main result

* `Matrix.exists_mul_eq_of_range_le`: construct the right factor from column preimages.
* `Matrix.mul_left_cancel_of_mulVec_injective`: cancel an injective left factor even for
  matrices with an empty output-column index type.
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

end Matrix
