/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Factoring matrices through a column range

A matrix `L'` factors as `L * G` whenever each of its columns belongs to the range of
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite. We also
give a criterion, splitting off the top row, for the column range of a matrix to be a given
submodule, and characterize when two nonsingular square matrices over a commutative domain span
the same column range.

## Main result

* `Matrix.col_mem_range_mulVecLin`: every column of `L` lies in the range of `L.mulVecLin`.
* `Matrix.row_mem_range_vecMulLinear`: every row of `e` lies in the range of `e.vecMulLinear`.
* `Matrix.exists_mul_eq_of_range_le`: construct the right factor from column preimages.
* `Matrix.mul_left_cancel_of_mulVec_injective`: cancel an injective left factor even for
  matrices with an empty output-column index type.
* `Matrix.range_mulVecLin_eq_of_succ`: a matrix with columns in a submodule `L` of `R^(n+1)` has
  column range `L` if it reaches every vector of `L` below the top row and every vector of `L`
  supported on the top row.
* `Matrix.range_comp_mulVecLin_unit`, `Matrix.range_mulVecLin_mul_unit`: precomposing with or
  right-multiplying by `U ∈ GL n R` preserves the range / column range.
* `Matrix.range_mulVecLin_eq_iff`: over a commutative domain, two nonsingular square matrices have
  the same column range if and only if they lie in the same right `GL n R`-coset.
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

section RowRange

variable {A ι κ : Type*} [Semiring A] [Fintype ι]

open LinearMap in
/-- Each row of a matrix lies in the range of right multiplication by it: it is the image of the
corresponding standard basis vector. -/
theorem row_mem_range_vecMulLinear (e : Matrix ι κ A) (i : ι) :
    e i ∈ range e.vecMulLinear := by
  classical
  exact ⟨Pi.single i 1, Matrix.single_one_vecMul i e⟩

end RowRange

section RightCoset

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommSemiring R]

/-- Precomposing a linear map out of `n → R` with `(U : Matrix n n R).mulVecLin` for `U ∈ GL n R`
preserves its range. -/
@[simp]
theorem range_comp_mulVecLin_unit {M : Type*} [AddCommMonoid M] [Module R M]
    (f : (n → R) →ₗ[R] M) (U : GL n R) :
    LinearMap.range (f ∘ₗ (↑U : Matrix n n R).mulVecLin) = LinearMap.range f :=
  LinearMap.range_comp_of_range_eq_top f <| LinearMap.range_eq_top_of_surjective _ <|
    Function.RightInverse.surjective (g := (↑U⁻¹ : Matrix n n R).mulVecLin) fun v ↦ by
      have hU : (↑U : Matrix n n R) * (↑U⁻¹ : Matrix n n R) = 1 :=
        (Units.val_mul U U⁻¹).symm.trans (by simp)
      simp [mulVec_mulVec, hU]

/-- Right-multiplying a matrix by a `GL n R` unit preserves the `R`-submodule spanned by its
columns. -/
-- Deliberately not `@[simp]`: `Matrix.mulVecLin_mul` rewrites the LHS to
-- `range_comp_mulVecLin_unit`.
theorem range_mulVecLin_mul_unit {m : Type*} (B : Matrix m n R) (U : GL n R) :
    LinearMap.range (B * (↑U : Matrix n n R)).mulVecLin = LinearMap.range B.mulVecLin := by
  rw [mulVecLin_mul, range_comp_mulVecLin_unit]

/-- Over a commutative domain, two nonsingular square matrices span the same column `R`-submodule if
and only if they lie in the same right `GL n R`-coset. -/
theorem range_mulVecLin_eq_iff {R : Type*} [CommRing R] [IsDomain R] {B₁ B₂ : Matrix n n R}
    (h₁ : B₁.det ≠ 0) (h₂ : B₂.det ≠ 0) :
    LinearMap.range B₁.mulVecLin = LinearMap.range B₂.mulVecLin ↔
      ∃ U : GL n R, B₁ * (↑U : Matrix n n R) = B₂ := by
  refine ⟨fun hrange ↦ ?_, ?_⟩
  · obtain ⟨P, hBP⟩ := exists_mul_eq_of_range_le fun j ↦ hrange ▸ col_mem_range_mulVecLin B₂ j
    obtain ⟨Q, hBQ⟩ := exists_mul_eq_of_range_le fun j ↦ hrange ▸ col_mem_range_mulVecLin B₁ j
    have hreg₁ := (isRegular_of_isLeftRegular_det fun _ _ ↦ mul_left_cancel₀ h₁).left
    have hreg₂ := (isRegular_of_isLeftRegular_det fun _ _ ↦ mul_left_cancel₀ h₂).left
    have hPQ : P * Q = 1 :=
      hreg₁ (by dsimp only; rw [← Matrix.mul_assoc, hBP, hBQ, Matrix.mul_one])
    have hQP : Q * P = 1 :=
      hreg₂ (by dsimp only; rw [← Matrix.mul_assoc, hBQ, hBP, Matrix.mul_one])
    exact ⟨⟨P, Q, hPQ, hQP⟩, hBP⟩
  · rintro ⟨U, rfl⟩
    exact (range_mulVecLin_mul_unit B₁ U).symm

end RightCoset

end Matrix
