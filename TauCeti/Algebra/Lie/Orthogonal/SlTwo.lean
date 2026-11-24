/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# `𝔰𝔩₂(ℝ) ≅ 𝔰𝔬(2, 1)`

The real Lie algebra `𝔰𝔬(2, 1) = LieAlgebra.Orthogonal.so' (Fin 2) (Fin 1) ℝ` of the matrices
skew-adjoint for `diag(1, 1, -1)` consists of the block matrices `[[A, b], [bᵀ, 0]]` with `A`
skew-symmetric of size two. This file builds the Lie algebra isomorphism
`TauCeti.slTwoLieEquivSoTwoOne : sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ so' (Fin 2) (Fin 1) ℝ`, sending
`[[x, y], [z, -x]]` to

`[[0, y - z, 2x], [z - y, 0, y + z], [2x, y + z, 0]]`.

It carries the rotation generator `[[0, 1], [-1, 0]]` of `𝔰𝔩₂(ℝ)` to twice the rotation
generator of `𝔰𝔬(2)` and the symmetric matrices `diag(1, -1)` and `[[0, 1], [1, 0]]` to twice the
two boosts. It intertwines the two Cartan involutions `X ↦ -Xᵀ`
(`TauCeti.slTwoLieEquivSoTwoOne_neg_transpose`).

## Main definitions

* `TauCeti.soTwoOneMatrix x y z`: the matrix `[[0, y - z, 2x], [z - y, 0, y + z], [2x, y + z, 0]]`
  of `𝔰𝔬(2, 1)`.
* `TauCeti.slTwoLieEquivSoTwoOne`: the isomorphism `𝔰𝔩₂(ℝ) ≃ 𝔰𝔬(2, 1)`.
-/

public section

open LieAlgebra LieAlgebra.Orthogonal LieAlgebra.SpecialLinear Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The matrix `[[0, y - z, 2x], [z - y, 0, y + z], [2x, y + z, 0]]` of `𝔰𝔬(2, 1)`, the image of
`[[x, y], [z, -x]] ∈ 𝔰𝔩₂(ℝ)` under `TauCeti.slTwoLieEquivSoTwoOne`. -/
def soTwoOneMatrix (x y z : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  fromBlocks !![0, y - z; z - y, 0] !![2 * x; y + z] !![2 * x, y + z] 0

/-- `soTwoOneMatrix x y z` is the block matrix `[[A, b], [bᵀ, 0]]` with
`A = [[0, y - z], [z - y, 0]]` and `b = [2x, y + z]`. -/
theorem soTwoOneMatrix_def (x y z : ℝ) :
    soTwoOneMatrix x y z = fromBlocks !![0, y - z; z - y, 0] !![2 * x; y + z] !![2 * x, y + z] 0 :=
  (rfl)

/-- A matrix indexed by `Fin 2 ⊕ Fin 1` is determined by its nine entries. -/
private theorem ext_fin_two_sum_fin_one {M N : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ}
    (h₀₀ : M (.inl 0) (.inl 0) = N (.inl 0) (.inl 0))
    (h₀₁ : M (.inl 0) (.inl 1) = N (.inl 0) (.inl 1))
    (h₀₂ : M (.inl 0) (.inr 0) = N (.inl 0) (.inr 0))
    (h₁₀ : M (.inl 1) (.inl 0) = N (.inl 1) (.inl 0))
    (h₁₁ : M (.inl 1) (.inl 1) = N (.inl 1) (.inl 1))
    (h₁₂ : M (.inl 1) (.inr 0) = N (.inl 1) (.inr 0))
    (h₂₀ : M (.inr 0) (.inl 0) = N (.inr 0) (.inl 0))
    (h₂₁ : M (.inr 0) (.inl 1) = N (.inr 0) (.inl 1))
    (h₂₂ : M (.inr 0) (.inr 0) = N (.inr 0) (.inr 0)) : M = N := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> assumption

/-- `soTwoOneMatrix` is additive in `(x, y, z)`. -/
theorem soTwoOneMatrix_add (x y z x' y' z' : ℝ) :
    soTwoOneMatrix (x + x') (y + y') (z + z') = soTwoOneMatrix x y z + soTwoOneMatrix x' y' z' := by
  apply ext_fin_two_sum_fin_one <;> simp [soTwoOneMatrix] <;> ring

/-- `soTwoOneMatrix` is homogeneous in `(x, y, z)`. -/
theorem soTwoOneMatrix_smul (r x y z : ℝ) :
    soTwoOneMatrix (r * x) (r * y) (r * z) = r • soTwoOneMatrix x y z := by
  apply ext_fin_two_sum_fin_one <;> simp [soTwoOneMatrix] <;> ring

/-- Negating `(x, y, z)` negates `soTwoOneMatrix x y z`. -/
theorem soTwoOneMatrix_neg (x y z : ℝ) :
    soTwoOneMatrix (-x) (-y) (-z) = -soTwoOneMatrix x y z := by
  simpa using soTwoOneMatrix_smul (-1) x y z

/-- Transposing `soTwoOneMatrix x y z` swaps `y` and `z`. -/
theorem soTwoOneMatrix_transpose (x y z : ℝ) :
    (soTwoOneMatrix x y z)ᵀ = soTwoOneMatrix x z y := by
  simp [soTwoOneMatrix, fromBlocks_transpose, ← Matrix.ext_iff, Fin.forall_fin_two, add_comm]

/-- `soTwoOneMatrix x y z` lies in `𝔰𝔬(2, 1)`. -/
theorem soTwoOneMatrix_mem_so' (x y z : ℝ) : soTwoOneMatrix x y z ∈ so' (Fin 2) (Fin 1) ℝ := by
  simp [mem_so'_iff_forall, Sum.forall, Fin.forall_fin_two, soTwoOneMatrix, indefiniteDiagonal]

/-- The isomorphism `𝔰𝔩₂(ℝ) ≃ 𝔰𝔬(2, 1)`, sending `[[x, y], [z, -x]]` to
`TauCeti.soTwoOneMatrix x y z`. -/
noncomputable def slTwoLieEquivSoTwoOne : sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ so' (Fin 2) (Fin 1) ℝ where
  toFun X := ⟨soTwoOneMatrix (X.val 0 0) (X.val 0 1) (X.val 1 0), soTwoOneMatrix_mem_so' _ _ _⟩
  map_add' X Y := Subtype.ext (soTwoOneMatrix_add _ _ _ _ _ _)
  map_smul' r X := Subtype.ext (soTwoOneMatrix_smul _ _ _ _)
  map_lie' {X Y} := by
    have hX := val_one_one_eq_neg_val_zero_zero X
    have hY := val_one_one_eq_neg_val_zero_zero Y
    refine Subtype.ext (ext_fin_two_sum_fin_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp [soTwoOneMatrix, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.fromBlocks_multiply, hX, hY] <;> ring
  invFun N := ⟨!![N.val (.inl 0) (.inr 0) / 2,
      (N.val (.inl 0) (.inl 1) + N.val (.inl 1) (.inr 0)) / 2;
      (N.val (.inl 1) (.inr 0) - N.val (.inl 0) (.inl 1)) / 2, -(N.val (.inl 0) (.inr 0) / 2)], by
    rw [mem_sl_iff]
    simp [trace_fin_two]⟩
  left_inv X := by
    have hX := val_one_one_eq_neg_val_zero_zero X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [soTwoOneMatrix, hX]
  right_inv N := by
    have h := (mem_so'_iff_forall N.val).mp N.property
    have h₁ := h (.inl 0) (.inl 0)
    have h₂ := h (.inl 1) (.inl 1)
    have h₃ := h (.inl 0) (.inl 1)
    have h₄ := h (.inl 0) (.inr 0)
    have h₅ := h (.inl 1) (.inr 0)
    have h₆ := h (.inr 0) (.inr 0)
    simp only [indefiniteDiagonal, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr]
      at h₁ h₂ h₃ h₄ h₅ h₆
    refine Subtype.ext (ext_fin_two_sum_fin_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp [soTwoOneMatrix] <;> linarith

/-- The image of `[[x, y], [z, -x]]` is `TauCeti.soTwoOneMatrix x y z`. -/
@[simp]
theorem coe_slTwoLieEquivSoTwoOne_apply (X : sl (Fin 2) ℝ) :
    (slTwoLieEquivSoTwoOne X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) =
      soTwoOneMatrix (X.val 0 0) (X.val 0 1) (X.val 1 0) :=
  (rfl)

/-- The inverse isomorphism `𝔰𝔬(2, 1) ≃ 𝔰𝔩₂(ℝ)` reads `x`, `y`, `z` off the entries of
`TauCeti.soTwoOneMatrix x y z`. -/
@[simp]
theorem coe_slTwoLieEquivSoTwoOne_symm_apply (N : so' (Fin 2) (Fin 1) ℝ) :
    (slTwoLieEquivSoTwoOne.symm N : Matrix (Fin 2) (Fin 2) ℝ) =
      !![N.val (.inl 0) (.inr 0) / 2,
        (N.val (.inl 0) (.inl 1) + N.val (.inl 1) (.inr 0)) / 2;
        (N.val (.inl 1) (.inr 0) - N.val (.inl 0) (.inl 1)) / 2, -(N.val (.inl 0) (.inr 0) / 2)] :=
  (rfl)

/-- The isomorphism `𝔰𝔩₂(ℝ) ≃ 𝔰𝔬(2, 1)` intertwines the Cartan involutions `X ↦ -Xᵀ` of the two
sides. -/
theorem slTwoLieEquivSoTwoOne_neg_transpose (X : sl (Fin 2) ℝ) :
    (slTwoLieEquivSoTwoOne ⟨-X.valᵀ, neg_transpose_mem_sl X.property⟩ :
        Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) =
      -(slTwoLieEquivSoTwoOne X : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ)ᵀ := by
  rw [coe_slTwoLieEquivSoTwoOne_apply, coe_slTwoLieEquivSoTwoOne_apply, soTwoOneMatrix_transpose,
    ← soTwoOneMatrix_neg]
  simp

end TauCeti
