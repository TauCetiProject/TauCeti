/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Algebra.Lie.Prod
import Mathlib.Tactic.LinearCombination

/-!
# Skew-adjoint matrices commuting with a block involution

On an orthogonal direct sum, the involution acting as the identity on the first summand and
minus the identity on the second has block-diagonal centralizer, provided two is regular.
`Matrix.skewAdjointBlockCentralizerEquiv` identifies its skew-adjoint centralizer with the
product of the two skew-adjoint Lie algebras. Its forward map extends the two blocks by zero;
its inverse restricts to the diagonal blocks. If the negative eigenspace is a regular line,
`Matrix.skewAdjointBlockCentralizerLineEquiv` removes its zero skew-adjoint Lie algebra and
identifies the centralizer with the skew-adjoint algebra of the positive eigenspace alone.

This supplies the restriction and extension maps for fixed orthogonal Lie algebras after an
orthogonal involution has been diagonalized. No nonsingularity or symmetry of the forms is
needed, and either summand may be empty.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters I–III, Chapter I, §6
  (classical Lie algebras).
-/

public section

namespace Matrix

attribute [local instance] LieRing.ofAssociativeRing

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The skew-adjoint centralizer of the involution with signs `+1` and `-1` on an orthogonal
direct sum with Gram matrices `J` and `K`. -/
def skewAdjointBlockCentralizer (J : Matrix m m R) (K : Matrix n n R) :
    LieSubalgebra R (Matrix (m ⊕ n) (m ⊕ n) R) :=
  skewAdjointMatricesLieSubalgebra (fromBlocks J 0 0 K) ⊓
    lieSubalgebraOfSubalgebra R _ (Subalgebra.centralizer R
      {fromBlocks (1 : Matrix m m R) 0 0 (-1 : Matrix n n R)})

/-- Membership is skew-adjointness together with commutation with the block involution. -/
theorem mem_skewAdjointBlockCentralizer_iff (J : Matrix m m R) (K : Matrix n n R)
    (X : Matrix (m ⊕ n) (m ⊕ n) R) :
    X ∈ skewAdjointBlockCentralizer J K ↔
      X ∈ skewAdjointMatricesLieSubalgebra (fromBlocks J 0 0 K) ∧
      fromBlocks (1 : Matrix m m R) 0 0 (-1 : Matrix n n R) * X =
        X * fromBlocks (1 : Matrix m m R) 0 0 (-1 : Matrix n n R) := by
  simp [skewAdjointBlockCentralizer, lieSubalgebraOfSubalgebra,
    Subalgebra.mem_centralizer_iff]

/-- When two is regular, the skew-adjoint centralizer consists exactly of independent
skew-adjoint diagonal blocks and zero off-diagonal blocks. -/
@[simp]
theorem mem_skewAdjointBlockCentralizer_iff_blocks (J : Matrix m m R) (K : Matrix n n R)
    (h2 : IsRegular (2 : R)) (X : Matrix (m ⊕ n) (m ⊕ n) R) :
    X ∈ skewAdjointBlockCentralizer J K ↔
      X.toBlocks₁₁ ∈ skewAdjointMatricesLieSubalgebra J ∧
      X.toBlocks₂₂ ∈ skewAdjointMatricesLieSubalgebra K ∧
      X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0 := by
  rw [mem_skewAdjointBlockCentralizer_iff]
  constructor
  · rintro ⟨hX, hc⟩
    rw [← fromBlocks_toBlocks X, fromBlocks_multiply, fromBlocks_multiply] at hc
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hc
    have hB : X.toBlocks₁₂ = 0 := by
      ext i j
      have h := congrArg (fun Y => Y (.inl i) (.inr j)) hc
      simp only [fromBlocks_apply₁₂, Matrix.neg_apply] at h
      apply h2.left
      simp only [Matrix.zero_apply, mul_zero]
      linear_combination h
    have hC : X.toBlocks₂₁ = 0 := by
      ext i j
      have h := congrArg (fun Y => Y (.inr i) (.inl j)) hc
      simp only [fromBlocks_apply₂₁, Matrix.neg_apply] at h
      apply h2.left
      simp only [Matrix.zero_apply, mul_zero]
      linear_combination -h
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
      Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← fromBlocks_toBlocks X, hB, hC] at hX
    simp only [fromBlocks_transpose, transpose_zero, fromBlocks_neg, neg_zero,
      fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hX
    exact ⟨by simpa [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
      Matrix.IsAdjointPair] using congrArg toBlocks₁₁ hX,
      by simpa [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
        Matrix.IsAdjointPair] using congrArg toBlocks₂₂ hX, hB, hC⟩
  · rintro ⟨hJ, hK, hB, hC⟩
    simp only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
      Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hJ hK ⊢
    rw [← fromBlocks_toBlocks X, hB, hC]
    simp [fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply, hJ, hK]

/-- Zero extension of two skew-adjoint blocks is a Lie equivalence onto the skew-adjoint
centralizer of the block involution. The inverse is restriction to the diagonal blocks. -/
def skewAdjointBlockCentralizerEquiv (J : Matrix m m R) (K : Matrix n n R)
    (h2 : IsRegular (2 : R)) :
    (skewAdjointMatricesLieSubalgebra J × skewAdjointMatricesLieSubalgebra K) ≃ₗ⁅R⁆
      skewAdjointBlockCentralizer J K where
  toFun X := ⟨fromBlocks X.1 0 0 X.2,
    (mem_skewAdjointBlockCentralizer_iff_blocks J K h2 _).2
      (by simp)⟩
  invFun X :=
    let hX := (mem_skewAdjointBlockCentralizer_iff_blocks J K h2 X).1 X.property
    (⟨(X : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₁₁, hX.1⟩,
      ⟨(X : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₂, hX.2.1⟩)
  left_inv X := by ext <;> rfl
  right_inv X := by
    apply Subtype.ext
    have hX := (mem_skewAdjointBlockCentralizer_iff_blocks J K h2 X).1 X.property
    simpa only [hX.2.2.1, hX.2.2.2] using fromBlocks_toBlocks (X : Matrix (m ⊕ n) (m ⊕ n) R)
  map_add' X Y := by
    apply Subtype.ext
    simp [fromBlocks_add]
  map_smul' t X := by
    apply Subtype.ext
    simp [fromBlocks_smul]
  map_lie' {X Y} := by
    apply Subtype.ext
    ext (i | i) (j | j) <;> simp [Ring.lie_def, fromBlocks_multiply]

/-- The forward equivalence is block-diagonal zero extension. -/
@[simp]
theorem coe_skewAdjointBlockCentralizerEquiv (J : Matrix m m R) (K : Matrix n n R)
    (h2 : IsRegular (2 : R))
    (X : skewAdjointMatricesLieSubalgebra J × skewAdjointMatricesLieSubalgebra K) :
    (skewAdjointBlockCentralizerEquiv J K h2 X : Matrix (m ⊕ n) (m ⊕ n) R) =
      fromBlocks X.1 0 0 X.2 := (rfl)

/-- The first inverse component is restriction to the first summand. -/
@[simp]
theorem coe_skewAdjointBlockCentralizerEquiv_symm_fst (J : Matrix m m R)
    (K : Matrix n n R) (h2 : IsRegular (2 : R)) (X : skewAdjointBlockCentralizer J K) :
    ((skewAdjointBlockCentralizerEquiv J K h2).symm X).1.val =
      (X : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₁₁ := (rfl)

/-- The second inverse component is restriction to the second summand. -/
@[simp]
theorem coe_skewAdjointBlockCentralizerEquiv_symm_snd (J : Matrix m m R)
    (K : Matrix n n R) (h2 : IsRegular (2 : R)) (X : skewAdjointBlockCentralizer J K) :
    ((skewAdjointBlockCentralizerEquiv J K h2).symm X).2.val =
      (X : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₂ := (rfl)

/-- A regular form in dimension at most one has zero skew-adjoint Lie algebra when two is
regular. -/
theorem skewAdjointMatricesLieSubalgebra_eq_bot_of_subsingleton [Subsingleton n]
    (J : Matrix n n R) (h2 : IsRegular (2 : R)) (hJ : ∀ i, IsRegular (J i i)) :
    skewAdjointMatricesLieSubalgebra J = ⊥ := by
  apply bot_unique
  intro X hX
  rw [LieSubalgebra.mem_bot]
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  have h := congrArg (fun Y : Matrix n n R => Y i i)
    ((mem_skewAdjointMatricesSubmodule J X).1 hX)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Fintype.sum_subsingleton _ i] at h
  apply h2.left
  apply (hJ i).left
  simp only [Matrix.zero_apply, mul_zero]
  linear_combination h

/-- If the negative eigenspace is a regular line, restriction to the positive eigenspace
identifies the skew-adjoint centralizer with its skew-adjoint Lie algebra. -/
def skewAdjointBlockCentralizerLineEquiv (J : Matrix m m R) (c : R)
    (h2 : IsRegular (2 : R)) (hc : IsRegular c) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆
      skewAdjointBlockCentralizer J (of fun _ _ : Unit => c) := by
  let E := skewAdjointBlockCentralizerEquiv J (of fun _ _ : Unit => c) h2
  have hz (X : skewAdjointMatricesLieSubalgebra (of fun _ _ : Unit => c)) : X = 0 := by
    apply Subtype.ext
    have hx : (X : Matrix Unit Unit R) ∈ (⊥ : LieSubalgebra R (Matrix Unit Unit R)) := by
      simpa only [skewAdjointMatricesLieSubalgebra_eq_bot_of_subsingleton
        (of fun _ _ : Unit => c) h2 (fun _ => hc)] using X.property
    exact (LieSubalgebra.mem_bot _).1 hx
  exact
    { toFun := fun X => E (X, 0)
      invFun := fun X => (E.symm X).1
      left_inv := fun X => by simp
      right_inv := fun X => by
        apply E.symm.injective
        exact (E.symm_apply_apply _).trans (Prod.ext rfl (hz (E.symm X).2).symm)
      map_add' := fun X Y => by simpa using E.map_add (X, 0) (Y, 0)
      map_smul' := fun t X => by simpa using E.map_smul t (X, 0)
      map_lie' := by
        intro X Y
        simpa using E.map_lie (X, 0) (Y, 0) }

/-- The line equivalence extends a matrix by zero on the line and on both mixed blocks. -/
@[simp]
theorem coe_skewAdjointBlockCentralizerLineEquiv (J : Matrix m m R) (c : R)
    (h2 : IsRegular (2 : R)) (hc : IsRegular c)
    (X : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointBlockCentralizerLineEquiv J c h2 hc X :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R) = fromBlocks X 0 0 0 := (rfl)

/-- The inverse line equivalence restricts to the positive eigenspace. -/
@[simp]
theorem coe_skewAdjointBlockCentralizerLineEquiv_symm (J : Matrix m m R) (c : R)
    (h2 : IsRegular (2 : R)) (hc : IsRegular c)
    (X : skewAdjointBlockCentralizer J (of fun _ _ : Unit => c)) :
    ((skewAdjointBlockCentralizerLineEquiv J c h2 hc).symm X : Matrix m m R) =
      (X : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ := (rfl)

end Matrix
