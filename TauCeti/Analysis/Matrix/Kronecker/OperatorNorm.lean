/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.LinearAlgebra.Matrix.Kronecker.Power

/-!
# Euclidean operator norms of Kronecker powers

The operator norm bound for a binary Kronecker product iterates to powers with arbitrary finite
index sets. The bound does not involve the matrix dimensions, and includes rectangular matrices.
-/

public section

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

private theorem l2_opNorm_kroneckerPower_fin_le (A : Matrix m n 𝕜) (d : ℕ) :
    ‖A.kroneckerPower (Fin d)‖ ≤ ‖A‖ ^ d := by
  induction d with
  | zero =>
    have h : A.kroneckerPower (Fin 0) = (1 : Matrix (Fin 0 → n) (Fin 0 → n) 𝕜).submatrix
        (fun _ ↦ (Fin.elim0 : Fin 0 → n)) id := by
      ext i j
      simp [kroneckerPower_apply, Matrix.one_apply, Subsingleton.elim (Fin.elim0 : Fin 0 → n) j]
    simpa only [h, pow_zero] using
      (l2_opNorm_submatrix_le _ (fun _ _ _ ↦ Subsingleton.elim _ _) Function.injective_id).trans
        (l2_opNorm_one_le (n := Fin 0 → n) (𝕜 := 𝕜))
  | succ d ih =>
    let eₘ := (Fin.consEquiv (fun _ : Fin (d + 1) ↦ m)).symm
    let eₙ := (Fin.consEquiv (fun _ : Fin (d + 1) ↦ n)).symm
    have h : A.kroneckerPower (Fin (d + 1)) = (A ⊗ₖ A.kroneckerPower (Fin d)).submatrix eₘ eₙ := by
      ext i j
      simp [eₘ, eₙ, Fin.consEquiv, Fin.tail, kroneckerPower_apply, Fin.prod_univ_succ,
        kroneckerMap_apply]
    rw [h, pow_succ']
    exact (l2_opNorm_submatrix_le _ eₘ.injective eₙ.injective).trans
      ((l2_opNorm_kronecker_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _)))

/-- The Euclidean operator norm of the `κ`-indexed Kronecker power is at most the operator norm
of the original matrix raised to `card κ`. -/
theorem l2_opNorm_kroneckerPower_le {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix m n 𝕜) :
    ‖A.kroneckerPower κ‖ ≤ ‖A‖ ^ Fintype.card κ := by
  let e := Fintype.equivFin κ
  let em : (κ → m) ≃ (Fin (Fintype.card κ) → m) := Equiv.arrowCongr e (Equiv.refl m)
  let en : (κ → n) ≃ (Fin (Fintype.card κ) → n) := Equiv.arrowCongr e (Equiv.refl n)
  have h : A.kroneckerPower κ = (A.kroneckerPower (Fin (Fintype.card κ))).submatrix em en := by
    ext i j
    simpa [kroneckerPower_apply, em, en] using
      (Fintype.prod_equiv e (fun k ↦ A (i k) (j k)) (fun k ↦ A (i (e.symm k)) (j (e.symm k)))
        (by simp))
  rw [h]
  exact (l2_opNorm_submatrix_le _ em.injective en.injective).trans
    (l2_opNorm_kroneckerPower_fin_le A _)

end Matrix
