/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.A
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.C
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.D
import TauCeti.Algebra.Polynomial.BigOperators

/-!
# Characteristic polynomials of the classical Coxeter elements

In the simple-root basis, the Coxeter element `s₀ s₁ ⋯ s_{n-1}` has characteristic polynomial

* `Xⁿ + 1` for `Bₙ` and `Cₙ`,
* `(X^{n-1} + 1)(X + 1)` for `Dₙ`,
* `1 + X + ⋯ + Xⁿ` for `Aₙ`.

The ε-models of `TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B`,
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.C`,
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.D` intertwine the Coxeter element with the
negacyclic shift (and, for `Dₙ`, a sign on the last coordinate), so
`Matrix.charpoly_eq_of_mul_eq_mul` transfers the polynomial. The negacyclic shift has the cyclic
vector `e₀` (`Matrix.charpoly_eq_of_cyclic`). For `Dₙ` the eigenvalue `-1` is double when `n` is
even, so there is no cyclic vector; the model is block diagonal instead. For `Aₙ` the Coxeter
element is the companion matrix of `1 + X + ⋯ + Xⁿ` (`TauCeti.Coxeter.coxeterElement_A_apply`).
In both cases the powers of the matrix carry the cyclic vector `e₀` to the standard basis.
-/

public section

open Polynomial Matrix Equiv.Perm

namespace TauCeti.Coxeter

/-- **The negacyclic shift on `ℤⁿ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_negaShift (m : ℕ) : (negaShift (m + 1)).charpoly = X ^ (m + 1) + 1 := by
  classical
  have hv : ∀ k : Fin (m + 1), (negaShift (m + 1) ^ (k : ℕ)) *ᵥ Pi.single 0 1 = Pi.single k 1 := by
    intro k
    funext a
    rw [mulVec_single_one, col_apply, negaShift_pow (by omega), Pi.single_apply]
    simp only [Fin.ext_iff, Fin.val_zero, zero_add]
    split_ifs <;> omega
  have hli : LinearIndependent ℤ fun k : Fin (m + 1) =>
      (negaShift (m + 1) ^ (k : ℕ)) *ᵥ Pi.single 0 1 := by
    simp_rw [hv]
    exact Pi.linearIndependent_single_one _ _
  refine charpoly_eq_of_cyclic _ (monic_X_pow_add_C 1 (by omega))
    (natDegree_X_pow_add_C) (Pi.single 0 1) hli ?_
  rw [map_add, map_pow, aeval_X, map_one, negaShift_pow_self, neg_add_cancel, zero_mulVec]

/-- **The Coxeter element of type `Bₙ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_coxeterElement_B (m : ℕ) :
    (coxeterElement (CartanMatrix.B (m + 1))).charpoly = X ^ (m + 1) + 1 := by
  rw [← charpoly_eq_of_mul_eq_mul (det_ne_zero_of_mul_left_cancel fun X Y h => by
      rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← epsBInv_mul_epsB, Matrix.mul_assoc,
        Matrix.mul_assoc, h]) epsB_mul_coxeterElement.symm, charpoly_negaShift]

/-- **The Coxeter element of type `Cₙ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_coxeterElement_C (m : ℕ) :
    (coxeterElement (CartanMatrix.C (m + 1))).charpoly = X ^ (m + 1) + 1 := by
  rw [charpoly_eq_of_mul_eq_mul (det_ne_zero_of_mul_left_cancel fun X Y h =>
      dB_mul_left_cancel h) dB_mul_coxeterElement.symm, charpoly_coxeterElement_B]

/-- `Fin (m + 3) ≃ Fin (m + 2) ⊕ Fin 1`. -/
@[expose] def eD (m : ℕ) : Fin (m + 3) ≃ Fin (m + 2) ⊕ Fin 1 :=
  (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm

/-- `negaD m` is block diagonal: the negacyclic shift on the first `m + 2` coordinates, `-1` on
the last. -/
theorem reindex_negaD (m : ℕ) :
    reindex (eD m) (eD m) (negaD m) =
      fromBlocks (negaShift (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext (i | i) (j | j)
  · simp only [reindex_apply, submatrix_apply, eD, Equiv.symm_symm, finSumFinEquiv_apply_left,
      fromBlocks_apply₁₁, negaD, negaShift, Matrix.of_apply, Fin.val_castAdd]
    split_ifs <;> omega
  · simp only [reindex_apply, submatrix_apply, eD, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, fromBlocks_apply₁₂, negaD, Matrix.of_apply, Fin.val_castAdd,
      Fin.val_natAdd, Matrix.zero_apply]
    split_ifs <;> omega
  · simp only [reindex_apply, submatrix_apply, eD, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, fromBlocks_apply₂₁, negaD, Matrix.of_apply, Fin.val_castAdd,
      Fin.val_natAdd, Matrix.zero_apply]
    split_ifs <;> omega
  · simp only [reindex_apply, submatrix_apply, eD, Equiv.symm_symm, finSumFinEquiv_apply_right,
      fromBlocks_apply₂₂, negaD, Matrix.of_apply, Fin.val_natAdd, Matrix.neg_apply,
      Matrix.one_apply, Subsingleton.elim i j]
    split_ifs <;> omega

theorem charpoly_neg_one_fin_one : (-1 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = X + 1 := by
  simp [charpoly, det_unique, sub_eq_add_neg]

theorem charpoly_negaD (m : ℕ) : (negaD m).charpoly = (X ^ (m + 2) + 1) * (X + 1) := by
  rw [← charpoly_reindex (eD m), reindex_negaD, charpoly_fromBlocks_zero₁₂,
    charpoly_negaShift, charpoly_neg_one_fin_one]

/-- **The Coxeter element of type `Dₙ` has characteristic polynomial `(X^{n-1} + 1)(X + 1)`**
(`n = m + 3`). -/
theorem charpoly_coxeterElement_D (m : ℕ) :
    (coxeterElement (CartanMatrix.D (m + 3))).charpoly = (X ^ (m + 2) + 1) * (X + 1) := by
  rw [← charpoly_eq_of_mul_eq_mul (det_ne_zero_of_mul_left_cancel fun X Y h =>
      epsD_mul_left_cancel h) epsD_mul_coxeterElement.symm, charpoly_negaD]

/-- Row sums of `epsMatrix`: they telescope. -/
theorem sum_epsMatrix_row {n : ℕ} (a : Fin (n + 1)) :
    ∑ j : Fin n, epsMatrix n a j = (if a.val = 0 then 1 else 0) - (if a.val = n then 1 else 0) := by
  simp only [epsMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if a.val = i then (1 : ℤ) else 0) - (if a.val = i + 1 then 1 else 0)) n]
  exact Finset.sum_range_sub' (fun i => if a.val = i then (1 : ℤ) else 0) n

/-- **The Coxeter element of type `Aₙ` is the companion matrix of `1 + X + ⋯ + Xⁿ`**: it sends
`eₖ` to `e_{k+1}` for `k + 1 < n`, and `e_{n-1}` to `-(e₀ + ⋯ + e_{n-1})`. -/
theorem coxeterElement_A_apply {n : ℕ} (a k : Fin n) :
    coxeterElement (CartanMatrix.A n) a k =
      if k.val + 1 < n then (if a.val = k.val + 1 then 1 else 0) else -1 := by
  set C : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a k =>
    if k.val + 1 < n then (if a.val = k.val + 1 then 1 else 0) else -1 with hC
  have hc : epsMatrix n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsMatrix n := by
    rw [coxeterElement, epsMatrix_mul_prod, prod_adjSwap_eq_finRotate]
  have hCe : epsMatrix n * C = permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsMatrix n := by
    ext a k
    rw [permMatrixHom_mul_apply, Matrix.mul_apply]
    have hs : ((finRotate (n + 1)).symm a).val = if a.val = 0 then n else a.val - 1 := by
      obtain ⟨b, rfl⟩ := (finRotate (n + 1)).surjective a
      rw [Equiv.symm_apply_apply, coe_finRotate]
      by_cases h : b = Fin.last n
      · rw [ite_eq_left h, ite_eq_left rfl, h, Fin.val_last]
      · rw [ite_eq_right h, ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    by_cases hk : k.val + 1 < n
    · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩]
      · simp only [hC, epsMatrix, Matrix.of_apply, hk, ite_true, mul_one]
        split_ifs at hs ⊢ <;> omega
      · intro j _ hj
        simp only [hC, Matrix.of_apply, hk, ite_true]
        rw [ite_eq_right (fun h => absurd (Fin.ext h) hj), mul_zero]
      · simp
    · simp only [hC, Matrix.of_apply, hk, ite_false, mul_neg, mul_one, Finset.sum_neg_distrib,
        sum_epsMatrix_row]
      simp only [epsMatrix, Matrix.of_apply]
      split_ifs at hs ⊢ <;> omega
  have hcancel : ∀ X Y : Matrix (Fin n) (Fin n) ℤ, epsMatrix n * X = epsMatrix n * Y → X = Y :=
    fun X Y h => by
      rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← epsLeftInv_mul_epsMatrix, Matrix.mul_assoc,
        Matrix.mul_assoc, h]
  rw [hcancel _ _ (hc.trans hCe.symm)]
  rfl

/-- **The Coxeter element of type `Aₙ` has characteristic polynomial `1 + X + ⋯ + Xⁿ`.** -/
theorem charpoly_coxeterElement_A (m : ℕ) :
    (coxeterElement (CartanMatrix.A (m + 1))).charpoly = ∑ i ∈ Finset.range (m + 2), X ^ i := by
  classical
  set c := coxeterElement (CartanMatrix.A (m + 1))
  have hcol : ∀ k : Fin (m + 1), c *ᵥ Pi.single k 1 =
      fun a => if k.val + 1 < m + 1 then (if a.val = k.val + 1 then 1 else 0) else -1 := by
    intro k
    funext a
    rw [mulVec_single_one, col_apply]
    exact coxeterElement_A_apply a k
  have hpow : ∀ (k : ℕ) (hk : k < m + 1), (c ^ k) *ᵥ Pi.single 0 1 = Pi.single ⟨k, hk⟩ 1 := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [pow_zero, Matrix.one_mulVec]
      congr 1
    | succ k ih =>
      intro hk
      rw [pow_succ', ← mulVec_mulVec, ih (by omega), hcol]
      funext a
      simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  have hv : ∀ k : Fin (m + 1), (c ^ (k : ℕ)) *ᵥ Pi.single 0 1 = Pi.single k 1 :=
    fun k => hpow k k.isLt
  have hmon : (∑ i ∈ Finset.range (m + 2), (X : ℤ[X]) ^ i).Monic := monic_geom_sum_X (by omega)
  have hli : LinearIndependent ℤ fun k : Fin (m + 1) => (c ^ (k : ℕ)) *ᵥ Pi.single 0 1 := by
    simp_rw [hv]
    exact Pi.linearIndependent_single_one _ _
  refine charpoly_eq_of_cyclic c hmon (natDegree_geom_sum_X (m + 1)) (Pi.single 0 1) hli ?_
  have hlast : (c ^ (m + 1)) *ᵥ Pi.single 0 1 = fun _ => -1 := by
    have h := hv (Fin.last m)
    rw [Fin.val_last] at h
    rw [pow_succ', ← mulVec_mulVec, h, hcol]
    funext a
    simp
  rw [map_sum, sum_mulVec, Finset.sum_range_succ]
  simp only [map_pow, aeval_X]
  rw [hlast]
  rw [← Fin.sum_univ_eq_sum_range (fun i => (c ^ i) *ᵥ Pi.single 0 1)]
  simp only [hv]
  funext a
  simp [Finset.sum_apply, Pi.single_apply]

end TauCeti.Coxeter

end
