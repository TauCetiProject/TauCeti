/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.A
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.C
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.D
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion

/-!
# Characteristic polynomials of the classical Coxeter elements

In the simple-root basis, the Coxeter element `s₀ s₁ ⋯ s_{n-1}` has characteristic polynomial

* `1 + X + ⋯ + Xⁿ` for `Aₙ`,
* `Xⁿ + 1` for `Bₙ` and `Cₙ`,
* `(X^{n-1} + 1)(X + 1)` for `Dₙ`.

For `Aₙ` the Coxeter element is, up to relabelling the indices, the companion matrix of
`1 + X + ⋯ + Xⁿ` (`TauCeti.Coxeter.coxeterElement_A_apply`), and so is the negacyclic shift for
`Xⁿ + 1`; `Polynomial.charpoly_companion` gives their characteristic polynomials. The `ε`-models of
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B` and
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.D` intertwine the Coxeter element with the
negacyclic shift (for `Dₙ`, with the negacyclic shift and a sign on the last coordinate, which is
block diagonal), and `TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.C` reduces `Cₙ` to `Bₙ`
through the diagonal intertwiner `TauCeti.Coxeter.dB`. In each case the intertwiner can be
cancelled, so it has nonzero determinant and `Matrix.charpoly_eq_of_mul_eq_mul` transfers the
characteristic polynomial.
-/

public section

open Polynomial Matrix

namespace TauCeti.Coxeter

/-- **The negacyclic shift on `ℤⁿ` has characteristic polynomial `Xⁿ + 1`**: up to relabelling,
it is the companion matrix of `Xⁿ + 1`. -/
theorem charpoly_negaShift (m : ℕ) : (negaShift (m + 1)).charpoly = X ^ (m + 1) + 1 := by
  have hdeg : (X ^ (m + 1) + 1 : ℤ[X]).natDegree = m + 1 := by simp
  have hmon : (X ^ (m + 1) + 1 : ℤ[X]).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) (n := m + 1) (by omega)
  have h : negaShift (m + 1) =
      reindex (finCongr hdeg) (finCongr hdeg) (X ^ (m + 1) + 1 : ℤ[X]).companion := by
    ext a b
    simp only [reindex_apply, submatrix_apply, finCongr_symm, finCongr_apply, companion_apply,
      Fin.val_cast, negaShift_apply, hdeg, coeff_add, coeff_X_pow, coeff_one]
    split_ifs <;> omega
  rw [h, charpoly_reindex, charpoly_companion hmon]

/-- **The Coxeter element of type `Bₙ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_coxeterElement_B {n : ℕ} (hn : 1 ≤ n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← charpoly_eq_of_mul_eq_mul (nonsingular_iff_det_ne_zero.mp (.of_leftRegular fun X Y h => by
      rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← epsBInv_mul_epsB, Matrix.mul_assoc,
        Matrix.mul_assoc]
      exact congrArg _ h)) epsB_mul_coxeterElement.symm, charpoly_negaShift]

/-- **The Coxeter element of type `Cₙ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_coxeterElement_C {n : ℕ} (hn : 1 ≤ n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 := by
  rw [charpoly_eq_of_mul_eq_mul (nonsingular_iff_det_ne_zero.mp (.of_leftRegular isLeftRegular_dB))
    dB_mul_coxeterElement.symm, charpoly_coxeterElement_B hn]

private theorem charpoly_neg_one_fin_one : (-1 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = X + 1 := by
  simp [charpoly, det_unique, sub_eq_add_neg]

theorem charpoly_negaD (m : ℕ) : (negaD m).charpoly = (X ^ (m + 2) + 1) * (X + 1) := by
  rw [← charpoly_reindex (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm,
    reindex_negaD, charpoly_fromBlocks_zero₁₂, charpoly_negaShift, charpoly_neg_one_fin_one]

/-- **The Coxeter element of type `Dₙ` has characteristic polynomial `(X^{n-1} + 1)(X + 1)`.** -/
theorem charpoly_coxeterElement_D {n : ℕ} (hn : 3 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact (charpoly_eq_of_mul_eq_mul (nonsingular_iff_det_ne_zero.mp
    (.of_leftRegular isLeftRegular_epsD)) epsD_mul_coxeterElement.symm).symm.trans
    (charpoly_negaD m)

/-- Row sums of `epsA`: they telescope. -/
theorem sum_epsA_row {n : ℕ} (a : Fin (n + 1)) :
    ∑ j : Fin n, epsA n a j = (if a.val = 0 then 1 else 0) - (if a.val = n then 1 else 0) := by
  simp only [epsA_apply]
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
  have hCe : epsA n * C = permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsA n := by
    ext a k
    rw [Equiv.Perm.permMatrixHom_mul_apply, Matrix.mul_apply]
    have hs : ((finRotate (n + 1)).symm a).val = if a.val = 0 then n else a.val - 1 := by
      obtain ⟨b, rfl⟩ := (finRotate (n + 1)).surjective a
      rw [Equiv.symm_apply_apply, coe_finRotate]
      by_cases h : b = Fin.last n
      · rw [ite_eq_left h, ite_eq_left rfl, h, Fin.val_last]
      · rw [ite_eq_right h, ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    by_cases hk : k.val + 1 < n
    · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩]
      · simp only [hC, epsA_apply, Matrix.of_apply, hk, ite_true, mul_one]
        split_ifs at hs ⊢ <;> omega
      · intro j _ hj
        simp only [hC, Matrix.of_apply, hk, ite_true]
        rw [ite_eq_right (fun h => absurd (Fin.ext h) hj), mul_zero]
      · simp
    · simp only [hC, Matrix.of_apply, hk, ite_false, mul_neg, mul_one, Finset.sum_neg_distrib,
        sum_epsA_row]
      simp only [epsA_apply]
      split_ifs at hs ⊢ <;> omega
  rw [epsA_mul_left_cancel (epsA_mul_coxeterElement.trans hCe.symm)]
  rfl

/-- **The Coxeter element of type `Aₙ` has characteristic polynomial `1 + X + ⋯ + Xⁿ`**: up to
relabelling, it is the companion matrix of that polynomial. -/
theorem charpoly_coxeterElement_A (n : ℕ) :
    (coxeterElement (CartanMatrix.A n)).charpoly = ∑ i ∈ Finset.range (n + 1), X ^ i := by
  have hdeg : (∑ i ∈ Finset.range (n + 1), (X : ℤ[X]) ^ i).natDegree = n := natDegree_geom_sum_X n
  have h : coxeterElement (CartanMatrix.A n) = reindex (finCongr hdeg) (finCongr hdeg)
      (∑ i ∈ Finset.range (n + 1), (X : ℤ[X]) ^ i).companion := by
    ext a k
    simp only [coxeterElement_A_apply, reindex_apply, submatrix_apply, finCongr_symm,
      finCongr_apply, companion_apply, Fin.val_cast, hdeg, finsetSum_coeff, coeff_X_pow,
      Finset.sum_ite_eq, Finset.mem_range]
    split_ifs <;> omega
  rw [h, charpoly_reindex, charpoly_companion (monic_geom_sum_X (Nat.succ_ne_zero n))]

end TauCeti.Coxeter

end
