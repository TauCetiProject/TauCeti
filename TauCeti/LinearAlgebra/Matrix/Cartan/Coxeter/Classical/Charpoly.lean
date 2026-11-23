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
cancelled (for `Bₙ` it even has an inverse over `ℤ`), so it has nonzero determinant and
`Matrix.charpoly_eq_of_mul_eq_mul` transfers the characteristic polynomial.
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
  rw [← charpoly_eq_of_mul_eq_mul (det_ne_zero_of_left_inverse epsBInv_mul_epsB)
    epsB_mul_coxeterElement.symm, charpoly_negaShift]

/-- **The Coxeter element of type `Cₙ` has characteristic polynomial `Xⁿ + 1`.** -/
theorem charpoly_coxeterElement_C {n : ℕ} (hn : 1 ≤ n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 := by
  rw [charpoly_eq_of_mul_eq_mul (nonsingular_iff_det_ne_zero.mp (.of_leftRegular isLeftRegular_dB))
    dB_mul_coxeterElement.symm, charpoly_coxeterElement_B hn]

private theorem charpoly_neg_one_fin_one : (-1 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = X + 1 := by
  simp [charpoly, det_unique, sub_eq_add_neg]

/-- **`negaD m` has characteristic polynomial `(X^{m+2} + 1)(X + 1)`**: it is block diagonal with
blocks the negacyclic shift on `ℤ^{m+2}` and `-1`. -/
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
