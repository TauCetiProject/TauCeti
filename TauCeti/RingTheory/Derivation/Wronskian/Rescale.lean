/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Wronskian.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Rescaling the derivation in a Wronskian

Replacing a derivation `D` by `a • D` multiplies the Wronskian of `n` functions by
`a ^ (n * (n - 1) / 2)`. The factor `a` need not be constant or invertible, and the
identity holds over commutative rings in every characteristic.

For function fields this is the change-of-parameter law for Wronskians. Together with
the transformation of `dx`, it makes the differential tensor
`Wr_x(f) (dx)^(n(n-1)/2)` independent of the separating parameter `x`, as required
for the ramification divisor of a linear series.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer,
  2003, the Wronskian treatment of Weierstrass points.
-/

public section

namespace Derivation

variable {k R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]

/-- Rescaling a derivation by `a` multiplies an `n`-function Wronskian by
`a ^ (n * (n - 1) / 2)`. The scalar need not be a constant of the derivation. -/
@[simp]
theorem wronskian_smul (D : Derivation k R R) (a : R) {n : ℕ} (f : Fin n → R) :
    (a • D).wronskian f = a ^ (n * (n - 1) / 2) * D.wronskian f := by
  let c : ℕ → ℕ → R := smulIterCoeff D a
  have hc : ∀ i j, i < j → c i j = 0 := fun _ _ hij ↦ smulIterCoeff_eq_zero_of_lt D a hij
  have hdiag : ∀ i, c i i = a ^ i := smulIterCoeff_self D a
  have hiter : ∀ i z, ((a • D : Derivation k R R) : R → R)^[i] z =
      ∑ j ∈ Finset.range (i + 1), c i j * (D : R → R)^[j] z :=
    fun i z ↦ iterate_smul_apply_eq_sum D a z i
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j ↦ c i.val j.val
  have htri : A.IsLowerTriangular := by
    intro i j hij
    exact hc i.val j.val hij
  have hmatrix :
      (Matrix.of fun i j : Fin n ↦ ((a • D : Derivation k R R) : R → R)^[i.val] (f j)) =
        A * (Matrix.of fun i j : Fin n ↦ (D : R → R)^[i.val] (f j)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, A]
    rw [hiter, Fin.sum_univ_eq_sum_range (fun l ↦ c i.val l * (D : R → R)^[l] (f j)) n]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l _ hli
    have hil : i.val < l := by simp only [Finset.mem_range] at hli; omega
    simp [hc i.val l hil]
  rw [wronskian_def, hmatrix, Matrix.det_mul, Matrix.det_of_isLowerTriangular A htri]
  simp only [A, Matrix.of_apply, hdiag]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n,
    Finset.sum_range_id, ← wronskian_def]

end Derivation
