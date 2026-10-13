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

namespace TauCeti

/-- Differentiating a finite sum of iterates produces the next rescaling coefficients. -/
private theorem sum_rescaleCoefficients {k R : Type*}
    [CommSemiring k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (a : R) (c : ℕ → R) (i : ℕ) (z : R)
    (hc : c (i + 1) = 0) :
    a * D (∑ j ∈ Finset.range (i + 1), c j * (D : R → R)^[j] z) =
      ∑ j ∈ Finset.range (i + 2),
        (a * D (c j) + if j = 0 then 0 else a * c (j - 1)) * (D : R → R)^[j] z := by
  calc
    _ = (∑ j ∈ Finset.range (i + 1), a * D (c j) * (D : R → R)^[j] z) +
        ∑ j ∈ Finset.range (i + 1), a * c j * (D : R → R)^[j + 1] z := by
      simp [map_sum, D.leibniz, Finset.mul_sum, Finset.sum_add_distrib,
        Function.iterate_succ_apply', mul_add, mul_comm, mul_assoc, add_comm]
    _ = (∑ j ∈ Finset.range (i + 2), a * D (c j) * (D : R → R)^[j] z) +
        ∑ j ∈ Finset.range (i + 2),
          (if j = 0 then 0 else a * c (j - 1)) * (D : R → R)^[j] z := by
      congr 1
      · rw [Finset.sum_range_succ
          (fun j ↦ a * D (c j) * (D : R → R)^[j] z) (i + 1)]
        simp [hc]
      · rw [Finset.sum_range_succ'
          (fun j ↦ (if j = 0 then 0 else a * c (j - 1)) * (D : R → R)^[j] z) (i + 1)]
        simp
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end TauCeti

namespace Derivation

variable {k R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]

/-- The iterates of `a D` are triangular combinations of the iterates of `D`, with
leading coefficient `a ^ i`. The coefficients are only used to compute the determinant. -/
private theorem exists_rescaleCoefficients (D : Derivation k R R) (a : R) (i : ℕ) :
    ∃ c : ℕ → R, (∀ j, i < j → c j = 0) ∧ c i = a ^ i ∧
      ∀ z, ((a • D : Derivation k R R) : R → R)^[i] z =
        ∑ j ∈ Finset.range (i + 1), c j * (D : R → R)^[j] z := by
  induction i with
  | zero =>
      exact ⟨fun j ↦ if j = 0 then 1 else 0,
        by intro j hj; simp [Nat.ne_of_gt hj], by simp, by simp⟩
  | succ i ih =>
      obtain ⟨c, hc, hdiag, hiter⟩ := ih
      let d : ℕ → R := fun j ↦ a * D (c j) + if j = 0 then 0 else a * c (j - 1)
      have hd (j : ℕ) : d (j + 1) = a * D (c (j + 1)) + a * c j := by simp [d]
      have hlast : c (i + 1) = 0 := hc _ (by omega)
      refine ⟨d, ?_, ?_, fun z ↦ ?_⟩
      · intro j hj
        have hj0 : j ≠ 0 := by omega
        simp [d, hj0, hc j (by omega), hc (j - 1) (by omega)]
      · simp [hd, hlast, hdiag, pow_succ, mul_comm]
      · rw [Function.iterate_succ_apply', hiter, Derivation.smul_apply, smul_eq_mul]
        exact TauCeti.sum_rescaleCoefficients D a c i z hlast

/-- Rescaling a derivation by `a` multiplies an `n`-function Wronskian by
`a ^ (n * (n - 1) / 2)`. The scalar need not be a constant of the derivation. -/
@[simp]
theorem wronskian_smul (D : Derivation k R R) (a : R) {n : ℕ} (f : Fin n → R) :
    (a • D).wronskian f = a ^ (n * (n - 1) / 2) * D.wronskian f := by
  classical
  choose c hc hdiag hiter using exists_rescaleCoefficients D a
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
    intro l hl hli
    have hil : i.val < l := by simp only [Finset.mem_range] at hli; omega
    simp [hc i.val l hil]
  rw [wronskian_def, hmatrix, Matrix.det_mul, Matrix.det_of_isLowerTriangular A htri]
  simp only [A, Matrix.of_apply, hdiag]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n,
    Finset.sum_range_id, ← wronskian_def]

end Derivation
