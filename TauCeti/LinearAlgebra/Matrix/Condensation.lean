/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Chiò's condensation

Let `A` be a square matrix of size `n + 1` over a commutative ring, with corner entry
`a = A 0 0`. Its *condensation* at that corner is the `n × n` matrix of `2 × 2` minors

```text
A' i j = a · A (i + 1) (j + 1) - A (i + 1) 0 · A 0 (j + 1),
```

and Chiò's identity says `a · det A' = aⁿ · det A`. Over a field with `a ≠ 0` it is the Schur
complement formula `det A = a · det (D - C a⁻¹ B)` with the denominators cleared, and it holds over
every commutative ring, with no invertibility hypothesis. This is what makes it usable for integral
matrices: the condensation of an integral Gram matrix is again integral, and it is `a` times the
Gram matrix of the projection orthogonal to the first basis vector. That is the inductive step of
Hermite's inequality for the minimum of a positive definite quadratic form over `ℤ`.

## Main results

* `Matrix.mul_det_condensation_eq_pow_mul_det`: `A 0 0 · det A' = (A 0 0)ⁿ · det A`.

## References

* F. Chiò, *Mémoire sur les fonctions connues sous le nom de résultantes ou de déterminants*,
  Turin, 1853.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- **Chiò's condensation.** For a square matrix `A` of size `n + 1`, the matrix `A'` of `2 × 2`
minors `A 0 0 * A (i + 1) (j + 1) - A (i + 1) 0 * A 0 (j + 1)` satisfies
`A 0 0 · det A' = (A 0 0)ⁿ · det A`. No invertibility of `A 0 0` is needed. -/
theorem mul_det_condensation_eq_pow_mul_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A 0 0 * (of fun i j : Fin n ↦ A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ).det =
      A 0 0 ^ n * A.det := by
  -- Scale the rows below the corner by `A 0 0`, then clear the first column below the corner.
  set s : Fin (n + 1) → R := Fin.cons 1 fun _ ↦ A 0 0
  set c : Fin (n + 1) → R := Fin.cons 0 fun i ↦ A i.succ 0
  set A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) R := of fun i j ↦ s i * A i j
  set A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) R := of fun i j ↦ A₁ i j - c i * A₁ 0 j
  have h₁ : A₁.det = A 0 0 ^ n * A.det := by
    rw [det_mul_column, Fin.prod_univ_succ]
    simp [s]
  have h₂ : A₁.det = A₂.det :=
    det_eq_of_forall_row_eq_smul_add_const c 0 rfl fun i j ↦ by simp [A₂, c]
  have h₃ : A₂.det = A 0 0 *
      (of fun i j : Fin n ↦ A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero fun i _ ↦ by
      simp [A₂, A₁, s, c, mul_comm]]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, add_zero]
    congr 2
    · simp [A₂, A₁, s, c]
    · ext i j
      simp [A₂, A₁, s, c]
  rw [← h₃, ← h₂, h₁]

end Matrix
