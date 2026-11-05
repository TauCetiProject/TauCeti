/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm

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

For a bilinear form `B` and a vector `v`, the corresponding *condensed form* is

```text
S(x, y) = B(v, v) · B(x, y) - B(x, v) · B(v, y).
```

It is symmetric when `B` is, and it vanishes when either argument is `v`, so it does not change
when multiples of `v` are added to its arguments. If `B` is positive definite, `S` is positive on
the nonzero vectors of the kernel of any linear functional that does not vanish at `v`; this is the
strict Cauchy–Schwarz inequality. If `v` is the first vector of a basis `c`, the Gram matrix of `S`
on the other basis vectors is the condensation of the Gram matrix of `B` in `c`, so Chiò's identity
computes its determinant.

## Main results

* `Matrix.mul_det_condensation_eq_pow_mul_det`: `A 0 0 · det A' = (A 0 0)ⁿ · det A`.
* `LinearMap.BilinForm.IsSymm.exists_isSymm_forall_apply_eq`: the condensed form of a symmetric
  form, read on any module through a linear map, is a symmetric form.
* `LinearMap.BilinForm.mul_apply_add_smul_add_smul`: completing the square along `v`,
  `B(v, v) B(x + s v, y + t v) = B(x + s v, v) B(v, y + t v) + S(x, y)`.
* `LinearMap.BilinForm.apply_mul_apply_lt_of_mem_ker`: for `B` positive definite, the condensed
  form is positive on the nonzero vectors of the kernel of a functional not vanishing at `v`.
* `LinearMap.BilinForm.mul_det_toMatrix_eq_pow_mul_det_toMatrix`: Chiò's identity for Gram
  matrices, `B(v, v) · det S = B(v, v)ⁿ · det B`.

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

namespace LinearMap.BilinForm

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The condensed form along `v`.** For a symmetric form `B`, a vector `v` and a linear map
`φ : N →ₗ[R] M`, the condensed form along `v`, read on `N` through `φ`, is a symmetric form:
some symmetric `S` on `N` has `S(y, z) = B(v, v) B(φ y, φ z) - B(φ y, v) B(v, φ z)`. -/
theorem IsSymm.exists_isSymm_forall_apply_eq {N : Type*} [AddCommGroup N] [Module R N]
    {B : LinearMap.BilinForm R M} (hB : B.IsSymm) (v : M) (φ : N →ₗ[R] M) :
    ∃ S : LinearMap.BilinForm R N, S.IsSymm ∧
      ∀ y z, S y z = B v v * B (φ y) (φ z) - B (φ y) v * B v (φ z) := by
  refine ⟨B v v • B.compl₁₂ φ φ - (LinearMap.mul R R).compl₁₂ (B.flip v ∘ₗ φ) (B v ∘ₗ φ),
    isSymm_def.mpr fun y z ↦ ?_, fun y z ↦ by simp⟩
  simp [hB.eq (φ y) (φ z), hB.eq (φ y) v, hB.eq v (φ z), mul_comm]

/-- **Completing the square along `v`.** Adding multiples of `v` to the arguments of `B` does not
change the condensed form `S(x, y) = B(v, v) B(x, y) - B(x, v) B(v, y)`:
`B(v, v) B(x + s v, y + t v) = B(x + s v, v) B(v, y + t v) + S(x, y)`. -/
theorem mul_apply_add_smul_add_smul (B : LinearMap.BilinForm R M) (v x y : M) (s t : R) :
    B v v * B (x + s • v) (y + t • v) =
      B (x + s • v) v * B v (y + t • v) + (B v v * B x y - B x v * B v y) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The condensed form of a positive definite form is positive on a complement of `v`.** Let `B`
be positive definite on a torsion-free module over an ordered ring. If a linear functional `f` does
not vanish at `v`, then every nonzero `x` in its kernel satisfies
`B(x, v) B(v, x) < B(v, v) B(x, x)`. This is the strict Cauchy–Schwarz inequality, since `v` and
`x` are linearly independent. -/
theorem apply_mul_apply_lt_of_mem_ker [LinearOrder R] [IsStrictOrderedRing R]
    [Module.IsTorsionFree R M] {B : LinearMap.BilinForm R M} (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    {f : M →ₗ[R] R} {v x : M} (hv : f v ≠ 0) (hx : x ∈ LinearMap.ker f) (hx0 : x ≠ 0) :
    B x v * B v x < B v v * B x x := by
  rw [mul_comm (B v v)]
  refine (B.apply_mul_apply_lt_iff_linearIndependent hpos x v).mpr
    (LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_)
  obtain rfl : t = 0 := by simpa [LinearMap.mem_ker.mp hx, hv] using congrArg f hst
  simpa [hx0] using hst

/-- **Chiò's condensation for Gram matrices.** Let `c` be a basis of `M` indexed by `Fin (n + 1)`
and `S` a bilinear form on `N` whose values on a basis `b` are those of the condensed form along
`c 0` on `c 1, …, c n`, that is, whose Gram matrix in `b` is the condensation of the Gram matrix of
`B` in `c`. Then `B(c 0, c 0) · det S = B(c 0, c 0)ⁿ · det B`, the determinants being taken in `b`
and `c`. -/
theorem mul_det_toMatrix_eq_pow_mul_det_toMatrix {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (B : LinearMap.BilinForm R M) (c : Basis (Fin (n + 1)) R M) {S : LinearMap.BilinForm R N}
    (b : Basis (Fin n) R N) (hS : ∀ i j, S (b i) (b j) =
      B (c 0) (c 0) * B (c i.succ) (c j.succ) - B (c i.succ) (c 0) * B (c 0) (c j.succ)) :
    B (c 0) (c 0) * (toMatrix b S).det = B (c 0) (c 0) ^ n * (toMatrix c B).det := by
  have h := Matrix.mul_det_condensation_eq_pow_mul_det (toMatrix c B)
  simp only [toMatrix_apply] at h
  rw [← h]
  congr 2
  ext i j
  simp [toMatrix_apply, hS]

end LinearMap.BilinForm
