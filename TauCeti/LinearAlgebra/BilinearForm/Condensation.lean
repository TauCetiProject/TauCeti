/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.Matrix.Condensation
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# The condensed form of a bilinear form

For a bilinear form `B` and a vector `v`, the corresponding *condensed form* is

```text
S(x, y) = B(v, v) · B(x, y) - B(x, v) · B(v, y).
```

It is symmetric when `B` is, and it vanishes when either argument is `v`, so it does not change
when multiples of `v` are added to its arguments. If `B` is positive definite, `S` is positive on
the nonzero vectors of the kernel of any linear functional that does not vanish at `v`; this is the
strict Cauchy–Schwarz inequality. If `v` is the first vector of a basis `c`, the Gram matrix of `S`
on the other basis vectors is the condensation of the Gram matrix of `B` in `c`, so Chiò's identity
(`Matrix.mul_det_condensation_eq_pow_mul_det`) computes its determinant. That is the inductive step
of Hermite's inequality for the minimum of a positive definite quadratic form over `ℤ`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isSymm_forall_apply_eq`: the condensed form of a symmetric
  form, read on any module through a linear map, is a symmetric form.
* `LinearMap.BilinForm.mul_apply_add_smul_add_smul`: completing the square along `v`,
  `B(v, v) B(x + s v, y + t v) = B(x + s v, v) B(v, y + t v) + S(x, y)`.
* `LinearMap.BilinForm.apply_mul_apply_lt_of_mem_ker`: for `B` positive definite, the condensed
  form is positive on the nonzero vectors of the kernel of a functional not vanishing at `v`.
* `LinearMap.BilinForm.mul_det_toMatrix_eq_pow_mul_det_toMatrix`: Chiò's identity for Gram
  matrices, `B(v, v) · det S = B(v, v)ⁿ · det B`.
-/

public section

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
be positive definite over an ordered ring. If a linear functional `f` does
not vanish at `v`, then every nonzero `x` in its kernel satisfies
`B(x, v) B(v, x) < B(v, v) B(x, x)`. This is the strict Cauchy–Schwarz inequality, since `v` and
`x` are linearly independent. -/
theorem apply_mul_apply_lt_of_mem_ker [LinearOrder R] [IsStrictOrderedRing R]
    {B : LinearMap.BilinForm R M} (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    {f : M →ₗ[R] R} {v x : M} (hv : f v ≠ 0) (hx : x ∈ LinearMap.ker f) (hx0 : x ≠ 0) :
    B x v * B v x < B v v * B x x := by
  have := LinearMap.BilinForm.isTorsionFree_of_pos hpos
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
