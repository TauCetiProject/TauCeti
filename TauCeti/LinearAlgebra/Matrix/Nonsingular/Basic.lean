/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices with a right inverse up to a regular scalar and basis-transfer nonsingularity

If `M * J = c • 1` for a left-regular scalar `c`, then `M` is injective on vectors, even though it
need not be invertible: `c • 1` is right-regular, hence so is `M`, and for square matrices over a
commutative semiring with cancellative addition right and left regularity agree.

For a linear map `ψ : M →ₗ[R] N` between finite-rank free `R`-modules with bases `v`, `w`, if a
semilinear map `f : N →ₛₗ[σ] V` into an `S`-module carries `ψ ∘ v` to an `S`-linearly independent
family, then the mapped transition matrix `σ.mapMatrix (LinearMap.toMatrix v w ψ)` has `S`-linearly
independent columns and is therefore nonsingular (`Matrix.Nonsingular.of_linearIndependent_col`).
Over commutative rings this forces `σ (LinearMap.toMatrix v w ψ).det` to be a non-zero-divisor (and
hence nonzero when `S` is nontrivial, forcing `(LinearMap.toMatrix v w ψ).det ≠ 0` as well).

## Main results

* `Matrix.mulVec_injective_of_mul_eq_smul_one`: `M * J = c • 1` with `c` left-regular forces
  `M.mulVec` to be injective.
* `LinearMap.nonsingular_mapMatrix_toMatrix_of_linearIndependent`: if `f ∘ ψ ∘ v` is `S`-linearly
  independent for a semilinear map `f : N →ₛₗ[σ] V`, then
  `σ.mapMatrix (LinearMap.toMatrix v w ψ)` is nonsingular.
* `LinearMap.map_det_toMatrix_mem_nonZeroDivisors_of_linearIndependent`: over commutative rings,
  `σ (LinearMap.toMatrix v w ψ).det ∈ nonZeroDivisors S`.
* `LinearMap.map_det_toMatrix_ne_zero_of_linearIndependent`: over nontrivial `S`,
  `σ (LinearMap.toMatrix v w ψ).det ≠ 0`.
* `LinearMap.det_toMatrix_ne_zero_of_linearIndependent`: over nontrivial `S`,
  `(LinearMap.toMatrix v w ψ).det ≠ 0`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R] [IsCancelAdd R]

/-- If `M * J = c • 1` for a left-regular scalar `c`, then multiplication of vectors by `M` is
injective. -/
theorem mulVec_injective_of_mul_eq_smul_one {c : R} (hc : IsLeftRegular c) {M J : Matrix n n R}
    (h : M * J = c • (1 : Matrix n n R)) : Function.Injective M.mulVec := by
  rw [← isLeftRegular_iff_mulVec_injective, isLeftRegular_iff_isRightRegular]
  refine IsRightRegular.of_mul (a := J) fun X Y hXY ↦ ext fun i j ↦ hc ?_
  simpa [h, mul_comm c] using congr_fun₂ hXY i j

end Matrix

namespace LinearMap

section CommSemiring

variable {ι R S M N V : Type*} [Fintype ι] [DecidableEq ι]
variable [CommSemiring R] [CommSemiring S]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid V]
variable [Module R M] [Module R N] [Module S V]

/-- **Nonsingularity of a mapped transition matrix from linear independence**: given bases `v` of
`M` and `w` of `N` over `R`, a linear map `ψ : M →ₗ[R] N`, and a semilinear map `f : N →ₛₗ[σ] V`
along `σ : R →+* S`, if `i ↦ f (ψ (v i))` is `S`-linearly independent in `V`, then the mapped
transition matrix `σ.mapMatrix (LinearMap.toMatrix v w ψ)` is nonsingular. -/
theorem nonsingular_mapMatrix_toMatrix_of_linearIndependent {σ : R →+* S}
    (v : Module.Basis ι R M) (w : Module.Basis ι R N) (ψ : M →ₗ[R] N) (f : N →ₛₗ[σ] V)
    (hli : LinearIndependent S fun i ↦ f (ψ (v i))) :
    (σ.mapMatrix (LinearMap.toMatrix v w ψ)).Nonsingular := by
  refine Matrix.Nonsingular.of_linearIndependent_col <|
    LinearIndependent.of_comp (Fintype.linearCombination S fun j ↦ f (w j)) ?_
  rwa [show (Fintype.linearCombination S fun j ↦ f (w j)) ∘
      (σ.mapMatrix (LinearMap.toMatrix v w ψ)).col = fun i ↦ f (ψ (v i)) from funext fun i ↦ by
    simp only [Function.comp_apply, Fintype.linearCombination_apply, Matrix.col_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, ← f.map_smulₛₗ,
      ← map_sum, w.sum_repr]]

end CommSemiring

section CommRing

variable {ι R S M N V : Type*} [Fintype ι] [DecidableEq ι]
variable [CommRing R] [CommRing S]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid V]
variable [Module R M] [Module R N] [Module S V]

/-- **Non-zero-divisor determinant of a mapped transition matrix**: under the hypotheses of
`LinearMap.nonsingular_mapMatrix_toMatrix_of_linearIndependent` over commutative rings `R` and `S`,
`σ (LinearMap.toMatrix v w ψ).det` is a non-zero-divisor in `S`. -/
theorem map_det_toMatrix_mem_nonZeroDivisors_of_linearIndependent {σ : R →+* S}
    (v : Module.Basis ι R M) (w : Module.Basis ι R N) (ψ : M →ₗ[R] N) (f : N →ₛₗ[σ] V)
    (hli : LinearIndependent S fun i ↦ f (ψ (v i))) :
    σ (LinearMap.toMatrix v w ψ).det ∈ nonZeroDivisors S :=
  RingHom.map_det σ (LinearMap.toMatrix v w ψ) ▸ Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
    (nonsingular_mapMatrix_toMatrix_of_linearIndependent v w ψ f hli)

/-- **Nonvanishing mapped determinant of a transition matrix**: if `S` is nontrivial and
`i ↦ f (ψ (v i))` is `S`-linearly independent for a semilinear map `f : N →ₛₗ[σ] V`, then
`σ (LinearMap.toMatrix v w ψ).det ≠ 0`. -/
theorem map_det_toMatrix_ne_zero_of_linearIndependent [Nontrivial S] {σ : R →+* S}
    (v : Module.Basis ι R M) (w : Module.Basis ι R N) (ψ : M →ₗ[R] N) (f : N →ₛₗ[σ] V)
    (hli : LinearIndependent S fun i ↦ f (ψ (v i))) :
    σ (LinearMap.toMatrix v w ψ).det ≠ 0 :=
  nonZeroDivisors.ne_zero (map_det_toMatrix_mem_nonZeroDivisors_of_linearIndependent v w ψ f hli)

/-- **Nonvanishing determinant of a transition matrix**: if `S` is nontrivial and `i ↦ f (ψ (v i))`
is `S`-linearly independent for a semilinear map `f : N →ₛₗ[σ] V`, then
`(LinearMap.toMatrix v w ψ).det ≠ 0`. -/
theorem det_toMatrix_ne_zero_of_linearIndependent [Nontrivial S] {σ : R →+* S}
    (v : Module.Basis ι R M) (w : Module.Basis ι R N) (ψ : M →ₗ[R] N) (f : N →ₛₗ[σ] V)
    (hli : LinearIndependent S fun i ↦ f (ψ (v i))) :
    (LinearMap.toMatrix v w ψ).det ≠ 0 :=
  fun h ↦ map_det_toMatrix_ne_zero_of_linearIndependent v w ψ f hli (by rw [h, map_zero])

end CommRing

end LinearMap
