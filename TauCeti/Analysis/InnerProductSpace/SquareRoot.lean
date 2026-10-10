/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SymmetricFunctionalCalculus

/-!
# The positive square root of a positive operator in finite dimension

Let `T` be a positive endomorphism of a finite-dimensional inner product space `E` over `ℝ` or
`ℂ` (any `RCLike` field `𝕜`). Its **positive square root** `√T` is the functional calculus of `T`
at `Real.sqrt`: on an orthonormal eigenbasis `(eᵢ)` of `T` with (nonnegative) eigenvalues `(λᵢ)`
it acts by `eᵢ ↦ √λᵢ • eᵢ`. This file defines it as `LinearMap.IsPositive.sqrt` and proves that
it is the unique positive operator whose square is `T`, together with the properties of `√T`
that the operator modulus `|A| = √(A†A)` and the polar decomposition are built from: `√T` has the
same kernel and the same range as `T`, `‖√T x‖² = re ⟪T x, x⟫`, `√T` is invertible exactly
when `T` is, and `√T` commutes with every operator commuting with `T`.

The construction works uniformly over `RCLike` scalars, so it applies to real inner product
spaces, where Mathlib's continuous functional calculus for bounded operators (and with it
`CFC.sqrt`) is not available. The names of the algebraic lemmas follow `CFC.sqrt`.

## Main declarations

* `LinearMap.IsPositive.sqrt`: the positive square root `√T` of a positive operator `T`.
* `LinearMap.IsPositive.isPositive_sqrt`, `LinearMap.IsPositive.sqrt_mul_sqrt_self`: `√T` is
  positive and `√T * √T = T`.
* `LinearMap.IsPositive.sqrt_unique`, `LinearMap.IsPositive.sqrt_eq_iff`: `√T` is the only
  positive operator whose square is `T`.
* `LinearMap.IsPositive.norm_sqrt_apply_sq`: `‖√T x‖² = re ⟪T x, x⟫`.
* `LinearMap.IsPositive.ker_sqrt`, `LinearMap.IsPositive.range_sqrt`: `√T` and `T` have the
  same kernel and the same range.
* `LinearMap.IsPositive.isUnit_sqrt_iff`: `√T` is invertible if and only if `T` is.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 7.2.6 (the unique positive semidefinite square root).
-/

public section

open Module.End RCLike
open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- The **positive square root** `√T` of a positive operator `T` on a finite-dimensional inner
product space: the functional calculus of `T` at `Real.sqrt`. It acts by `√λ` on the eigenvectors
of `T` with eigenvalue `λ` (`sqrt_apply_of_apply_eq_smul`), and it is the unique positive
operator whose square is `T` (`sqrt_eq_iff`). -/
noncomputable def sqrt (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  hT.isSymmetric.cfc Real.sqrt

theorem sqrt_def (hT : T.IsPositive) : hT.sqrt = hT.isSymmetric.cfc Real.sqrt :=
  (rfl)

/-- If `Tx = μx`, then `√T x = √μ x`. -/
theorem sqrt_apply_of_apply_eq_smul (hT : T.IsPositive) {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) : hT.sqrt x = (√μ : 𝕜) • x :=
  hT.isSymmetric.cfc_apply_of_apply_eq_smul _ hx

/-- The square root acts diagonally on every ordered eigenbasis of `T`. -/
@[simp]
theorem sqrt_apply_eigenvectorBasis (hT : T.IsPositive) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) :
    hT.sqrt (hT.isSymmetric.eigenvectorBasis hn i) =
      (√(hT.isSymmetric.eigenvalues hn i) : 𝕜) • hT.isSymmetric.eigenvectorBasis hn i :=
  hT.isSymmetric.cfc_apply_eigenvectorBasis hn _ i

/-- The square root of a positive operator is symmetric. -/
theorem isSymmetric_sqrt (hT : T.IsPositive) : hT.sqrt.IsSymmetric :=
  hT.isSymmetric.isSymmetric_cfc _

/-- The square root of a positive operator is positive. -/
theorem isPositive_sqrt (hT : T.IsPositive) : hT.sqrt.IsPositive :=
  hT.isSymmetric.isPositive_cfc fun _ _ ↦ Real.sqrt_nonneg _

/-- **The square-root equation** `√T * √T = T`. -/
@[simp]
theorem sqrt_mul_sqrt_self (hT : T.IsPositive) : hT.sqrt * hT.sqrt = T := by
  rw [sqrt_def, ← hT.isSymmetric.cfc_mul]
  conv_rhs => rw [← hT.isSymmetric.cfc_id]
  exact hT.isSymmetric.cfc_congr fun μ hμ ↦ Real.mul_self_sqrt
    (eigenvalue_nonneg_of_nonneg hμ hT.re_inner_nonneg_right)

/-- **The square-root equation** `(√T)² = T`. -/
@[simp]
theorem sq_sqrt (hT : T.IsPositive) : hT.sqrt ^ 2 = T := by
  rw [sq, sqrt_mul_sqrt_self]

/-- The square-root equation `√T (√T x) = T x`, evaluated at a vector. -/
@[simp]
theorem sqrt_sqrt_apply (hT : T.IsPositive) (x : E) : hT.sqrt (hT.sqrt x) = T x := by
  rw [← Module.End.mul_apply, sqrt_mul_sqrt_self]

/-- **Uniqueness of the positive square root.** A positive operator `S` with `S * S = T` is the
square root of `T`. -/
theorem sqrt_unique (hT : T.IsPositive) (hS : S.IsPositive) (h : S * S = T) : hT.sqrt = S := by
  -- Compare both sides on an eigenbasis of `S`: if `S v = s v`, then `T v = s² v`, so
  -- `√T v = √(s²) v = s v` because `s ≥ 0`.
  refine (hS.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  have hv := hS.isSymmetric.apply_eigenvectorBasis rfl i
  have hTv : T (hS.isSymmetric.eigenvectorBasis rfl i) =
      ((hS.isSymmetric.eigenvalues rfl i * hS.isSymmetric.eigenvalues rfl i : ℝ) : 𝕜) •
        hS.isSymmetric.eigenvectorBasis rfl i := by
    rw [← h, Module.End.mul_apply, hv, map_smul, hv, smul_smul, ofReal_mul]
  rw [OrthonormalBasis.coe_toBasis, hT.sqrt_apply_of_apply_eq_smul hTv,
    Real.sqrt_mul_self (hS.nonneg_eigenvalues rfl i), hv]

/-- **Characterization of the positive square root.** `√T` is the unique positive operator whose
square is `T`. -/
theorem sqrt_eq_iff (hT : T.IsPositive) : hT.sqrt = S ↔ S.IsPositive ∧ S * S = T :=
  ⟨fun h ↦ h ▸ ⟨hT.isPositive_sqrt, hT.sqrt_mul_sqrt_self⟩,
    fun h ↦ hT.sqrt_unique h.1 h.2⟩

/-- The square root of the zero operator is zero. -/
@[simp]
theorem sqrt_zero : (isPositive_zero : (0 : E →ₗ[𝕜] E).IsPositive).sqrt = 0 :=
  isPositive_zero.sqrt_unique isPositive_zero (mul_zero 0)

/-- The square root of the identity operator is the identity. -/
@[simp]
theorem sqrt_one : (isPositive_one : (1 : E →ₗ[𝕜] E).IsPositive).sqrt = 1 :=
  isPositive_one.sqrt_unique isPositive_one (mul_one 1)

/-- The square root of `T` vanishes exactly when `T` does. -/
@[simp]
theorem sqrt_eq_zero_iff (hT : T.IsPositive) : hT.sqrt = 0 ↔ T = 0 := by
  rw [sqrt_eq_iff, mul_zero, eq_comm]
  exact and_iff_right isPositive_zero

/-- **The square-root norm identity** `‖√T x‖² = re ⟪T x, x⟫`. -/
theorem norm_sqrt_apply_sq (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = re ⟪T x, x⟫_𝕜 := by
  rw [← hT.sqrt_sqrt_apply, hT.isSymmetric_sqrt, inner_self_eq_norm_sq]

/-- The square root of `T` has the same kernel as `T`. -/
@[simp]
theorem ker_sqrt (hT : T.IsPositive) : LinearMap.ker hT.sqrt = LinearMap.ker T := by
  ext x
  simp only [LinearMap.mem_ker]
  refine ⟨fun h ↦ by rw [← hT.sqrt_sqrt_apply, h, map_zero], fun h ↦ ?_⟩
  rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, hT.norm_sqrt_apply_sq, h, inner_zero_left,
    map_zero]

/-- The square root of `T` has the same range as `T`. -/
@[simp]
theorem range_sqrt (hT : T.IsPositive) : LinearMap.range hT.sqrt = LinearMap.range T := by
  -- `range T ≤ range √T` because `T = √T √T`, and the two ranges have the same dimension by
  -- rank–nullity, since the kernels agree.
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rintro _ ⟨x, rfl⟩
    exact ⟨hT.sqrt x, hT.sqrt_sqrt_apply x⟩
  · have h₁ := hT.sqrt.finrank_range_add_finrank_ker
    have h₂ := T.finrank_range_add_finrank_ker
    rw [hT.ker_sqrt] at h₁
    omega

/-- The square root of `T` is invertible if and only if `T` is. -/
@[simp]
theorem isUnit_sqrt_iff (hT : T.IsPositive) : IsUnit hT.sqrt ↔ IsUnit T := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.isUnit_iff_ker_eq_bot, ker_sqrt]

/-- Every operator commuting with `T` commutes with `√T`. -/
theorem commute_sqrt (hT : T.IsPositive) (hS : Commute S T) : Commute S hT.sqrt :=
  hT.isSymmetric.commute_cfc hS _

end LinearMap.IsPositive
