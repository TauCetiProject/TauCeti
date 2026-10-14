/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.SymmetricFunctionalCalculus

/-!
# Positive square roots and the finite-dimensional operator modulus

A positive endomorphism of a finite-dimensional real or complex inner product space has a unique
positive square root.  It is obtained by applying the finite symmetric functional calculus to
`Real.sqrt`.  This file develops its kernel, range, norm, and uniqueness properties, then applies
the construction to the source Gram operator `A† A` of a rectangular map.

The resulting `LinearMap.operatorAbs A` is the finite-dimensional operator modulus.  Its square is
`A† A`, it has the same pointwise norms and kernel as `A`, and its range is `(ker A)ᗮ`.  A normal
endomorphism commutes with its modulus.  These facts are the spectral input to finite-dimensional
polar decomposition.

## Main declarations

* `LinearMap.IsPositive.sqrt`: the positive square root of a positive endomorphism.
* `LinearMap.IsPositive.sqrt_sq`: its square is the original endomorphism.
* `LinearMap.IsPositive.sqrt_unique`: uniqueness among positive square roots.
* `LinearMap.operatorAbs`: the modulus `sqrt (A† A)` of a rectangular linear map.
* `LinearMap.IsPositive.eq_operatorAbs`: uniqueness among positive square roots of `A† A`.
* `LinearMap.norm_operatorAbs_apply`: `‖|A|x‖ = ‖Ax‖`.
* `LinearMap.ker_operatorAbs`, `LinearMap.range_operatorAbs`: the kernel and range of the modulus.
* `LinearMap.commute_operatorAbs`: a normal endomorphism commutes with its modulus.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorems 7.2.6 and 7.3.1.
-/

public section

open Module.End InnerProductSpace
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {T S : E →ₗ[𝕜] E}

namespace IsPositive

/-- The positive square root of a positive endomorphism, defined by the finite symmetric
functional calculus at `Real.sqrt`. -/
noncomputable def sqrt (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  hT.isSymmetric.cfc Real.sqrt

/-- The positive square root acts on an eigenvector by the square root of its eigenvalue. -/
theorem sqrt_apply_of_apply_eq_smul (hT : T.IsPositive) {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) : hT.sqrt x = (√μ : 𝕜) • x :=
  hT.isSymmetric.cfc_apply_of_apply_eq_smul Real.sqrt hx

/-- The positive square root acts diagonally on the ordered eigenbasis. -/
@[simp]
theorem sqrt_apply_eigenvectorBasis (hT : T.IsPositive) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.sqrt (hT.isSymmetric.eigenvectorBasis hn i) =
      (√(hT.isSymmetric.eigenvalues hn i) : 𝕜) • hT.isSymmetric.eigenvectorBasis hn i :=
  hT.sqrt_apply_of_apply_eq_smul (hT.isSymmetric.apply_eigenvectorBasis hn i)

/-- The square root of a positive endomorphism is positive. -/
theorem sqrt_isPositive (hT : T.IsPositive) : hT.sqrt.IsPositive := by
  let R := hT.isSymmetric.cfc fun μ ↦ √√μ
  have hR : R.IsSymmetric := hT.isSymmetric.isSymmetric_cfc _
  have hsq : R.adjoint ∘ₗ R = hT.sqrt := by
    rw [hR.adjoint_eq]
    refine (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
    rw [OrthonormalBasis.coe_toBasis, comp_apply]
    simp only [R, hT.isSymmetric.cfc_apply_eigenvectorBasis, map_smul, smul_smul,
      ← RCLike.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
    exact (hT.sqrt_apply_eigenvectorBasis rfl i).symm
  rw [← hsq]
  exact isPositive_adjoint_comp_self R

/-- The positive square root is symmetric. -/
theorem sqrt_isSymmetric (hT : T.IsPositive) : hT.sqrt.IsSymmetric :=
  hT.sqrt_isPositive.isSymmetric

/-- The square of the positive square root is the original endomorphism. -/
@[simp]
theorem sqrt_sq (hT : T.IsPositive) : hT.sqrt ∘ₗ hT.sqrt = T := by
  refine (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  simp [smul_smul, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i),
    hT.isSymmetric.apply_eigenvectorBasis]

/-- The squared norm of `sqrt T x` is the quadratic form of `T` at `x`. -/
theorem norm_sqrt_apply_sq (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, ← hT.sqrt_isSymmetric (hT.sqrt x) x,
    ← comp_apply, hT.sqrt_sq]

/-- The positive square root has the same kernel as the original endomorphism. -/
@[simp]
theorem ker_sqrt (hT : T.IsPositive) : hT.sqrt.ker = T.ker := by
  ext x
  simp only [mem_ker]
  constructor
  · intro hx
    rw [← hT.sqrt_sq, comp_apply, hx, map_zero]
  · intro hx
    have hsquare : ‖hT.sqrt x‖ ^ 2 = 0 := by
      rw [hT.norm_sqrt_apply_sq, hx, inner_zero_left, map_zero]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- The positive square root has the same range as the original endomorphism. -/
@[simp]
theorem range_sqrt (hT : T.IsPositive) : hT.sqrt.range = T.range := by
  calc
    hT.sqrt.range = hT.sqrt.adjoint.range := by rw [hT.sqrt_isPositive.adjoint_eq]
    _ = hT.sqrt.kerᗮ := hT.sqrt.orthogonal_ker.symm
    _ = T.kerᗮ := by rw [hT.ker_sqrt]
    _ = T.adjoint.range := T.orthogonal_ker
    _ = T.range := by rw [hT.adjoint_eq]

/-- The positive square root is a unit exactly when the original endomorphism is a unit. -/
@[simp]
theorem sqrt_isUnit_iff (hT : T.IsPositive) : IsUnit hT.sqrt ↔ IsUnit T := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.isUnit_iff_ker_eq_bot, hT.ker_sqrt]

/-- The positive square root is unique among positive endomorphisms whose square is `T`. -/
theorem sqrt_unique (hT : T.IsPositive) (hS : S.IsPositive) (hST : S ∘ₗ S = T) :
    S = hT.sqrt := by
  refine (hS.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  have hSe := hS.isSymmetric.apply_eigenvectorBasis rfl i
  have hTe : T (hS.isSymmetric.eigenvectorBasis rfl i) =
      ((hS.isSymmetric.eigenvalues rfl i ^ 2 : ℝ) : 𝕜) • hS.isSymmetric.eigenvectorBasis rfl i := by
    simp [← hST, hSe, smul_smul, sq]
  simp [hSe, hT.sqrt_apply_of_apply_eq_smul hTe, Real.sqrt_sq (hS.nonneg_eigenvalues rfl i)]

end IsPositive

/-- The finite-dimensional modulus of a rectangular linear map is the positive square root of
its source Gram operator `A† A`. -/
noncomputable def operatorAbs (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  (isPositive_adjoint_comp_self A).sqrt

/-- The finite-dimensional modulus is positive. -/
theorem isPositive_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.IsPositive :=
  (isPositive_adjoint_comp_self A).sqrt_isPositive

/-- The finite-dimensional modulus is symmetric. -/
theorem isSymmetric_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.IsSymmetric :=
  A.isPositive_operatorAbs.isSymmetric

/-- The square of the finite-dimensional modulus is the source Gram operator. -/
@[simp]
theorem operatorAbs_sq (A : E →ₗ[𝕜] F) :
    A.operatorAbs ∘ₗ A.operatorAbs = A.adjoint ∘ₗ A :=
  (isPositive_adjoint_comp_self A).sqrt_sq

/-- The modulus is the unique positive endomorphism whose square is the source Gram operator
`A† A`. -/
theorem IsPositive.eq_operatorAbs {A : E →ₗ[𝕜] F} {S : E →ₗ[𝕜] E} (hS : S.IsPositive)
    (h : S ∘ₗ S = A.adjoint ∘ₗ A) : S = A.operatorAbs :=
  (isPositive_adjoint_comp_self A).sqrt_unique hS h

/-- The modulus and the original map have the same pointwise norms. -/
@[simp]
theorem norm_operatorAbs_apply (A : E →ₗ[𝕜] F) (x : E) :
    ‖A.operatorAbs x‖ = ‖A x‖ := by
  rw [operatorAbs, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    (isPositive_adjoint_comp_self A).norm_sqrt_apply_sq]
  simp only [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The modulus and the original map have the same kernel. -/
@[simp]
theorem ker_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.ker = A.ker := by
  rw [operatorAbs, (isPositive_adjoint_comp_self A).ker_sqrt, ker_adjoint_comp_self]

/-- The range of the modulus is the orthogonal complement of the original map's kernel. -/
@[simp]
theorem range_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.range = A.kerᗮ := by
  rw [operatorAbs, (isPositive_adjoint_comp_self A).range_sqrt,
    range_adjoint_comp_self, ← orthogonal_ker]

/-- A normal finite-dimensional endomorphism commutes with its modulus. -/
theorem commute_operatorAbs (A : E →ₗ[𝕜] E) [IsStarNormal A] :
    Commute A A.operatorAbs := by
  have hA : Commute A (A.adjoint ∘ₗ A) := by
    simpa only [Module.End.mul_eq_comp, star_eq_adjoint] using
      star_comm_self.symm.mul_right (Commute.refl A)
  simpa only [operatorAbs, IsPositive.sqrt] using
    (isSymmetric_adjoint_comp_self A).commute_cfc hA Real.sqrt

end LinearMap
