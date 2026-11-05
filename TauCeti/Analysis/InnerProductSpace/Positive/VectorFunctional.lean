/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Vector functionals as positive linear maps

On a real or complex inner product space `E`, pairing an operator against a fixed vector `ξ : E`
defines the functional `T ↦ ⟪ξ, T ξ⟫_𝕜`. Because a positive operator is symmetric with nonnegative
quadratic form in the Loewner partial order, this pairing is a `PositiveLinearMap` both on
algebraic endomorphisms `E →ₗ[𝕜] E` and on bounded operators `E →L[𝕜] E`, without assuming that
`E` is complete or finite-dimensional.

Evaluating at the identity gives `(‖ξ‖ ^ 2 : 𝕜)`, so a unit vector `‖ξ‖ = 1` determines a
normalized positive functional (a vector state when `E` is a complex Hilbert space).

## Main definitions

* `LinearMap.innerPositiveLinearMap 𝕜 ξ`: the positive linear functional `T ↦ ⟪ξ, T ξ⟫_𝕜` on
  `E →ₗ[𝕜] E`.
* `ContinuousLinearMap.innerPositiveLinearMap 𝕜 ξ`: the positive linear functional `T ↦ ⟪ξ, T ξ⟫_𝕜`
  on `E →L[𝕜] E`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open scoped ComplexOrder InnerProductSpace

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The vector functional `T ↦ ⟪ξ, T ξ⟫_𝕜` on `E →ₗ[𝕜] E` as a positive linear map for the
Loewner order. -/
def innerPositiveLinearMap (ξ : E) : (E →ₗ[𝕜] E) →ₚ[𝕜] 𝕜 :=
  PositiveLinearMap.mk₀
    { toFun T := ⟪ξ, T ξ⟫_𝕜
      map_add' S T := by simp [inner_add_right]
      map_smul' c T := by simp [inner_smul_right] }
    fun _ hT => (nonneg_iff_isPositive.mp hT).inner_nonneg_right ξ

@[simp]
theorem innerPositiveLinearMap_apply (ξ : E) (T : E →ₗ[𝕜] E) :
    innerPositiveLinearMap 𝕜 ξ T = ⟪ξ, T ξ⟫_𝕜 :=
  (rfl)

theorem innerPositiveLinearMap_one (ξ : E) :
    innerPositiveLinearMap 𝕜 ξ 1 = (‖ξ‖ ^ 2 : 𝕜) := by
  simp [inner_self_eq_norm_sq_to_K]

@[simp]
theorem innerPositiveLinearMap_zero_vector :
    innerPositiveLinearMap 𝕜 (0 : E) = 0 := by
  ext T
  simp

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The vector functional `T ↦ ⟪ξ, T ξ⟫_𝕜` on bounded operators `E →L[𝕜] E` as a positive linear
map for the Loewner order. When `E` is a complex Hilbert space and `‖ξ‖ = 1`, this is the vector
state associated with `ξ`. -/
def innerPositiveLinearMap (ξ : E) : (E →L[𝕜] E) →ₚ[𝕜] 𝕜 :=
  PositiveLinearMap.mk₀
    { toFun T := ⟪ξ, T ξ⟫_𝕜
      map_add' S T := by simp [inner_add_right]
      map_smul' c T := by simp [inner_smul_right] }
    fun _ hT => (nonneg_iff_isPositive.mp hT).inner_nonneg_right ξ

@[simp]
theorem innerPositiveLinearMap_apply (ξ : E) (T : E →L[𝕜] E) :
    innerPositiveLinearMap 𝕜 ξ T = ⟪ξ, T ξ⟫_𝕜 :=
  (rfl)

theorem innerPositiveLinearMap_one (ξ : E) :
    innerPositiveLinearMap 𝕜 ξ 1 = (‖ξ‖ ^ 2 : 𝕜) := by
  simp [inner_self_eq_norm_sq_to_K]

@[simp]
theorem innerPositiveLinearMap_zero_vector :
    innerPositiveLinearMap 𝕜 (0 : E) = 0 := by
  ext T
  simp

/-- The vector functional at `ξ` is bounded by `‖ξ‖ ^ 2` in operator norm. -/
theorem norm_innerPositiveLinearMap_apply_le (ξ : E) (T : E →L[𝕜] E) :
    ‖innerPositiveLinearMap 𝕜 ξ T‖ ≤ ‖ξ‖ ^ 2 * ‖T‖ := by
  calc ‖⟪ξ, T ξ⟫_𝕜‖ ≤ ‖ξ‖ * ‖T ξ‖ := norm_inner_le_norm ξ (T ξ)
    _ ≤ ‖ξ‖ * (‖T‖ * ‖ξ‖) := by gcongr; exact T.le_opNorm ξ
    _ = ‖ξ‖ ^ 2 * ‖T‖ := by ring

end ContinuousLinearMap
