/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.ExteriorPower.SesquilinearForm

import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Symmetry and positivity of the exterior-power Gram form

Let `V` be an inner product space over `𝕜 = ℝ` or `ℂ` (not necessarily finite-dimensional). Its
exterior power `⋀[𝕜]^n V` carries the basis-free Gram hermitian form
`(innerₛₗ 𝕜).sesqExteriorPower n`, conjugate-linear in the first argument, whose value on
decomposable vectors is the Gram determinant `det (⟪vᵢ, wⱼ⟫)`
(`LinearMap.sesqExteriorPower_ιMulti_ιMulti`). Over `ℂ` it is the complex counterpart of Mathlib's
inner product on the exterior powers of a real inner product space.

This module proves that `(innerₛₗ 𝕜).sesqExteriorPower n` is hermitian and positive definite
without any finite-dimensionality assumption on `V`, by reducing to a finitely generated submodule
and identifying `(innerₛₗ 𝕜).sesqExteriorPower n` with the wedge-basis form of its standard
orthonormal basis.

## Main results

* `exteriorPower.isSymm_sesqExteriorPower_innerₛₗ`: `(innerₛₗ 𝕜).sesqExteriorPower n` is
  hermitian.
* `exteriorPower.sesqExteriorPower_innerₛₗ_self_nonneg`:
  `0 ≤ (innerₛₗ 𝕜).sesqExteriorPower n x x`.
* `exteriorPower.sesqExteriorPower_innerₛₗ_self_eq_zero_iff`:
  `(innerₛₗ 𝕜).sesqExteriorPower n x x = 0 ↔ x = 0`.
* `exteriorPower.sesqExteriorPower_innerₛₗ_self_pos`:
  `0 < (innerₛₗ 𝕜).sesqExteriorPower n x x` for `x ≠ 0`.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
-/

public noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace exteriorPower

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The exterior-power Gram form `(innerₛₗ 𝕜).sesqExteriorPower n` is hermitian. -/
theorem isSymm_sesqExteriorPower_innerₛₗ (n : ℕ) :
    ((innerₛₗ 𝕜 : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜).sesqExteriorPower n).IsSymm :=
  LinearMap.IsSymm.sesqExteriorPower star_involutive
    (LinearMap.isSymm_def.mpr fun x y ↦ by simp [inner_conj_symm]) n

/-- The exterior-power Gram form `(innerₛₗ 𝕜).sesqExteriorPower n` is positive semidefinite
(without any finite-dimensionality assumption on `V`). -/
theorem sesqExteriorPower_innerₛₗ_self_nonneg (n : ℕ) (x : ⋀[𝕜]^n V) :
    0 ≤ (innerₛₗ 𝕜).sesqExteriorPower n x x := by
  obtain ⟨W, _, y, rfl⟩ := exists_finite_mem_range_map x
  let b := stdOrthonormalBasis 𝕜 W
  have hsub : ∀ u v : W, innerₛₗ 𝕜 (W.subtype u) (W.subtype v) = innerₛₗ 𝕜 u v :=
    fun u v ↦ by simp [Submodule.coe_inner]
  rw [LinearMap.sesqExteriorPower_map_map hsub, ← b.toLinearMapₛₗ₂_one_eq_innerₛₗ,
    ← b.toBasis.toLinearMapₛₗ₂_exteriorPower_one]
  exact Matrix.toLinearMapₛₗ₂_one_self_nonneg _ _

/-- The exterior-power Gram form `(innerₛₗ 𝕜).sesqExteriorPower n` is definite: an element
has zero self-pairing if and only if it is zero (without any finite-dimensionality assumption on
`V`). -/
@[simp]
theorem sesqExteriorPower_innerₛₗ_self_eq_zero_iff {n : ℕ} {x : ⋀[𝕜]^n V} :
    (innerₛₗ 𝕜).sesqExteriorPower n x x = 0 ↔ x = 0 := by
  obtain ⟨W, _, y, rfl⟩ := exists_finite_mem_range_map x
  let b := stdOrthonormalBasis 𝕜 W
  have hsub : ∀ u v : W, innerₛₗ 𝕜 (W.subtype u) (W.subtype v) = innerₛₗ 𝕜 u v :=
    fun u v ↦ by simp [Submodule.coe_inner]
  rw [LinearMap.sesqExteriorPower_map_map hsub, ← b.toLinearMapₛₗ₂_one_eq_innerₛₗ,
    ← b.toBasis.toLinearMapₛₗ₂_exteriorPower_one, Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff,
    ← (map_injective_field W.subtype_injective).eq_iff, map_zero]

/-- The exterior-power Gram form `(innerₛₗ 𝕜).sesqExteriorPower n` is positive definite (without
any finite-dimensionality assumption on `V`). -/
theorem sesqExteriorPower_innerₛₗ_self_pos {n : ℕ} {x : ⋀[𝕜]^n V} (hx : x ≠ 0) :
    0 < (innerₛₗ 𝕜).sesqExteriorPower n x x :=
  (sesqExteriorPower_innerₛₗ_self_nonneg n x).lt_of_ne'
    (sesqExteriorPower_innerₛₗ_self_eq_zero_iff.not.mpr hx)

end exteriorPower
