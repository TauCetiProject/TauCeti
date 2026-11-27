/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric

import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates

/-!
# The Gram hermitian form on exterior powers of an inner product space

Let `V` be a finite-dimensional inner product space over `𝕜 = ℝ` or `ℂ`. Its exterior power
`⋀[𝕜]^n V` carries the hermitian form `exteriorPower.gramSesqForm n`, conjugate-linear in the
first argument, whose value on decomposable vectors is the Gram determinant

  `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det (⟪vᵢ, wⱼ⟫)`

(`exteriorPower.gramSesqForm_ιMulti_ιMulti`). It is hermitian and positive definite, and these
values determine it (`exteriorPower.eq_gramSesqForm_of_ιMulti`). Over `ℂ` it is the complex
counterpart of Mathlib's inner product on the exterior powers of a real inner product space.
For a vector bundle with a hermitian metric, it gives the metric on exterior powers, in
particular on the determinant line, fibre by fibre.

The form is built from an orthonormal basis `b` of `V`: it is the restriction to `⋀[𝕜]^n V` of
the hermitian form on the exterior algebra for which the increasing wedges of `b` are orthonormal.
By the Gram-determinant formula the result does not depend on `b`.

## Main definitions

* `exteriorPower.gramSesqForm n`: the Gram hermitian form on `⋀[𝕜]^n V`.

## Main results

* `exteriorPower.gramSesqForm_ιMulti_ιMulti`: the Gram-determinant formula.
* `exteriorPower.isSymm_gramSesqForm`: the form is hermitian.
* `exteriorPower.gramSesqForm_self_pos`: the form is positive definite.
* `exteriorPower.eq_gramSesqForm_of_ιMulti`: a sesquilinear form on `⋀[𝕜]^n V` with the
  Gram-determinant values is `exteriorPower.gramSesqForm n`.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
-/

public noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace exteriorPower

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

variable (𝕜 V) in
/-- The hermitian form on the exterior algebra for which the increasing wedges of the standard
orthonormal basis of `V` are orthonormal. -/
private def wedgeBasisForm :
    ExteriorAlgebra 𝕜 V →ₗ⋆[𝕜] ExteriorAlgebra 𝕜 V →ₗ[𝕜] 𝕜 :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd 𝕜) (stdOrthonormalBasis 𝕜 V).toBasis.ExteriorAlgebra
    (stdOrthonormalBasis 𝕜 V).toBasis.ExteriorAlgebra 1

/-- The **Gram hermitian form** on the exterior power `⋀[𝕜]^n V` of a finite-dimensional inner
product space, conjugate-linear in the first argument, with
`⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det (⟪vᵢ, wⱼ⟫)` (`exteriorPower.gramSesqForm_ιMulti_ιMulti`). -/
def gramSesqForm (n : ℕ) : ⋀[𝕜]^n V →ₗ⋆[𝕜] ⋀[𝕜]^n V →ₗ[𝕜] 𝕜 :=
  (wedgeBasisForm 𝕜 V ∘ₛₗ (⋀[𝕜]^n V).subtype).compl₂ (⋀[𝕜]^n V).subtype

private theorem gramSesqForm_apply (n : ℕ) (x y : ⋀[𝕜]^n V) :
    gramSesqForm n x y = wedgeBasisForm 𝕜 V x y :=
  (rfl)

/-- **The Gram-determinant formula**: `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det (⟪vᵢ, wⱼ⟫)`. -/
@[simp]
theorem gramSesqForm_ιMulti_ιMulti (n : ℕ) (v w : Fin n → V) :
    gramSesqForm n (ιMulti 𝕜 n v) (ιMulti 𝕜 n w) = (Matrix.of fun i j ↦ ⟪v i, w j⟫_𝕜).det := by
  rw [gramSesqForm_apply, ιMulti_apply_coe, ιMulti_apply_coe, wedgeBasisForm,
    ExteriorAlgebra.toLinearMapₛₗ₂_ιMulti_ιMulti,
    OrthonormalBasis.toLinearMapₛₗ₂_one_eq_innerₛₗ]
  simp only [innerₛₗ_apply_apply]

/-- The Gram form is hermitian. -/
theorem isSymm_gramSesqForm (n : ℕ) : (gramSesqForm (𝕜 := 𝕜) (V := V) n).IsSymm :=
  LinearMap.isSymm_def.mpr fun x y ↦ by
    rw [gramSesqForm_apply, gramSesqForm_apply, starRingEnd_apply, wedgeBasisForm,
      Matrix.star_toLinearMapₛₗ₂_one_apply]

theorem gramSesqForm_self_nonneg (n : ℕ) (x : ⋀[𝕜]^n V) : 0 ≤ gramSesqForm n x x := by
  rw [gramSesqForm_apply, wedgeBasisForm]
  exact Matrix.toLinearMapₛₗ₂_one_self_nonneg _ _

@[simp]
theorem gramSesqForm_self_eq_zero_iff {n : ℕ} {x : ⋀[𝕜]^n V} : gramSesqForm n x x = 0 ↔ x = 0 := by
  rw [gramSesqForm_apply, wedgeBasisForm, Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff,
    Submodule.coe_eq_zero]

/-- The Gram form is positive definite. -/
theorem gramSesqForm_self_pos {n : ℕ} {x : ⋀[𝕜]^n V} (hx : x ≠ 0) : 0 < gramSesqForm n x x :=
  (gramSesqForm_self_nonneg n x).lt_of_ne' (gramSesqForm_self_eq_zero_iff.not.mpr hx)

/-- **The Gram form is determined by its values on decomposable vectors**: a sesquilinear form on
`⋀[𝕜]^n V` with `B (v₁ ∧ ⋯ ∧ vₙ) (w₁ ∧ ⋯ ∧ wₙ) = det (⟪vᵢ, wⱼ⟫)` is the Gram form. -/
theorem eq_gramSesqForm_of_ιMulti {n : ℕ} (B : ⋀[𝕜]^n V →ₗ⋆[𝕜] ⋀[𝕜]^n V →ₗ[𝕜] 𝕜)
    (hB : ∀ v w : Fin n → V,
      B (ιMulti 𝕜 n v) (ιMulti 𝕜 n w) = (Matrix.of fun i j ↦ ⟪v i, w j⟫_𝕜).det) :
    B = gramSesqForm n :=
  LinearMap.ext_on_range (ιMulti_span 𝕜 n V) fun v ↦ LinearMap.ext_on_range (ιMulti_span 𝕜 n V)
    fun w ↦ by rw [hB, gramSesqForm_ιMulti_ιMulti]

end exteriorPower
