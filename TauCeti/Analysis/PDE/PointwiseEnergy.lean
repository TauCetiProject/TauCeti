/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.PDE.UniformEllipticity

/-!
# Pointwise energy forms for divergence-form PDEs

This file relates the pointwise bilinear expression

`ηᵀ A ξ = η ⬝ᵥ A *ᵥ ξ`

to Mathlib's continuous sesquilinear form
`ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A)`.
It is the local algebraic ingredient for the PDE roadmap's divergence-form energy
`∫ x, ∂u(x)ᵀ a(x) ∂v(x)`: uniform ellipticity gives the lower bound needed for coercivity,
and the bilinear upper bound gives continuity.

The file deliberately stays pointwise. Domain Sobolev spaces and integrals are later Lane A/D
material; once they exist, these lemmas are the coefficient-matrix facts used under the integral.

## Main declarations

* `TauCeti.PDE.toSesqForm_toEuclideanCLM_isCoercive_of_lower_bound`: a pointwise lower
  quadratic bound gives Mathlib's `IsCoercive`.
* `TauCeti.PDE.toSesqForm_toEuclideanCLM_isCoercive_of_uniformlyEllipticOn`: uniform
  ellipticity at a point gives coercivity of the corresponding pointwise energy form.
* `TauCeti.PDE.norm_toSesqForm_toEuclideanCLM_le_of_uniformlyEllipticOn`: uniform
  ellipticity gives the pointwise operator-norm upper bound.
* `TauCeti.PDE.toSesqForm_toEuclideanCLM_self`: the quadratic part of Mathlib's matrix
  sesquilinear form is the matrix quadratic form.
* `TauCeti.PDE.toSesqForm_toEuclideanCLM_one_apply`: the identity coefficient is the usual
  inner product.
-/

namespace TauCeti

namespace PDE

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix sesquilinear form is the pointwise dot-product expression. -/
@[simp]
lemma toSesqForm_toEuclideanCLM_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) η) ξ =
      η ⬝ᵥ (A *ᵥ ξ) := by
  exact Matrix.inner_toEuclideanCLM A η ξ

/-- Mathlib's matrix sesquilinear form is the same bundled bilinear form as
`matrixBilinearForm`. -/
lemma toSesqForm_toEuclideanCLM_eq_matrixBilinearForm (A : Matrix n n ℝ) :
    ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      matrixBilinearForm A := by
  ext η ξ
  rw [toSesqForm_toEuclideanCLM_apply]
  exact (matrixBilinearForm_apply A η ξ).symm

/-- The quadratic part of Mathlib's matrix sesquilinear form is the matrix quadratic form. -/
@[simp]
lemma toSesqForm_toEuclideanCLM_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) ξ) ξ =
      A.toQuadraticForm' ξ := by
  rw [toSesqForm_toEuclideanCLM_eq_matrixBilinearForm]
  exact matrixBilinearForm_self A ξ

/-- The operator norm of Mathlib's matrix sesquilinear form is controlled by the supplied
upper bound. -/
lemma norm_toSesqForm_toEuclideanCLM_le (A : Matrix n n ℝ) {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    ‖ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A)‖ ≤ C :=
  by
    rw [toSesqForm_toEuclideanCLM_eq_matrixBilinearForm]
    exact matrixBilinearForm_opNorm_le_of_upper_bound A hC_nonneg hC

/-- A pointwise lower quadratic-form bound gives coercivity of the associated continuous
bilinear form, in Mathlib's `IsCoercive` sense used by Lax--Milgram. -/
lemma toSesqForm_toEuclideanCLM_isCoercive_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (hlower : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ (A.toQuadraticForm' ξ)) :
    IsCoercive (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) := by
  rw [toSesqForm_toEuclideanCLM_eq_matrixBilinearForm]
  exact isCoercive_matrixBilinearForm_of_lower_bound A hlam hlower

/-- Uniform ellipticity at a point gives coercivity of the pointwise energy form. -/
@[grind =>]
lemma toSesqForm_toEuclideanCLM_isCoercive_of_uniformlyEllipticOn {X : Type*} {Ω : Set X}
    {a : X → Matrix n n ℝ} {lam Lam : ℝ} (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) :
    IsCoercive (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) (a x))) :=
  toSesqForm_toEuclideanCLM_isCoercive_of_lower_bound (a x) h.pos (h.lower_bound hx)

/-- Uniform ellipticity at a point gives the operator-norm upper bound for Mathlib's matrix
sesquilinear form. -/
@[grind =>]
lemma norm_toSesqForm_toEuclideanCLM_le_of_uniformlyEllipticOn {X : Type*} {Ω : Set X}
    {a : X → Matrix n n ℝ} {lam Lam : ℝ} (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) :
    ‖ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) (a x))‖ ≤ Lam :=
  norm_toSesqForm_toEuclideanCLM_le (a x) (h.pos.le.trans h.le) (h.upper_bound hx)

/-- The identity coefficient's pointwise energy form is the real inner product. -/
@[simp]
lemma toSesqForm_toEuclideanCLM_one_apply (η ξ : EuclideanSpace ℝ n) :
    (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix n n ℝ)) η)
      ξ = inner ℝ η ξ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The identity coefficient's pointwise energy form is coercive with coercivity constant `1`. -/
lemma toSesqForm_toEuclideanCLM_one_isCoercive :
    IsCoercive
      (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix n n ℝ))) :=
  toSesqForm_toEuclideanCLM_isCoercive_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one
    (fun ξ => by simp)

/-- The identity matrix satisfies the raw dot-product upper bound with constant `1`. -/
lemma dotProduct_one_mulVec_le_norm_mul_norm (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖ := by
  rw [one_mulVec, one_mul]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

end

end PDE

end TauCeti
