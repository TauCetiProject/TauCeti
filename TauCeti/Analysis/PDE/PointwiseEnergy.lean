/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.Analysis.PDE.UniformEllipticity

/-!
# Pointwise energy forms for divergence-form PDEs

This file packages the pointwise bilinear expression

`ηᵀ A ξ = η ⬝ᵥ A *ᵥ ξ`

as a continuous bilinear form on `EuclideanSpace ℝ n`. It is the local algebraic ingredient
for the PDE roadmap's divergence-form energy
`∫ x, ∂u(x)ᵀ a(x) ∂v(x)`: uniform ellipticity gives the lower bound needed for coercivity,
and the bilinear upper bound gives continuity.

The file deliberately stays pointwise. Domain Sobolev spaces and integrals are later Lane A/D
material; once they exist, these lemmas are the coefficient-matrix facts used under the integral.

## Main declarations

* `TauCeti.PDE.pointwiseEnergy`: the continuous bilinear form `η, ξ ↦ ηᵀ A ξ`.
* `TauCeti.PDE.pointwiseEnergy_isCoercive_of_lower_bound`: a pointwise lower quadratic
  bound gives Mathlib's `IsCoercive`.
* `TauCeti.PDE.pointwiseEnergy_isCoercive_of_uniformlyEllipticOn`: uniform ellipticity at a
  point gives coercivity of the corresponding pointwise energy form.
* `TauCeti.PDE.pointwiseEnergy_one_apply`: the identity coefficient is the usual inner product.
-/

namespace TauCeti

namespace IsCoercive

/-- A positive diagonal lower bound is the basic constructor for Mathlib's `IsCoercive`. -/
lemma of_lower_bound {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ u, lam * ‖u‖ ^ 2 ≤ B u u) : IsCoercive B := by
  refine ⟨lam, hlam, fun u => ?_⟩
  calc
    lam * ‖u‖ * ‖u‖ = lam * ‖u‖ ^ 2 := by ring
    _ ≤ B u u := h u

end IsCoercive

namespace PDE

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The algebraic bilinear form `η, ξ ↦ ηᵀ A ξ` associated to a coefficient matrix.

This is the pointwise integrand of the principal part of a divergence-form energy form. -/
private def pointwiseEnergyLinear (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n →ₗ[ℝ] ℝ :=
  (Matrix.toBilin' A).comp (EuclideanSpace.equiv n ℝ).toLinearMap
    (EuclideanSpace.equiv n ℝ).toLinearMap

@[simp]
private lemma pointwiseEnergyLinear_apply (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    pointwiseEnergyLinear A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  simp [pointwiseEnergyLinear, EuclideanSpace.equiv, Matrix.toBilin'_apply',
    PiLp.coe_continuousLinearEquiv]

/-- The pointwise energy form `η, ξ ↦ ηᵀ A ξ` as a continuous bilinear form.

The continuity bound is supplied explicitly because the PDE roadmap tracks the upper ellipticity
constant `Λ` separately from the lower ellipticity constant `λ`. -/
def pointwiseEnergy (A : Matrix n n ℝ) {C : ℝ}
    (hC : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  (pointwiseEnergyLinear A).mkContinuous₂ C fun η ξ => by
    simpa [Real.norm_eq_abs] using hC η ξ

/-- The value of `pointwiseEnergy` is the matrix expression `ηᵀ A ξ`. -/
@[simp]
lemma pointwiseEnergy_apply (A : Matrix n n ℝ) {C : ℝ}
    (hC : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    pointwiseEnergy A hC η ξ = η ⬝ᵥ (A *ᵥ ξ) :=
  by
    simp [pointwiseEnergy]

/-- The operator norm of the pointwise energy form is controlled by the supplied upper bound. -/
lemma norm_pointwiseEnergy_le (A : Matrix n n ℝ) {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    ‖pointwiseEnergy A hC‖ ≤ C :=
  LinearMap.mkContinuous₂_norm_le (pointwiseEnergyLinear A) hC_nonneg fun η ξ => by
    simpa [Real.norm_eq_abs] using hC η ξ

/-- A pointwise lower quadratic-form bound gives coercivity of the associated continuous
bilinear form, in Mathlib's `IsCoercive` sense used by Lax--Milgram. -/
lemma pointwiseEnergy_isCoercive_of_lower_bound (A : Matrix n n ℝ) {lam C : ℝ}
    (hlam : 0 < lam)
    (hlower : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ (A.toQuadraticForm' ξ))
    (hupper : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    IsCoercive (pointwiseEnergy A hupper) := by
  refine IsCoercive.of_lower_bound (pointwiseEnergy A hupper) hlam fun ξ => ?_
  calc
    lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ := hlower ξ
    _ = pointwiseEnergy A hupper ξ ξ := by
      simp [toQuadraticForm'_eq_dotProduct]

/-- Uniform ellipticity at a point gives coercivity of the pointwise energy form. -/
lemma pointwiseEnergy_isCoercive_of_uniformlyEllipticOn {X : Type*} {Ω : Set X}
    {a : X → Matrix n n ℝ} {lam Lam : ℝ} (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) :
    IsCoercive (pointwiseEnergy (a x) (h.upper_bound hx)) :=
  pointwiseEnergy_isCoercive_of_lower_bound (a x) h.pos (h.lower_bound hx)
    (h.upper_bound hx)

/-- The identity coefficient's pointwise energy form is the real inner product. -/
@[simp]
lemma pointwiseEnergy_one_apply (hC : ∀ η ξ : EuclideanSpace ℝ n,
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    pointwiseEnergy (1 : Matrix n n ℝ) hC η ξ = inner ℝ η ξ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The identity coefficient's pointwise energy form is coercive with coercivity constant `1`. -/
lemma pointwiseEnergy_one_isCoercive (hC : ∀ η ξ : EuclideanSpace ℝ n,
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖) :
    IsCoercive (pointwiseEnergy (1 : Matrix n n ℝ) hC) :=
  pointwiseEnergy_isCoercive_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one
    (fun ξ => by simp) hC

/-- The identity coefficient satisfies the pointwise upper bound with constant `1`. -/
lemma pointwiseEnergy_one_bound (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖ := by
  rw [one_mulVec, one_mul]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

/-- The identity-coefficient pointwise energy is Mathlib's continuous inner product. -/
lemma pointwiseEnergy_one_eq_innerSL :
    pointwiseEnergy (1 : Matrix n n ℝ) pointwiseEnergy_one_bound =
      (innerSL ℝ : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ) := by
  ext η ξ
  rw [pointwiseEnergy_one_apply]
  rfl

end

end PDE

end TauCeti
