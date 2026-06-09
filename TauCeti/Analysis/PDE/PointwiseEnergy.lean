/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
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

namespace PDE

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The pointwise energy form `η, ξ ↦ ηᵀ A ξ` as a continuous bilinear form.

This is the pointwise integrand of the principal part of a divergence-form energy form. -/
def pointwiseEnergy (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  let B := ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
  { toLinearMap :=
      { toFun := fun η => B η
        map_add' := by
          intro η η'
          ext ξ
          simp
        map_smul' := by
          intro c η
          ext ξ
          simp }
    cont := by
      simpa using B.cont }

/-- The value of `pointwiseEnergy` is the matrix expression `ηᵀ A ξ`. -/
@[simp]
lemma pointwiseEnergy_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    pointwiseEnergy A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  rw [pointwiseEnergy]
  change (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) η) ξ =
    η ⬝ᵥ (A *ᵥ ξ)
  exact Matrix.inner_toEuclideanCLM A η ξ

/-- The operator norm of the pointwise energy form is controlled by the supplied upper bound. -/
lemma norm_pointwiseEnergy_le (A : Matrix n n ℝ) {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    ‖pointwiseEnergy A‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound (pointwiseEnergy A) hC_nonneg fun η => by
    refine ContinuousLinearMap.opNorm_le_bound (pointwiseEnergy A η)
      (mul_nonneg hC_nonneg (norm_nonneg η)) fun ξ => ?_
    calc
      ‖pointwiseEnergy A η ξ‖ = |η ⬝ᵥ (A *ᵥ ξ)| := by
        rw [pointwiseEnergy_apply, Real.norm_eq_abs]
      _ ≤ C * ‖η‖ * ‖ξ‖ := hC η ξ
      _ = (C * ‖η‖) * ‖ξ‖ := by ring

/-- A pointwise lower quadratic-form bound gives coercivity of the associated continuous
bilinear form, in Mathlib's `IsCoercive` sense used by Lax--Milgram. -/
lemma pointwiseEnergy_isCoercive_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (hlower : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ (A.toQuadraticForm' ξ)) :
    IsCoercive (pointwiseEnergy A) := by
  refine ⟨lam, hlam, fun ξ => ?_⟩
  calc
    lam * ‖ξ‖ * ‖ξ‖ = lam * ‖ξ‖ ^ 2 := by ring
    _ ≤ A.toQuadraticForm' ξ := hlower ξ
    _ = pointwiseEnergy A ξ ξ := by
      simp [toQuadraticForm'_eq_dotProduct]

/-- Uniform ellipticity at a point gives coercivity of the pointwise energy form. -/
lemma pointwiseEnergy_isCoercive_of_uniformlyEllipticOn {X : Type*} {Ω : Set X}
    {a : X → Matrix n n ℝ} {lam Lam : ℝ} (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) :
    IsCoercive (pointwiseEnergy (a x)) :=
  pointwiseEnergy_isCoercive_of_lower_bound (a x) h.pos (h.lower_bound hx)

/-- The identity coefficient's pointwise energy form is the real inner product. -/
@[simp]
lemma pointwiseEnergy_one_apply (η ξ : EuclideanSpace ℝ n) :
    pointwiseEnergy (1 : Matrix n n ℝ) η ξ = inner ℝ η ξ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The identity coefficient's pointwise energy form is coercive with coercivity constant `1`. -/
lemma pointwiseEnergy_one_isCoercive :
    IsCoercive (pointwiseEnergy (1 : Matrix n n ℝ)) :=
  pointwiseEnergy_isCoercive_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one
    (fun ξ => by simp)

/-- The identity coefficient satisfies the pointwise upper bound with constant `1`. -/
lemma pointwiseEnergy_one_bound (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖ := by
  rw [one_mulVec, one_mul]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

end

end PDE

end TauCeti
