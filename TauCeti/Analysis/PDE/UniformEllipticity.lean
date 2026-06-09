/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Uniform ellipticity for divergence-form PDE coefficients

This file records the explicit-constant matrix inequalities used for uniformly elliptic
divergence-form operators. For a coefficient field
`a : X → Matrix n n ℝ` on a domain `Ω : Set X`, the predicate
`UniformlyEllipticOn Ω a λ Λ` means

`λ ‖ξ‖² ≤ ξᵀ a(x) ξ` and `|ηᵀ a(x) ξ| ≤ Λ ‖η‖ ‖ξ‖`

for every `x ∈ Ω` and all vectors `η`, `ξ`, together with the quantitative side conditions
`0 < λ` and `λ ≤ Λ`. The lower bound is the coercivity hypothesis; the bilinear upper bound
controls nonsymmetric coefficient fields for weak-form boundedness.

This is the coefficient hypothesis named in the PDE roadmap before the energy bilinear form
and Lax--Milgram arguments: constants are parameters, not hidden existential data.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn`: uniform lower and upper ellipticity bounds on a set.
* `TauCeti.PDE.uniformlyEllipticOn_const_one`: the identity matrix is uniformly elliptic.
* `TauCeti.PDE.UniformlyEllipticOn.mono_constants`: weakening constants preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.mono_set`: restriction to a smaller domain preserves the
  predicate.
* `TauCeti.PDE.matrixBilinearForm`: the bounded bilinear form `η, ξ ↦ ηᵀ A ξ` attached to
  a coefficient matrix.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_matrixBilinearForm`: pointwise coercivity of
  the bilinear form attached to a uniformly elliptic coefficient field.

The vectors are `EuclideanSpace ℝ n`, matching the roadmap's bounded open subsets of
`ℝⁿ`; this type is reducibly a finite `L²` product, so Mathlib's matrix-vector API applies
directly.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ (A *ᵥ ξ) := by
  rw [Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- The identity matrix has quadratic form `‖ξ‖²`. -/
@[simp]
lemma toQuadraticForm'_one (ξ : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toQuadraticForm' ξ = ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_eq_dotProduct, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

omit [DecidableEq n] in
/-- The continuous bilinear form attached to a real matrix on Euclidean space.

For a coefficient matrix `A`, this is the pointwise weak-form integrand
`(η, ξ) ↦ ηᵀ A ξ`. It is bundled as a continuous bilinear map so it can feed directly into
Mathlib's bounded-bilinear-form and Lax--Milgram APIs once the corresponding Sobolev spaces
are available. -/
noncomputable def matrixBilinearForm (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  (A.toBilin'.comp (EuclideanSpace.equiv n ℝ).toLinearMap
    (EuclideanSpace.equiv n ℝ).toLinearMap).toContinuousBilinearMap

/-- The matrix bilinear form is the dot-product expression `ηᵀ A ξ`. -/
@[simp]
lemma matrixBilinearForm_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  rw [matrixBilinearForm, LinearMap.toContinuousBilinearMap_apply,
    LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply']
  rfl

/-- The matrix bilinear form associated to the identity matrix is the Euclidean dot product. -/
@[simp]
lemma matrixBilinearForm_one_apply (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (1 : Matrix n n ℝ) η ξ = η ⬝ᵥ ξ := by
  rw [matrixBilinearForm_apply, one_mulVec]

/-- The quadratic part of the matrix bilinear form is the matrix quadratic form. -/
@[simp]
lemma matrixBilinearForm_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A ξ ξ = A.toQuadraticForm' ξ := by
  rw [matrixBilinearForm_apply, toQuadraticForm'_eq_dotProduct]

/-- A pointwise bilinear upper bound gives the corresponding norm estimate for the bundled
continuous bilinear form. -/
lemma norm_matrixBilinearForm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using hA η ξ

/-- A pointwise quadratic lower bound makes the associated matrix bilinear form coercive in
Mathlib's Lax--Milgram sense. -/
lemma isCoercive_matrixBilinearForm_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) :
    IsCoercive (matrixBilinearForm A) := by
  refine ⟨lam, hlam, fun ξ => ?_⟩
  rw [matrixBilinearForm_self]
  simpa [sq, pow_two, mul_assoc] using hA ξ

/-- The identity matrix bilinear form is coercive with constant `1`. -/
lemma isCoercive_matrixBilinearForm_one :
    IsCoercive (matrixBilinearForm (1 : Matrix n n ℝ)) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one ?_
  intro ξ
  simp

/-- Uniform ellipticity and boundedness with explicit constants on a domain.

The predicate says that for every `x ∈ Ω`, the matrix `a x` has quadratic form bounded below
by `λ‖ξ‖²` and bilinear form bounded above by `Λ‖η‖‖ξ‖`, uniformly in `x`, `η`, and `ξ`.
The side conditions `0 < λ` and `λ ≤ Λ` are part of the predicate so later energy estimates can
recover them directly. -/
def UniformlyEllipticOn (Ω : Set X) (a : X → Matrix n n ℝ) (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω →
      (∀ ξ : EuclideanSpace ℝ n,
        lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖

/-- Characteristic restatement of uniform ellipticity and boundedness on a domain. -/
lemma uniformlyEllipticOn_iff :
    UniformlyEllipticOn Ω a lam Lam ↔
      0 < lam ∧ lam ≤ Lam ∧
        ∀ ⦃x⦄, x ∈ Ω →
          (∀ ξ : EuclideanSpace ℝ n,
            lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
            ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a : X → Matrix n n ℝ} {lam Lam lam' Lam' : ℝ}

/-- The lower ellipticity constant is positive. -/
@[grind →]
lemma pos (h : UniformlyEllipticOn Ω a lam Lam) : 0 < lam :=
  h.1

/-- The lower ellipticity constant is no larger than the upper constant. -/
@[grind →]
lemma le (h : UniformlyEllipticOn Ω a lam Lam) : lam ≤ Lam :=
  h.2.1

/-- The lower quadratic-form bound supplied by uniform ellipticity. -/
@[grind =>]
lemma lower_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ :=
  (h.2.2 hx).1 ξ

/-- The bilinear upper bound supplied by uniform ellipticity. -/
@[grind =>]
lemma upper_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  (h.2.2 hx).2 η ξ

/-- Uniform ellipticity implies pointwise nonnegativity of the coefficient quadratic form. -/
lemma quadraticForm_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    0 ≤ (a x).toQuadraticForm' ξ := by
  exact (mul_nonneg h.pos.le (sq_nonneg ‖ξ‖)).trans (h.lower_bound hx ξ)

/-- Uniform ellipticity gives a positive quadratic form on every nonzero vector. -/
lemma quadraticForm_pos (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {ξ : EuclideanSpace ℝ n} (hξ : ξ ≠ 0) :
    0 < (a x).toQuadraticForm' ξ := by
  exact (mul_pos h.pos (sq_pos_of_ne_zero (by simpa using hξ))).trans_le
    (h.lower_bound hx ξ)

/-- Restricting the domain preserves uniform ellipticity with the same constants. -/
lemma mono_set (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    UniformlyEllipticOn Ω' a lam Lam :=
  ⟨h.pos, h.le, fun {_} hx => h.2.2 (hΩ hx)⟩

/-- Weakening the lower constant and increasing the upper constant preserves uniform
ellipticity. -/
lemma mono_constants (h : UniformlyEllipticOn Ω a lam Lam) (hlam' : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    UniformlyEllipticOn Ω a lam' Lam' := by
  refine ⟨hlam', hlam'_le.trans (h.le.trans hLam_le), fun {x} hx => ?_⟩
  refine ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    exact (mul_le_mul_of_nonneg_right hlam'_le hnorm).trans (h.lower_bound hx ξ)
  · exact (h.upper_bound hx η ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLam_le (norm_nonneg _))
        (norm_nonneg _))

/-- A constructor when the side conditions and pointwise quadratic-form bounds are already
available separately. -/
lemma of_bounds (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbounds : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hupper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω a lam Lam :=
  ⟨hlam, hlamLam, fun {_} hx => ⟨hbounds hx, hupper hx⟩⟩

/-- At every point of the domain, uniform ellipticity gives a norm bound for the attached
matrix bilinear form. -/
@[grind =>]
lemma norm_point_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

/-- At every point of the domain, uniform ellipticity gives coercivity of the attached matrix
bilinear form. -/
@[grind =>]
lemma isCoercive_matrixBilinearForm (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  isCoercive_matrixBilinearForm_of_lower_bound (a x) h.pos (h.lower_bound hx)

end UniformlyEllipticOn

/-- The constant identity coefficient field is uniformly elliptic with any constants
`λ ≤ 1 ≤ Λ` and `0 < λ`. This is the coefficient field of the Laplacian model problem. -/
lemma uniformlyEllipticOn_const_one (Ω : Set X) {lam Lam : ℝ} (hlam : 0 < lam)
    (hlam_one : lam ≤ 1) (hone_Lam : 1 ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam (hlam_one.trans hone_Lam) (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    simp only [toQuadraticForm'_one]
    simpa using mul_le_mul_of_nonneg_right hlam_one hnorm
  · rw [one_mulVec]
    calc
      |η ⬝ᵥ ξ| ≤ ‖η‖ * ‖ξ‖ := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
          abs_real_inner_le_norm η ξ
      _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
        have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hone_Lam hnorm

/-- In particular, the identity coefficient field is uniformly elliptic with constants
`λ = Λ = 1`. -/
lemma uniformlyEllipticOn_const_one_one (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

end PDE

end TauCeti
