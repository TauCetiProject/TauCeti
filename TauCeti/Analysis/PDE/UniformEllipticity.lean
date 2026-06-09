/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.LinearAlgebra.Matrix.SymmetricPart

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
* `TauCeti.PDE.UniformlyEllipticOn.selfAdjointPart`: replacing coefficients by their
  self-adjoint part preserves the same uniform ellipticity constants.

The vectors are `EuclideanSpace ℝ n`, matching the roadmap's bounded open subsets of
`ℝⁿ`; this type is reducibly a finite `L²` product, so Mathlib's matrix-vector API applies
directly.
-/

namespace TauCeti

namespace PDE

open _root_.Matrix

variable {X n : Type*}

/-- The identity matrix has quadratic form `‖ξ‖²`. -/
@[simp]
lemma toQuadraticForm'_one [Fintype n] [DecidableEq n] (ξ : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toQuadraticForm' ξ = ‖ξ‖ ^ 2 := by
  rw [TauCeti.Matrix.toQuadraticForm'_eq_dotProduct, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

/-- Uniform ellipticity and boundedness with explicit constants on a domain.

The predicate says that for every `x ∈ Ω`, the matrix `a x` has quadratic form bounded below
by `λ‖ξ‖²` and bilinear form bounded above by `Λ‖η‖‖ξ‖`, uniformly in `x`, `η`, and `ξ`.
The side conditions `0 < λ` and `λ ≤ Λ` are part of the predicate so later energy estimates can
recover them directly. -/
def UniformlyEllipticOn [Fintype n] [DecidableEq n] (Ω : Set X) (a : X → Matrix n n ℝ)
    (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω →
      (∀ ξ : EuclideanSpace ℝ n,
        lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖

/-- Characteristic restatement of uniform ellipticity and boundedness on a domain. -/
lemma uniformlyEllipticOn_iff [Fintype n] [DecidableEq n] :
    UniformlyEllipticOn Ω a lam Lam ↔
      0 < lam ∧ lam ≤ Lam ∧
        ∀ ⦃x⦄, x ∈ Ω →
          (∀ ξ : EuclideanSpace ℝ n,
            lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
            ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

namespace UniformlyEllipticOn

variable [Fintype n] [DecidableEq n]
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

/-- Replacing a coefficient field by its pointwise transpose preserves the same upper
bilinear bound, with the arguments exchanged. -/
lemma upper_bound_transpose (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((a x)ᵀ *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  calc
    |η ⬝ᵥ ((a x)ᵀ *ᵥ ξ)| = |ξ ⬝ᵥ (a x *ᵥ η)| := by
      rw [Matrix.dotProduct_transpose_mulVec]
    _ ≤ Lam * ‖ξ‖ * ‖η‖ := h.upper_bound hx ξ η
    _ = Lam * ‖η‖ * ‖ξ‖ := by ring

/-- The self-adjoint part of uniformly elliptic coefficients is uniformly elliptic with the same
constants. -/
lemma selfAdjointPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => (selfAdjointPart ℝ (a x) : Matrix n n ℝ)) lam Lam := by
  refine of_bounds h.pos h.le (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · rw [TauCeti.Matrix.toQuadraticForm'_selfAdjointPart]
    exact h.lower_bound hx ξ
  · have hself :
        (_root_.selfAdjointPart ℝ (a x) : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (a x + (a x)ᵀ) := by
      ext i j
      simp
    rw [hself, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
    set C : ℝ := Lam * ‖η‖ * ‖ξ‖
    have hA : |η ⬝ᵥ (a x *ᵥ ξ)| ≤ C := h.upper_bound hx η ξ
    have hAT : |η ⬝ᵥ ((a x)ᵀ *ᵥ ξ)| ≤ C := h.upper_bound_transpose hx η ξ
    calc
      |(2 : ℝ)⁻¹ • (η ⬝ᵥ (a x *ᵥ ξ) + η ⬝ᵥ ((a x)ᵀ *ᵥ ξ))|
          = (2 : ℝ)⁻¹ * |η ⬝ᵥ (a x *ᵥ ξ) + η ⬝ᵥ ((a x)ᵀ *ᵥ ξ)| := by
            rw [smul_eq_mul, abs_mul, abs_of_nonneg]
            · norm_num
      _ ≤ (2 : ℝ)⁻¹ * (C + C) := by
        exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hA hAT))
          (by norm_num)
      _ = C := by ring

end UniformlyEllipticOn

/-- The constant identity coefficient field is uniformly elliptic with any constants
`λ ≤ 1 ≤ Λ` and `0 < λ`. This is the coefficient field of the Laplacian model problem. -/
lemma uniformlyEllipticOn_const_one [Fintype n] [DecidableEq n] (Ω : Set X) {lam Lam : ℝ}
    (hlam : 0 < lam)
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
lemma uniformlyEllipticOn_const_one_one [Fintype n] [DecidableEq n] (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

end PDE

end TauCeti
