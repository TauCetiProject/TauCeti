/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Real inner products with a unit complex number

Multiplication by a unit complex number `ζ` is a rotation of the plane, so the real inner product
of `ζ` with `ζ * w` is the real inner product of `1` with `w`, namely the real part of `w`. This
lets the level sets `⟪ζ, z⟫_ℝ = t` be read in the rotated coordinate `w = conj ζ * z`.
Conversely, a real-linear map of the plane commuting with multiplication by `i` and preserving the
real inner product is a rotation by a unit complex number.

## Main declarations

* `Complex.mul_conj_eq_one_of_norm_eq_one` -- a unit complex number times its conjugate is `1`.
* `Complex.inner_mul_left_of_norm_eq_one` -- `⟪ζ, ζ * w⟫_ℝ = w.re` for a unit `ζ`.
* `Complex.inner_mul_mul_of_norm_eq_one` -- `⟪ζ * a, ζ * b⟫_ℝ = ⟪a, b⟫_ℝ` for a unit `ζ`.
* `Complex.real_inner_I_right` -- `⟪z, i⟫_ℝ = z.im`: the height of `z` in the direction of `i`.
* `Complex.I_mul_I_mul` -- `i (i z) = -z`.
* `Complex.real_inner_I_mul_left` -- multiplication by `i` is skew-adjoint:
  `⟪i x, y⟫_ℝ = -⟪x, i y⟫_ℝ`.
* `Complex.exists_apply_eq_mul_exp` -- a real-linear map commuting with multiplication by `i` and
  preserving `⟪i ·, ·⟫_ℝ` on `(1, i)` is multiplication by `exp (i θ)`.
* `LinearIsometry.norm_map_I` -- a linear isometry from the plane maps `i` to a unit vector.
* `Real.inner_ofReal_I_mul_ofReal` -- `⟪x, i y⟫_ℝ = 0` for real `x`, `y`: the real line is
  orthogonal to its rotation by `i`.
-/

public section

namespace Complex

variable {ζ : ℂ}

/-- A complex number of norm `1` times its conjugate is `1`. -/
theorem mul_conj_eq_one_of_norm_eq_one (hζ : ‖ζ‖ = 1) : ζ * (starRingEnd ℂ) ζ = 1 := by
  rw [mul_conj', hζ]
  norm_num

/-- The real inner product of a unit complex number `ζ` with `ζ * w` is the real part of `w`. -/
theorem inner_mul_left_of_norm_eq_one (hζ : ‖ζ‖ = 1) (w : ℂ) : inner ℝ ζ (ζ * w) = w.re := by
  rw [Complex.inner, mul_comm ζ w, mul_assoc, mul_conj_eq_one_of_norm_eq_one hζ, mul_one]

/-- Multiplication by a unit complex number `ζ` preserves the real inner product. -/
theorem inner_mul_mul_of_norm_eq_one (hζ : ‖ζ‖ = 1) (a b : ℂ) :
    inner ℝ (ζ * a) (ζ * b) = inner ℝ a b := by
  rw [Complex.inner, Complex.inner, map_mul, mul_mul_mul_comm, mul_comm ζ,
    mul_comm (starRingEnd ℂ ζ), mul_conj_eq_one_of_norm_eq_one hζ, one_mul]

/-- The real inner product of `z` with `i` is the imaginary part of `z`. -/
theorem real_inner_I_right (z : ℂ) : inner ℝ z I = z.im := by
  simp [Complex.inner]

/-- Multiplying twice by `i` negates. -/
@[simp]
theorem I_mul_I_mul (z : ℂ) : I * (I * z) = -z := by
  rw [← mul_assoc, I_mul_I, neg_one_mul]

/-- Multiplication by `i` is skew-adjoint for the real inner product of `ℂ`. -/
theorem real_inner_I_mul_left (x y : ℂ) : inner ℝ (I * x) y = -inner ℝ x (I * y) := by
  simp only [Complex.inner, mul_re, mul_im, conj_re, conj_im, I_re, I_im]
  ring

/-- A real-linear map of `ℂ` commuting with multiplication by `i` and preserving `⟪i ·, ·⟫_ℝ` on
the pair `(1, i)` is multiplication by a unit complex number `exp (i θ)`. -/
theorem exists_apply_eq_mul_exp {C : ℂ →ₗ[ℝ] ℂ} (hCI : ∀ z, C (I * z) = I * C z)
    (hCω : inner ℝ (I * C 1) (C I) = inner ℝ I I) :
    ∃ θ : ℝ, ∀ z, C z = z * exp (θ * I) := by
  have hC (z : ℂ) : C z = z * C 1 :=
    calc C z = C (z.re • (1 : ℂ) + z.im • (I * 1)) := by
          congr 1
          apply Complex.ext <;> simp
      _ = z.re • C 1 + z.im • (I * C 1) := by rw [map_add, map_smul, map_smul, hCI]
      _ = z * C 1 := by apply Complex.ext <;> simp [sub_eq_add_neg]
  have hnorm : ‖C 1‖ = 1 := by
    rw [hC I, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_mul, norm_I,
      one_mul] at hCω
    nlinarith [norm_nonneg (C 1)]
  refine ⟨arg (C 1), fun z => ?_⟩
  rw [hC z]
  congr 1
  simpa [hnorm] using (norm_mul_exp_arg_mul_I (C 1)).symm

end Complex

/-- A linear isometry from the plane maps `i` to a unit vector. -/
theorem LinearIsometry.norm_map_I {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι Complex.I‖ = 1 :=
  (ι.norm_map _).trans Complex.norm_I

/-- The real line is orthogonal to its rotation by `i`: `⟪x, i y⟫_ℝ = 0` for real `x`, `y`. That
is, `F = ℝ ⊆ ℂ` satisfies the orthogonality `⟪F, J F⟫ = 0` for `J = i`. -/
theorem Real.inner_ofReal_I_mul_ofReal (x y : ℝ) : inner ℝ (x : ℂ) (Complex.I * y) = 0 := by
  simp [Complex.inner]
