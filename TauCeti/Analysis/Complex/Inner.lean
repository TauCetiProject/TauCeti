/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Conformal
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# Real inner products with a unit complex number

Multiplication by a scalar `ζ` of an `RCLike` field scales the real inner product by `‖ζ‖ ^ 2`
(`TauCeti.RCLike.real_inner_mul_mul`). In particular multiplication by a unit complex number `ζ`
is a rotation of the plane, so the real inner product of `ζ` with `ζ * w` is the real inner
product of `1` with `w`, namely the real part of `w`. This lets the level sets `⟪ζ, z⟫_ℝ = t` be
read in the rotated coordinate `w = conj ζ * z`. Conversely, a real-linear map of the plane
commuting with multiplication by `i` at `1` and preserving the real inner product is a rotation by
a unit complex number.

## Main declarations

* `Complex.inner_mul_mul_of_norm_eq_one` -- `⟪ζ * a, ζ * b⟫_ℝ = ⟪a, b⟫_ℝ` for a unit `ζ`.
* `Complex.inner_mul_left_of_norm_eq_one` -- `⟪ζ, ζ * w⟫_ℝ = w.re` for a unit `ζ`.
* `Complex.real_inner_I_right` -- `⟪z, i⟫_ℝ = z.im`: the height of `z` in the direction of `i`.
* `Complex.inner_one_smul_I_sub_inner_I_smul_one` -- the infinitesimal rotation
  `z ↦ ⟪z, 1⟫_ℝ i - ⟪z, i⟫_ℝ` of the plane is multiplication by `i`.
* `Complex.I_mul_I_mul` -- `i (i z) = -z`.
* `Complex.real_inner_I_mul_left` -- multiplication by `i` is skew-adjoint:
  `⟪i x, y⟫_ℝ = -⟪x, i y⟫_ℝ`.
* `Complex.exists_apply_eq_mul_exp` -- a real-linear map `C` with `C i = i * C 1` and
  preserving `⟪i ·, ·⟫_ℝ` on `(1, i)` is multiplication by `exp (i θ)`.
* `Real.inner_ofReal_I_mul_ofReal` -- `⟪x, i y⟫_ℝ = 0` for real `x`, `y`: the real line is
  orthogonal to its rotation by `i`.
-/

public section

namespace Complex

variable {ζ : ℂ}

/-- Multiplication by a unit complex number `ζ` preserves the real inner product. -/
theorem inner_mul_mul_of_norm_eq_one (hζ : ‖ζ‖ = 1) (a b : ℂ) :
    inner ℝ (ζ * a) (ζ * b) = inner ℝ a b := by
  rw [TauCeti.RCLike.real_inner_mul_mul, hζ, one_pow, one_mul]

/-- The real inner product of a unit complex number `ζ` with `ζ * w` is the real part of `w`. -/
theorem inner_mul_left_of_norm_eq_one (hζ : ‖ζ‖ = 1) (w : ℂ) : inner ℝ ζ (ζ * w) = w.re := by
  simpa [Complex.inner] using inner_mul_mul_of_norm_eq_one hζ 1 w

/-- The real inner product of `z` with `i` is the imaginary part of `z`. -/
theorem real_inner_I_right (z : ℂ) : inner ℝ z I = z.im := by
  simp [Complex.inner]

/-- The infinitesimal rotation `z ↦ ⟪z, 1⟫ i - ⟪z, i⟫` of the plane `ℂ` is multiplication by `i`. -/
theorem inner_one_smul_I_sub_inner_I_smul_one (z : ℂ) :
    inner ℝ z 1 • I - inner ℝ z I • (1 : ℂ) = I * z := by
  apply Complex.ext <;> simp [Complex.inner]

/-- Multiplying twice by `i` negates. -/
@[simp]
theorem I_mul_I_mul (z : ℂ) : I * (I * z) = -z := by
  rw [← mul_assoc, I_mul_I, neg_one_mul]

/-- Multiplication by `i` is skew-adjoint for the real inner product of `ℂ`. -/
theorem real_inner_I_mul_left (x y : ℂ) : inner ℝ (I * x) y = -inner ℝ x (I * y) := by
  simp only [Complex.inner, mul_re, mul_im, conj_re, conj_im, I_re, I_im]
  ring

/-- A real-linear map `C` of `ℂ` with `C i = i * C 1`, preserving `⟪i ·, ·⟫_ℝ` on the pair
`(1, i)`, is multiplication by a unit complex number `exp (i θ)`. -/
theorem exists_apply_eq_mul_exp {C : ℂ →ₗ[ℝ] ℂ} (hCI : C I = I * C 1)
    (hCω : inner ℝ (I * C 1) (C I) = inner ℝ I I) :
    ∃ θ : ℝ, ∀ z, C z = z * exp (θ * I) := by
  have hC (z : ℂ) : C z = z * C 1 := by
    simpa using real_linearMap_map_smul_complex (ℓ := C) (by simpa using hCI) z 1
  have hnorm : ‖C 1‖ = 1 := by
    have h : ‖C 1‖ ^ 2 = (1 : ℝ) ^ 2 := by
      simpa [hCI, real_inner_self_eq_norm_sq, norm_mul] using hCω
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h
  obtain ⟨θ, hθ⟩ := (norm_eq_one_iff (C 1)).1 hnorm
  exact ⟨θ, fun z => by rw [hC z, hθ]⟩

end Complex

/-- The real line is orthogonal to its rotation by `i`: `⟪x, i y⟫_ℝ = 0` for real `x`, `y`. That
is, `F = ℝ ⊆ ℂ` satisfies the orthogonality `⟪F, J F⟫ = 0` for `J = i`. -/
theorem Real.inner_ofReal_I_mul_ofReal (x y : ℝ) : inner ℝ (x : ℂ) (Complex.I * y) = 0 := by
  simp [Complex.inner]
