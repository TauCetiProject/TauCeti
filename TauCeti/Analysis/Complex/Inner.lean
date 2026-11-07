/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.Analysis.RCLike.Sum

/-!
# Real inner products with a unit complex number

Multiplication by a unit complex number `ζ` is a rotation of the plane, so the real inner product
of `ζ` with `ζ * w` is the real inner product of `1` with `w`, namely the real part of `w`. This
lets the level sets `⟪ζ, z⟫_ℝ = t` be read in the rotated coordinate `w = conj ζ * z`.

## Main declarations

* `Complex.mul_conj_eq_one_of_norm_eq_one` -- a unit complex number times its conjugate is `1`.
* `Complex.inner_mul_left_of_norm_eq_one` -- `⟪ζ, ζ * w⟫_ℝ = w.re` for a unit `ζ`.
* `Complex.inner_mul_mul_of_norm_eq_one` -- `⟪ζ * a, ζ * b⟫_ℝ = ⟪a, b⟫_ℝ` for a unit `ζ`.
* `Complex.eq_of_sum_mul_eq_of_norm_eq_one` -- positively weighted unit complex numbers whose
  weighted sum has the maximal absolute value all equal the common phase.
* `Complex.real_inner_I_right` -- `⟪z, i⟫_ℝ = z.im`: the height of `z` in the direction of `i`.
* `LinearIsometry.norm_map_I` -- a linear isometry from the plane maps `i` to a unit vector.
-/

public section

namespace Complex

variable {ζ : ℂ}

/-- A complex number of norm `1` times its conjugate is `1`. -/
theorem mul_conj_eq_one_of_norm_eq_one (hζ : ‖ζ‖ = 1) : ζ * (starRingEnd ℂ) ζ = 1 := by
  rw [mul_conj', hζ]
  norm_num

/-- **Weighted unit complex numbers of the maximal sum point the same way.** If the unit complex
numbers `z i`, `i ∈ s`, with positive real weights `d i` have weighted sum `μ₀ * ∑ d i` for a
unit `μ₀`, then every `z i` equals `μ₀`: after rotating by `conj μ₀`, the weighted sum is the sum
of the norms, so every rotated term is its own norm. -/
theorem eq_of_sum_mul_eq_of_norm_eq_one {ι : Type*} {s : Finset ι} {z : ι → ℂ} {d : ι → ℝ}
    {μ₀ : ℂ} (hμ₀ : ‖μ₀‖ = 1) (hd : ∀ i ∈ s, 0 < d i) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hsum : ∑ i ∈ s, (d i : ℂ) * z i = μ₀ * ∑ i ∈ s, (d i : ℂ)) :
    ∀ i ∈ s, z i = μ₀ := by
  have hkey : ∑ i ∈ s, (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i) = ∑ i ∈ s, (d i : ℂ) := by
    calc ∑ i ∈ s, (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)
        = (starRingEnd ℂ) μ₀ * ∑ i ∈ s, (d i : ℂ) * z i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = ∑ i ∈ s, (d i : ℂ) := by
          rw [hsum, ← mul_assoc, mul_comm _ μ₀, mul_conj_eq_one_of_norm_eq_one hμ₀, one_mul]
  have hnorm : ∀ i ∈ s, ‖(d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)‖ = d i := fun i hi ↦ by
    rw [norm_mul, norm_mul, Complex.norm_conj, hμ₀, hz i hi, Complex.norm_real,
      Real.norm_of_nonneg (hd i hi).le]
    ring
  intro i hi
  have h := RCLike.eq_norm_of_sum_eq_sum_norm
    (z := fun i ↦ (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)) (s := s)
    (by
      rw [hkey, Finset.sum_congr rfl hnorm]
      push_cast
      rfl) hi
  rw [hnorm i hi] at h
  have h1 : (starRingEnd ℂ) μ₀ * z i = 1 :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (hd i hi).ne') (by simpa using h)
  calc z i = μ₀ * ((starRingEnd ℂ) μ₀ * z i) := by
        rw [← mul_assoc, mul_conj_eq_one_of_norm_eq_one hμ₀, one_mul]
    _ = μ₀ := by rw [h1, mul_one]

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

end Complex

/-- A linear isometry from the plane maps `i` to a unit vector. -/
theorem LinearIsometry.norm_map_I {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι Complex.I‖ = 1 :=
  (ι.norm_map _).trans Complex.norm_I
