/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

import Mathlib.MeasureTheory.Group.Integral

/-!
# Rapid decay of integral convolutions on a smaller cone

Let `F` grow at most polynomially on a finite-dimensional real normed space `E` and decay rapidly
on a set `Γ` of frequencies, and let `K θ ζ` be a kernel rapidly decreasing in `θ`, with at most
polynomial growth in `ζ`. Then the convolution-type integral `η ↦ ∫ K (η - ζ) ζ (F ζ) dζ` decays
rapidly on every set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)`, `c > 0`, lie in `Γ`.
The points `ζ` of the closed ball evaluate `F` inside `Γ` at frequencies of size comparable to
`‖η‖`, and the remaining points have `‖η - ζ‖` comparable to `‖η‖` or larger, where the decay of
the kernel wins.

This is the integral form of `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`. It shows that
a pseudodifferential operator with compact spatial support, whose output has Fourier transform
`∫ â(η - ζ, ζ) û(ζ) dζ` with `â` the Fourier transform of the symbol in the position, preserves
rapid decay of `û` in a cone, up to shrinking the cone.

## Main declarations

* `TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`: the decay bound above, order by order.
-/

public section

open MeasureTheory Module Metric

namespace TauCeti

section Pointwise

variable {E : Type*} [NormedAddCommGroup E]

/-- The pointwise bound near the diagonal: if `‖η - ζ‖ ≤ ‖η‖ / 2`, then `1 + ‖η‖ ≤ 2 (1 + ‖ζ‖)`,
and the decay of `F` at `ζ` controls the integrand. -/
private theorem one_add_norm_pow_mul_mul_le_of_near {η ζ : E} {k₀ f A C₁ : ℝ} {r j N M : ℕ}
    (hrj : r ≤ j) (hnear : ‖η - ζ‖ ≤ ‖η‖ / 2) (hk₀ : 0 ≤ k₀) (hf : 0 ≤ f) (hA : 0 ≤ A)
    (hK : (1 + ‖η - ζ‖) ^ j * k₀ ≤ A * (1 + ‖ζ‖) ^ M) (hF : (1 + ‖ζ‖) ^ (N + M) * f ≤ C₁) :
    (1 + ‖η‖) ^ N * (k₀ * f) * (1 + ‖η - ζ‖) ^ r ≤ 2 ^ N * A * C₁ := by
  have hle : 1 + ‖η‖ ≤ 2 * (1 + ‖ζ‖) := by
    have := norm_le_norm_add_norm_sub' η ζ
    nlinarith [norm_nonneg η]
  have hK' : (1 + ‖η - ζ‖) ^ r * k₀ ≤ A * (1 + ‖ζ‖) ^ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg (η - ζ)]) hrj)
      hk₀).trans hK
  calc (1 + ‖η‖) ^ N * (k₀ * f) * (1 + ‖η - ζ‖) ^ r
      = ((1 + ‖η - ζ‖) ^ r * k₀) * ((1 + ‖η‖) ^ N * f) := by ring
    _ ≤ (A * (1 + ‖ζ‖) ^ M) * ((2 * (1 + ‖ζ‖)) ^ N * f) := by gcongr
    _ = 2 ^ N * A * ((1 + ‖ζ‖) ^ (N + M) * f) := by rw [mul_pow, pow_add]; ring
    _ ≤ 2 ^ N * A * C₁ := by gcongr

/-- The pointwise bound away from the diagonal: if `c ‖η‖ < ‖η - ζ‖` with `0 < c ≤ 1`, then
`1 + ‖η‖` and `1 + ‖ζ‖` are controlled by `1 + ‖η - ζ‖`, where the kernel decays. -/
private theorem one_add_norm_pow_mul_mul_le_of_far {η ζ : E} {k₀ f A C₀ c : ℝ} {r N M k : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hfar : c * ‖η‖ < ‖η - ζ‖) (hk₀ : 0 ≤ k₀) (hf : 0 ≤ f)
    (hK : (1 + ‖η - ζ‖) ^ (r + N + 2 * (M + k)) * k₀ ≤ A * (1 + ‖ζ‖) ^ M)
    (hF : f ≤ C₀ * (1 + ‖ζ‖) ^ k) :
    (1 + ‖η‖) ^ N * (k₀ * f) * (1 + ‖η - ζ‖) ^ r ≤ A * C₀ * c⁻¹ ^ (N + M + k) := by
  have hC₀ : 0 ≤ C₀ := by
    by_contra h
    nlinarith [pow_pos (by positivity : (0 : ℝ) < 1 + ‖ζ‖) k]
  set θ := η - ζ
  have hη : 1 + ‖η‖ ≤ c⁻¹ * (1 + ‖θ‖) := by
    rw [le_inv_mul_iff₀ hc]
    nlinarith [norm_nonneg η]
  have hζ : 1 + ‖ζ‖ ≤ c⁻¹ * (1 + ‖θ‖) ^ 2 := by
    have : ‖ζ‖ ≤ ‖η‖ + ‖θ‖ := by
      have := norm_le_norm_add_norm_sub' ζ η
      rwa [norm_sub_rev] at this
    calc 1 + ‖ζ‖ ≤ (1 + ‖η‖) * (1 + ‖θ‖) := by nlinarith [norm_nonneg η, norm_nonneg θ]
      _ ≤ c⁻¹ * (1 + ‖θ‖) * (1 + ‖θ‖) := by gcongr
      _ = c⁻¹ * (1 + ‖θ‖) ^ 2 := by ring
  have hζM : (1 + ‖ζ‖) ^ M * (1 + ‖θ‖) ^ (2 * M) * c⁻¹ ^ M ≥ (1 + ‖ζ‖) ^ M * (1 + ‖ζ‖) ^ M := by
    rw [mul_assoc, pow_mul, ← mul_pow]
    gcongr
    linarith
  calc (1 + ‖η‖) ^ N * (k₀ * f) * (1 + ‖θ‖) ^ r
      ≤ (c⁻¹ * (1 + ‖θ‖)) ^ N * (k₀ * (C₀ * (c⁻¹ * (1 + ‖θ‖) ^ 2) ^ k)) * (1 + ‖θ‖) ^ r := by
        have h₁ : f ≤ C₀ * (c⁻¹ * (1 + ‖θ‖) ^ 2) ^ k := hF.trans (by gcongr)
        gcongr
    _ = C₀ * c⁻¹ ^ (N + k) * ((1 + ‖θ‖) ^ (r + N + 2 * k) * k₀) := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring
    _ ≤ C₀ * c⁻¹ ^ (N + k) * ((1 + ‖θ‖) ^ (r + N + 2 * k) * k₀) *
          ((1 + ‖θ‖) ^ (2 * M) * c⁻¹ ^ M / (1 + ‖ζ‖) ^ M) := by
        refine le_mul_of_one_le_right (by positivity) ?_
        rw [one_le_div (by positivity)]
        nlinarith [pow_pos (by positivity : 0 < 1 + ‖ζ‖) M]
    _ = C₀ * c⁻¹ ^ (N + M + k) * ((1 + ‖θ‖) ^ (r + N + 2 * (M + k)) * k₀) / (1 + ‖ζ‖) ^ M := by
        field_simp
        ring
    _ ≤ C₀ * c⁻¹ ^ (N + M + k) * (A * (1 + ‖ζ‖) ^ M) / (1 + ‖ζ‖) ^ M := by gcongr
    _ = A * C₀ * c⁻¹ ^ (N + M + k) := by field_simp

end Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Rapid decay of an integral convolution on a smaller cone.** Let `F` grow at most polynomially,
and let the kernel `K θ ζ` satisfy `(1 + ‖θ‖) ^ j ‖K θ ζ‖ ≤ A_j (1 + ‖ζ‖) ^ M` for every `j`. If
`(1 + ‖η‖) ^ (N + M) ‖F η‖` is bounded on a set `Γ`, and the closed ball of radius `c ‖η‖` about
every `η ∈ Γ'` lies in `Γ`, then `(1 + ‖η‖) ^ N ‖∫ K (η - ζ) ζ (F ζ) dζ‖` is bounded on `Γ'`. -/
theorem exists_one_add_norm_pow_mul_norm_integral_le {𝕜 G H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedSpace ℝ H] {K : E → E → G →L[𝕜] H} {M : ℕ}
    (hK : ∀ j : ℕ, ∃ A, ∀ θ ζ, (1 + ‖θ‖) ^ j * ‖K θ ζ‖ ≤ A * (1 + ‖ζ‖) ^ M) {F : E → G} {C₀ : ℝ}
    {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {N : ℕ}
    (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (N + M) * ‖F η‖ ≤ C) :
    ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖∫ ζ, K (η - ζ) ζ (F ζ) ∂μ‖ ≤ C := by
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  obtain ⟨C₁, hC₁⟩ := hdecay
  set r := finrank ℝ E + 1
  obtain ⟨A, hA⟩ := hK (r + N + 2 * (M + k))
  have hA0 : 0 ≤ A := by
    have := hA 0 0
    simp only [norm_zero, add_zero, one_pow, one_mul, mul_one] at this
    exact (norm_nonneg _).trans this
  set D := max (2 ^ N * A * C₁) (A * C₀ * c'⁻¹ ^ (N + M + k))
  -- The integrable majorant `κ θ = (1 + ‖θ‖) ^ (-r)`.
  set κ : E → ℝ := fun θ ↦ (1 + ‖θ‖) ^ (-(r : ℝ))
  have hκ : Integrable κ μ := integrable_one_add_norm (by simp [r])
  refine ⟨D * ∫ θ, κ θ ∂μ, fun η hη ↦ ?_⟩
  -- The pointwise bound `(1 + ‖η‖) ^ N ‖K (η - ζ) ζ (F ζ)‖ ≤ D κ (η - ζ)`.
  have hpt (ζ : E) : (1 + ‖η‖) ^ N * ‖K (η - ζ) ζ (F ζ)‖ ≤ D * κ (η - ζ) := by
    have hθpos : 0 < (1 + ‖η - ζ‖) ^ r := by positivity
    rw [show κ (η - ζ) = ((1 + ‖η - ζ‖) ^ r)⁻¹ by simp only [κ, Real.rpow_neg
      (by positivity : (0 : ℝ) ≤ 1 + ‖η - ζ‖), Real.rpow_natCast], ← div_eq_mul_inv,
      le_div_iff₀ hθpos]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((K (η - ζ) ζ).le_opNorm (F ζ)) (by positivity)) hθpos.le).trans ?_
    by_cases hnear : ‖η - ζ‖ ≤ c' * ‖η‖
    · have hmem : ζ ∈ Γ := hΓ' η hη (mem_closedBall.2 (by
        rw [dist_comm, dist_eq_norm]
        exact hnear.trans (by gcongr; exact min_le_left _ _)))
      exact (one_add_norm_pow_mul_mul_le_of_near (by omega)
        (hnear.trans (by nlinarith [min_le_right c (1 / 2), norm_nonneg η])) (norm_nonneg _)
        (norm_nonneg _) hA0 (hA _ _) (hC₁ ζ hmem)).trans (le_max_left _ _)
    · exact (one_add_norm_pow_mul_mul_le_of_far hc' ((min_le_right _ _).trans (by norm_num))
        (not_le.1 hnear) (norm_nonneg _) (norm_nonneg _) (hA _ _) (hF ζ)).trans (le_max_right _ _)
  have hint : Integrable (fun ζ ↦ D * κ (ζ - η)) μ := (hκ.comp_sub_right η).const_mul D
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  have hbound : ‖∫ ζ, K (η - ζ) ζ (F ζ) ∂μ‖ ≤ ∫ ζ, ((1 + ‖η‖) ^ N)⁻¹ * (D * κ (ζ - η)) ∂μ :=
    norm_integral_le_of_norm_le (hint.const_mul _) (ae_of_all _ fun ζ ↦ by
      rw [← div_eq_inv_mul, le_div_iff₀ hp, mul_comm]
      simpa only [κ, norm_sub_rev η ζ] using hpt ζ)
  rw [integral_const_mul, integral_const_mul, integral_sub_right_eq_self (fun θ ↦ κ θ) η]
    at hbound
  calc (1 + ‖η‖) ^ N * ‖∫ ζ, K (η - ζ) ζ (F ζ) ∂μ‖
      ≤ (1 + ‖η‖) ^ N * (((1 + ‖η‖) ^ N)⁻¹ * (D * ∫ θ, κ θ ∂μ)) := by gcongr
    _ = D * ∫ θ, κ θ ∂μ := by field_simp

end TauCeti
