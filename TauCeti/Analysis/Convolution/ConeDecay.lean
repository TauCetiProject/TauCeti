/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Rapid decay of a convolution on a set of frequencies

Let `F` and `G` be functions on a finite-dimensional real normed space which grow at most
polynomially and decay rapidly off sets `U₁` and `U₂`. The convolution
`ζ ↦ ∫ F η G (ζ - η) dη` decays rapidly on every set `Γ` of frequencies `ζ` for which, whenever
`η ∈ U₁`, the point `ζ - η` lies off `U₂` and is comparable to `ζ`, and whenever `ζ - η ∈ U₂`, the
point `η` is comparable to `ζ`. Then for every `η` at least one of the two factors is evaluated
where it decays, at a point comparable to `ζ`, or both factors decay.

This is how the localized Fourier transform of a product of distributions, which is a convolution
of the localized Fourier transforms of the factors, decays in a cone of frequencies outside the
sums of the frequencies of the wave front sets of the factors. There `U₁` and `U₂` are conic
neighbourhoods of these frequencies.

## Main results

* `TauCeti.exists_one_add_norm_pow_mul_norm_mul_le`: the pointwise bound on the weighted
  integrand `F η G (ζ - η)`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_integral_mul_le`: rapid decay of the convolution on
  `Γ`.
-/

public section

open MeasureTheory Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- One factor of the convolution integrand decays at `u` and the other grows at most polynomially
at `v`, where `u + v = ζ` and `c ‖ζ‖ ≤ ‖u‖`. Then `(1 + ‖ζ‖) ^ M X Y` is bounded by a multiple of
`(1 + ‖u‖) ^ (-d)`. -/
private theorem one_add_norm_pow_mul_mul_mul_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {ζ u v : E}
    (huv : u + v = ζ) (hcu : c * ‖ζ‖ ≤ ‖u‖) {X Y B C : ℝ} {k M d : ℕ} (hX0 : 0 ≤ X)
    (hB : 0 ≤ B) (hY0 : 0 ≤ Y) (hY : Y ≤ B * (1 + ‖v‖) ^ k)
    (hX : (1 + ‖u‖) ^ (M + k + d) * X ≤ C) :
    (1 + ‖ζ‖) ^ M * (X * Y) * (1 + ‖u‖) ^ d ≤ B * ((1 + c⁻¹) ^ k * c⁻¹ ^ M) * C := by
  have hc' : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc1
  have hζ : ‖ζ‖ ≤ c⁻¹ * ‖u‖ := by rwa [le_inv_mul_iff₀ hc]
  have hv : ‖v‖ ≤ ‖ζ‖ + ‖u‖ := by
    rw [← huv, add_comm u v]
    simpa using norm_sub_le (v + u) u
  have hz : 1 + ‖ζ‖ ≤ c⁻¹ * (1 + ‖u‖) := by nlinarith [norm_nonneg u]
  have hb : 1 + ‖v‖ ≤ (1 + c⁻¹) * (1 + ‖u‖) := by nlinarith [norm_nonneg u]
  calc (1 + ‖ζ‖) ^ M * (X * Y) * (1 + ‖u‖) ^ d
      ≤ (c⁻¹ * (1 + ‖u‖)) ^ M * (X * (B * ((1 + c⁻¹) * (1 + ‖u‖)) ^ k)) * (1 + ‖u‖) ^ d := by
        gcongr
        exact hY.trans (by gcongr)
    _ = B * ((1 + c⁻¹) ^ k * c⁻¹ ^ M) * ((1 + ‖u‖) ^ (M + k + d) * X) := by
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring
    _ ≤ B * ((1 + c⁻¹) ^ k * c⁻¹ ^ M) * C := by gcongr

/-- If `X b ≤ D` or `X a ≤ D`, then `X (a b) ≤ D (a + b)`. -/
private theorem mul_mul_le_mul_add_of_le_or_le {X a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD : 0 ≤ D) (h : X * b ≤ D ∨ X * a ≤ D) : X * (a * b) ≤ D * (a + b) := by
  rcases h with h | h
  · nlinarith [mul_le_mul_of_nonneg_right h ha, mul_nonneg hD hb]
  · nlinarith [mul_le_mul_of_nonneg_right h hb, mul_nonneg hD ha]

/-- The pointwise bound behind `exists_one_add_norm_pow_mul_norm_integral_mul_le`: for `ζ ∈ Γ`,
the integrand `F η G (ζ - η)`, weighted by `(1 + ‖ζ‖) ^ M`, is bounded by a multiple of
`(1 + ‖η‖) ^ (-d) + (1 + ‖ζ - η‖) ^ (-d)`. -/
theorem exists_one_add_norm_pow_mul_norm_mul_le {F G : E → ℂ} {A B : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hFk : ∀ η, ‖F η‖ ≤ A * (1 + ‖η‖) ^ k)
    (hGk : ∀ θ, ‖G θ‖ ≤ B * (1 + ‖θ‖) ^ k) {U₁ U₂ : Set E}
    (hF : ∀ N : ℕ, ∃ C, 0 ≤ C ∧ ∀ η ∈ U₁ᶜ, (1 + ‖η‖) ^ N * ‖F η‖ ≤ C)
    (hG : ∀ N : ℕ, ∃ C, 0 ≤ C ∧ ∀ θ ∈ U₂ᶜ, (1 + ‖θ‖) ^ N * ‖G θ‖ ≤ C) {Γ : Set E} {c : ℝ}
    (hc : 0 < c) (hΓ : ∀ ζ ∈ Γ, ∀ η, (η ∈ U₁ → ζ - η ∉ U₂ ∧ c * ‖ζ‖ ≤ ‖ζ - η‖) ∧
      (ζ - η ∈ U₂ → c * ‖ζ‖ ≤ ‖η‖)) (M d : ℕ) :
    ∃ D, ∀ ζ ∈ Γ, ∀ η, (1 + ‖ζ‖) ^ M * ‖F η * G (ζ - η)‖ * ((1 + ‖η‖) ^ d * (1 + ‖ζ - η‖) ^ d) ≤
      D * ((1 + ‖η‖) ^ d + (1 + ‖ζ - η‖) ^ d) := by
  obtain ⟨CF, hCF0, hCF⟩ := hF (M + k + d)
  obtain ⟨CG, hCG0, hCG⟩ := hG (M + k + d)
  set c' := min c 1
  have hc' : 0 < c' := lt_min hc one_pos
  set L := (1 + c'⁻¹) ^ k * c'⁻¹ ^ M
  have hL : 0 ≤ L := by positivity
  set D := CF * CG + A * L * CG + B * L * CF
  have hK₁ : A * L * CG ≤ D := by nlinarith [mul_nonneg hB hL, mul_nonneg hCF0 hCG0]
  have hK₂ : B * L * CF ≤ D := by nlinarith [mul_nonneg hA hL, mul_nonneg hCF0 hCG0]
  have hK₃ : CF * CG ≤ D := by nlinarith [mul_nonneg hA hL, mul_nonneg hB hL, hCG0]
  refine ⟨D, fun ζ hζ η ↦ ?_⟩
  have hc'ζ {u : E} (h : c * ‖ζ‖ ≤ ‖u‖) : c' * ‖ζ‖ ≤ ‖u‖ :=
    (mul_le_mul_of_nonneg_right (min_le_left c 1) (norm_nonneg ζ)).trans h
  set a := 1 + ‖η‖
  set b := 1 + ‖ζ - η‖
  have ha : 1 ≤ a := le_add_of_nonneg_right (norm_nonneg _)
  have hb : 1 ≤ b := le_add_of_nonneg_right (norm_nonneg _)
  rw [norm_mul]
  refine mul_mul_le_mul_add_of_le_or_le (by positivity) (by positivity)
    ((mul_nonneg hCF0 hCG0).trans hK₃) ?_
  by_cases h₁ : η ∈ U₁
  · -- `G` decays at `ζ - η`, which is comparable to `ζ`.
    obtain ⟨h₂, hcη⟩ := (hΓ ζ hζ η).1 h₁
    refine Or.inl (le_trans ?_ hK₁)
    rw [mul_comm (‖F η‖)]
    exact one_add_norm_pow_mul_mul_mul_le hc' (min_le_right c 1) (sub_add_cancel ζ η)
      (hc'ζ hcη) (norm_nonneg _) hA (norm_nonneg _) (hFk η) (hCG _ h₂)
  refine Or.inr ?_
  by_cases h₂ : ζ - η ∈ U₂
  · -- `F` decays at `η`, which is comparable to `ζ`.
    exact le_trans (one_add_norm_pow_mul_mul_mul_le hc' (min_le_right c 1) (add_sub_cancel η ζ)
      (hc'ζ ((hΓ ζ hζ η).2 h₂)) (norm_nonneg _) hB (norm_nonneg _) (hGk _) (hCF η h₁)) hK₂
  · -- Both factors decay.
    refine le_trans ?_ hK₃
    have hab : 1 + ‖ζ‖ ≤ a * b := by
      have : ‖ζ‖ ≤ ‖η‖ + ‖ζ - η‖ := by simpa using norm_add_le η (ζ - η)
      nlinarith [norm_nonneg η, norm_nonneg (ζ - η)]
    have h₃ : a ^ (M + d) ≤ a ^ (M + k + d) := pow_le_pow_right₀ ha (by omega)
    have h₄ : b ^ M ≤ b ^ (M + k + d) := pow_le_pow_right₀ hb (by omega)
    calc (1 + ‖ζ‖) ^ M * (‖F η‖ * ‖G (ζ - η)‖) * a ^ d
        ≤ (a * b) ^ M * (‖F η‖ * ‖G (ζ - η)‖) * a ^ d := by gcongr
      _ = (a ^ (M + d) * ‖F η‖) * (b ^ M * ‖G (ζ - η)‖) := by rw [pow_add, mul_pow]; ring
      _ ≤ (a ^ (M + k + d) * ‖F η‖) * (b ^ (M + k + d) * ‖G (ζ - η)‖) := by gcongr
      _ ≤ CF * CG := mul_le_mul (hCF η h₁) (hCG _ h₂) (by positivity) hCF0

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Rapid decay of the convolution `ζ ↦ ∫ F η G (ζ - η) dμ(η)` on a set `Γ` of frequencies, where
`F` and `G` grow at most polynomially and decay rapidly off `U₁` and off `U₂`. For `ζ ∈ Γ`,
whenever `η ∈ U₁`, so that `F η` need not be small, `ζ - η` lies off `U₂` and is comparable to `ζ`,
and whenever `ζ - η ∈ U₂`, `η` is comparable to `ζ`. -/
theorem exists_one_add_norm_pow_mul_norm_integral_mul_le {F G : E → ℂ} {A B : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hFk : ∀ η, ‖F η‖ ≤ A * (1 + ‖η‖) ^ k)
    (hGk : ∀ θ, ‖G θ‖ ≤ B * (1 + ‖θ‖) ^ k) {U₁ U₂ : Set E}
    (hF : ∀ N : ℕ, ∃ C, 0 ≤ C ∧ ∀ η ∈ U₁ᶜ, (1 + ‖η‖) ^ N * ‖F η‖ ≤ C)
    (hG : ∀ N : ℕ, ∃ C, 0 ≤ C ∧ ∀ θ ∈ U₂ᶜ, (1 + ‖θ‖) ^ N * ‖G θ‖ ≤ C) {Γ : Set E} {c : ℝ}
    (hc : 0 < c) (hΓ : ∀ ζ ∈ Γ, ∀ η, (η ∈ U₁ → ζ - η ∉ U₂ ∧ c * ‖ζ‖ ≤ ‖ζ - η‖) ∧
      (ζ - η ∈ U₂ → c * ‖ζ‖ ≤ ‖η‖)) (M : ℕ) :
    ∃ C, ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ M * ‖∫ η, F η * G (ζ - η) ∂μ‖ ≤ C := by
  set d := finrank ℝ E + 1
  obtain ⟨D, hD⟩ := exists_one_add_norm_pow_mul_norm_mul_le hA hB hFk hGk hF hG hc hΓ M d
  set w : E → ℝ := fun θ ↦ (1 + ‖θ‖) ^ (-(d : ℝ))
  have hw (θ : E) : w θ = ((1 + ‖θ‖) ^ d)⁻¹ := by
    simp only [w, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖θ‖), Real.rpow_natCast]
  have hint : Integrable w μ := integrable_one_add_norm (by simp [d])
  have hint' (ζ : E) : Integrable (fun η ↦ D * w η + D * w (ζ - η)) μ :=
    (hint.const_mul D).add ((hint.comp_sub_left ζ).const_mul D)
  refine ⟨2 * D * ∫ θ, w θ ∂μ, fun ζ hζ ↦ ?_⟩
  calc (1 + ‖ζ‖) ^ M * ‖∫ η, F η * G (ζ - η) ∂μ‖
      = ‖∫ η, ((1 + ‖ζ‖) ^ M : ℂ) * (F η * G (ζ - η)) ∂μ‖ := by
        rw [integral_const_mul, norm_mul]
        norm_cast
        rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ ∫ η, (D * w η + D * w (ζ - η)) ∂μ := by
        refine norm_integral_le_of_norm_le (hint' ζ) (ae_of_all _ fun η ↦ ?_)
        rw [norm_mul]
        norm_cast
        rw [Real.norm_of_nonneg (by positivity), hw, hw]
        field_simp
        linarith [hD ζ hζ η]
    _ = 2 * D * ∫ θ, w θ ∂μ := by
        rw [integral_add (hint.const_mul D) ((hint.comp_sub_left ζ).const_mul D),
          integral_const_mul, integral_const_mul, integral_sub_left_eq_self]
        ring

end TauCeti
