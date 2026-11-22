/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Rapid decay of integral convolutions on a smaller cone

Let `F` grow at most polynomially on a finite-dimensional real normed space `E` and decay rapidly
on a set `Γ` of frequencies, and let `K θ ζ` be a kernel rapidly decreasing in `θ`, with at most
polynomial growth in `ζ`. Then the convolution-type integral `η ↦ ∫ K (η - ζ) ζ (F ζ) dζ` decays
rapidly on every set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)`, `c > 0`, lie in `Γ`.
The points `ζ` of the closed ball evaluate `F` inside `Γ` at frequencies of size comparable to
`‖η‖`, and the remaining points have `‖η - ζ‖` comparable to `‖η‖` or larger, where the decay of
the kernel wins.

This is the integral form of `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`, and rests on
the same pointwise bound `TauCeti.exists_one_add_norm_pow_mul_norm_apply_sub_le`. It shows that
a pseudodifferential operator with compact spatial support, whose output has Fourier transform
`∫ â(η - ζ, ζ) û(ζ) dζ` with `â` the Fourier transform of the symbol in the position, preserves
rapid decay of `û` in a cone, up to shrinking the cone.

## Main declarations

* `TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`: the decay bound above, order by order.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Lemma 8.1.1.
-/

public section

open MeasureTheory Module Metric

namespace TauCeti

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
  obtain ⟨D, -, hD⟩ := exists_one_add_norm_pow_mul_norm_apply_sub_le hF hc hΓ' hdecay
  set P := N + 2 * (M + k)
  set r := finrank ℝ E + 1
  obtain ⟨A, hA⟩ := hK (r + P)
  -- The integrable majorant `κ θ = (1 + ‖θ‖) ^ (-r)`.
  set κ : E → ℝ := fun θ ↦ (1 + ‖θ‖) ^ (-(r : ℝ))
  have hκ : Integrable κ μ := integrable_one_add_norm (by simp [r])
  refine ⟨A * D * ∫ θ, κ θ ∂μ, fun η hη ↦ ?_⟩
  -- The pointwise bound `(1 + ‖η‖) ^ N ‖K θ ζ (F ζ)‖ ≤ A D κ θ` for `ζ = η - θ`: the kernel
  -- absorbs the weight `(1 + ‖ζ‖) ^ M (1 + ‖θ‖) ^ (r + P)`.
  have hpt (θ : E) : (1 + ‖η‖) ^ N * ‖K θ (η - θ) (F (η - θ))‖ ≤ A * D * κ θ := by
    have hw : 0 < (1 + ‖η - θ‖) ^ M * (1 + ‖θ‖) ^ P := by positivity
    simp only [κ, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ hw
    calc (1 + ‖η‖) ^ N * ‖K θ (η - θ) (F (η - θ))‖ * (1 + ‖θ‖) ^ r *
          ((1 + ‖η - θ‖) ^ M * (1 + ‖θ‖) ^ P)
        ≤ (1 + ‖η‖) ^ N * (‖K θ (η - θ)‖ * ‖F (η - θ)‖) * (1 + ‖θ‖) ^ r *
          ((1 + ‖η - θ‖) ^ M * (1 + ‖θ‖) ^ P) := by gcongr; exact (K θ (η - θ)).le_opNorm _
      _ = ((1 + ‖θ‖) ^ (r + P) * ‖K θ (η - θ)‖) *
          ((1 + ‖η‖) ^ N * ((1 + ‖η - θ‖) ^ M * ‖F (η - θ)‖)) := by ring
      _ ≤ (A * (1 + ‖η - θ‖) ^ M) * (D * (1 + ‖θ‖) ^ P) :=
        mul_le_mul (hA θ _) (hD η hη θ) (by positivity)
          ((by positivity : (0 : ℝ) ≤ (1 + ‖θ‖) ^ (r + P) * ‖K θ (η - θ)‖).trans (hA θ _))
      _ = A * D * ((1 + ‖η - θ‖) ^ M * (1 + ‖θ‖) ^ P) := by ring
  have hint : Integrable (fun ζ ↦ A * D * κ (ζ - η)) μ := (hκ.comp_sub_right η).const_mul _
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  have hbound : ‖∫ ζ, K (η - ζ) ζ (F ζ) ∂μ‖ ≤ ∫ ζ, ((1 + ‖η‖) ^ N)⁻¹ * (A * D * κ (ζ - η)) ∂μ :=
    norm_integral_le_of_norm_le (hint.const_mul _) (ae_of_all _ fun ζ ↦ by
      rw [← div_eq_inv_mul, le_div_iff₀ hp, mul_comm]
      simpa only [κ, norm_sub_rev η ζ, sub_sub_cancel] using hpt (η - ζ))
  rw [integral_const_mul, integral_const_mul, integral_sub_right_eq_self (fun θ ↦ κ θ) η]
    at hbound
  calc (1 + ‖η‖) ^ N * ‖∫ ζ, K (η - ζ) ζ (F ζ) ∂μ‖
      ≤ (1 + ‖η‖) ^ N * (((1 + ‖η‖) ^ N)⁻¹ * (A * D * ∫ θ, κ θ ∂μ)) := by gcongr
    _ = A * D * ∫ θ, κ θ ∂μ := by field_simp

end TauCeti
