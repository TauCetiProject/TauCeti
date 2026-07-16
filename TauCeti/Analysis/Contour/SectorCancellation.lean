/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.TangentForcing
import TauCeti.Analysis.Contour.HigherOrderAsymptotics

/-!
# Sector-even cancellation at a flat crossing

For a curve crossing a pole `s` of the Laurent term `c / (z - s)^k` (`k ≥ 2`), the two branch
contributions to the principal value cancel when the one-sided tangent directions satisfy the
power identity `(L₊ / ‖L₊‖)^(k-1) = (-L₋ / ‖L₋‖)^(k-1)` — condition (B) of Hungerbühler–Wasem,
their equation 3.4: `PV ∮ dz/zⁿ = lim (1 - e^{-i(n-1)α}) / ((n-1)ε^{n-1})`, which vanishes
whenever `(n-1)α ∈ 2πℤ`.

This file contributes the antiderivative-difference half of that mechanism, for the
antiderivative `F(z) = -1/((k-1)(z-s)^(k-1))` of `z ↦ (z - s)^(-k)`:

## Main results

* `Contour.antiderivative_tangent_target_eq_of_pow_eq` — under the power identity, `F` takes
  equal values at the two chord targets `s + ε • (L₊ / ‖L₊‖)` and `s + ε • (-L₋ / ‖L₋‖)`.
* `Contour.antiderivative_diff_across_crossing_tendsto_zero` — for a curve flat of order
  `n ≥ k` at the crossing with one-sided tangents `L₋`, `L₊`, the difference of `F` along the
  curve across the crossing, evaluated at exit times from the `ε`-disc on each side, tends to
  `0` as `ε → 0⁺`.

## Provenance

Migrated from `F_line_diff_eq_zero_under_conditionB` and
`F_curve_diff_tendsto_zero_under_conditionB` of `SectorCancellation.lean` in the AINTLIB
`LeanModularForms` development. There the flatness hypothesis is tangent-indexed
(`IsFlatOfOrder`), so the deviation bounds feed in directly; here `Contour.FlatOfOrder`
quantifies its witness directions existentially, and the tangent-forcing bridge
(`FlatOfOrder.tangentDeviation_isLittleO_right/left`) recovers them. See N. Hungerbühler,
M. Wasem, *Non-integer valued winding numbers and a generalized Residue Theorem*,
arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **Equal antiderivative values at the two chord targets.** For the antiderivative
`F(z) = -1/((k-1)(z-s)^(k-1))` and tangent directions `L₊` (rightward) and `-L₋` (the left
tangent, used inward), the values at the radius-`ε` chord targets agree under the power
identity `(L₊ / ‖L₊‖)^(k-1) = (-L₋ / ‖L₋‖)^(k-1)` — condition (B) of Hungerbühler–Wasem. For
`k` odd the identity holds automatically, since `k - 1` is even. -/
theorem antiderivative_tangent_target_eq_of_pow_eq (s L_minus L_plus : ℂ) (k : ℕ)
    (h_B : (L_plus / (‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (‖L_minus‖ : ℂ)) ^ (k - 1)) (ε : ℝ) :
    -(↑(k - 1) : ℂ)⁻¹ * (((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹ =
    -(↑(k - 1) : ℂ)⁻¹ * (((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1))⁻¹ := by
  have h_smul : ∀ (r : ℝ) (v : ℂ), ((ε / r : ℝ) • v : ℂ) = (ε : ℂ) * (v / (r : ℂ)) := by
    intro r v
    rw [Complex.real_smul]
    push_cast
    rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [add_sub_cancel_left, add_sub_cancel_left, h_smul ‖L_plus‖ L_plus,
    h_smul ‖L_minus‖ (-L_minus), mul_pow, mul_pow, h_B]

/-- **The antiderivative difference across a flat crossing tends to zero.** For a curve flat of
order `n` at `t₀` over the pole `s = γ t₀`, with one-sided tangents `L₋` (left) and `L₊`
(right) satisfying the condition-(B) power identity, and exit times `t_eps_plus`, `t_eps_minus`
reaching radius `ε` on each side: the difference of `F(z) = -1/((k-1)(z-s)^(k-1))` along the
curve between the two exits tends to `0` as `ε → 0⁺` (`2 ≤ k ≤ n`). This is the cancellation
half of the Hungerbühler–Wasem principal-value mechanism at a condition-(B) crossing. -/
theorem antiderivative_diff_across_crossing_tendsto_zero
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ}
    (h_flat : FlatOfOrder γ t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L_plus (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_minus (Iio t₀) t₀)
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_B : (L_plus / (‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (‖L_minus‖ : ℂ)) ^ (k - 1))
    {t_eps_plus t_eps_minus : ℝ → ℝ}
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  subst h_s
  have hn1 : 1 ≤ n := by omega
  have h_right := antiderivative_diff_at_tangent_target_tendsto_zero_right hL_plus
    h_deriv_right rfl (h_flat.tangentDeviation_isLittleO_right hn1 hL_plus h_deriv_right) hk hkn
  have h_left := antiderivative_diff_at_tangent_target_tendsto_zero_left hL_minus
    h_deriv_left rfl (h_flat.tangentDeviation_isLittleO_left hn1 hL_minus h_deriv_left) hk hkn
  have h_sum := (h_right.comp h_plus_to).add (h_left.comp h_minus_to)
  rw [add_zero] at h_sum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  simp only [Function.comp_apply]
  have h_targets :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((γ t₀ + (‖γ (t_eps_minus ε) - γ t₀‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - γ t₀)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((γ t₀ + (‖γ (t_eps_plus ε) - γ t₀‖ / ‖L_plus‖ : ℝ) • L_plus) - γ t₀)
          ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    exact (antiderivative_tangent_target_eq_of_pow_eq (γ t₀) L_minus L_plus k h_B ε).symm
  rw [h_targets]
  have htri : ∀ A B TR : ℂ, ‖A - B‖ ≤ ‖B - TR‖ + ‖A - TR‖ := by
    intro A B TR
    rw [← sub_sub_sub_cancel_right A B TR]
    exact (norm_sub_le _ _).trans_eq (add_comm _ _)
  exact htri _ _ _

end TauCeti.Contour

end
