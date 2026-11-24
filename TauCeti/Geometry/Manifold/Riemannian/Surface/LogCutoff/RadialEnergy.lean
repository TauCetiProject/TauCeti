/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Radial energy of the logarithmic cutoff profile

Let `L` be a continuous real-valued function on `[0, δ]` with `|L(t) - 2πt| ≤ C₁ t²`, as the
length of the geodesic circles of a surface is. For `0 < 4ε ≤ δ` and `Λ = log (δ / ε)`, the radial
energy `∫₀^δ ψ_ε'(t)² L(t) dt` of the logarithmic cutoff profile differs from `2π / Λ` by at most
`C / Λ²`, with `C` independent of `ε`. On `[2ε, δ / 2]`, where `ψ_ε' = 1 / (tΛ)`, the energy is
`Λ⁻² ∫ L(t) t⁻² dt`, which is `2π (Λ - 2 log 2) / Λ²` up to `C₁ δ / Λ²`. On each of `[ε, 2ε]` and
`[δ / 2, δ]` the bound `ψ_ε' ≤ c₀ / (tΛ)` and `|L(t)| ≤ (2π + C₁ δ) t` bound the absolute energy by
`c₀² (2π + C₁ δ) log 2 / Λ²`.

## Main results

* `TauCeti.abs_integral_deriv_logCutoffProfile_sq_mul_sub_le`: the energy bound, with the
  explicit constant `4π log 2 + 2 c₀² (2π + C₁ δ) log 2 + C₁ δ`.

## Attribution

Adapted from Giada Franz's radial-energy proof in
[ColdingMinicozziTheory at commit bd800bbe][source].

[source]: https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/bd800bbeea7e67e3f9a40a82d7f01b6eb45d71e9
-/

public section

open Real Set MeasureTheory intervalIntegral

namespace TauCeti

variable {ε δ C₁ : ℝ} {L : ℝ → ℝ}

private noncomputable def radialEnergyDensity (ε δ : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (logCutoffProfile ε δ) t ^ 2 * L t

private theorem intervalIntegrable_radialEnergyDensity
    (hε : 0 < ε) (hδ : 0 < δ) (hL : ContinuousOn L (Icc 0 δ))
    {a b : ℝ} (ha : a ∈ Icc 0 δ) (hb : b ∈ Icc 0 δ) :
    IntervalIntegrable (radialEnergyDensity ε δ L) volume a b := by
  unfold radialEnergyDensity
  simpa only [Pi.mul_def, Pi.pow_def] using
    ((((contDiff_logCutoffProfile hε hδ).continuous_deriv (by simp)).pow 2).continuousOn.mul
      hL |>.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

private theorem integral_radialEnergyDensity_split
    (hε : 0 < ε) (hεδ : 4 * ε ≤ δ) (hL : ContinuousOn L (Icc 0 δ)) :
    (∫ t in 0..δ, radialEnergyDensity ε δ L t) =
      (∫ t in ε..2 * ε, radialEnergyDensity ε δ L t) +
      (∫ t in 2 * ε..δ / 2, radialEnergyDensity ε δ L t) +
      ∫ t in δ / 2..δ, radialEnergyDensity ε δ L t := by
  have hδ : 0 < δ := by linarith
  have h2εδ : 2 * ε ≤ δ := by linarith
  have hfi {a b : ℝ} (ha : a ∈ Icc 0 δ) (hb : b ∈ Icc 0 δ) :=
    intervalIntegrable_radialEnergyDensity hε hδ hL ha hb
  have h0 : (0 : ℝ) ∈ Icc 0 δ := ⟨le_rfl, hδ.le⟩
  have h1 : ε ∈ Icc 0 δ := ⟨hε.le, by linarith⟩
  have h2 : 2 * ε ∈ Icc 0 δ := ⟨by linarith, by linarith⟩
  have h3 : δ / 2 ∈ Icc 0 δ := ⟨by linarith, by linarith⟩
  have h4 : δ ∈ Icc 0 δ := ⟨hδ.le, le_rfl⟩
  have hz : (∫ t in 0..ε, radialEnergyDensity ε δ L t) = 0 := by
    calc
      _ = ∫ _ in 0..ε, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hε.le] at ht
        simp [radialEnergyDensity, deriv_logCutoffProfile_eq_zero_of_le hε
          h2εδ ht.2]
      _ = 0 := intervalIntegral.integral_zero
  rw [← integral_add_adjacent_intervals (hfi h0 h3) (hfi h3 h4),
    ← integral_add_adjacent_intervals (hfi h0 h2) (hfi h2 h3),
    ← integral_add_adjacent_intervals (hfi h0 h1) (hfi h1 h2), hz, zero_add]

private theorem abs_integral_radialEnergyDensity_le
    (hε : 0 < ε) (hεδ : 4 * ε ≤ δ) (hL : ContinuousOn L (Icc 0 δ))
    {K a b : ℝ} (hLK : ∀ t ∈ Icc 0 δ, |L t| ≤ K * t) (ha : a ∈ Icc 0 δ) (hb : b ∈ Icc 0 δ)
    (ha0 : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, radialEnergyDensity ε δ L t| ≤
      logCutoffConst ^ 2 * K / Real.log (δ / ε) ^ 2 * Real.log (b / a) := by
  have hsub : Icc a b ⊆ Icc 0 δ := Icc_subset_Icc ha.1 hb.2
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  rw [← integral_inv_of_pos ha0 (ha0.trans_le hab), ← intervalIntegral.integral_const_mul]
  have hinv := (intervalIntegrable_inv_iff (a := a) (b := b)).mpr
    (.inr (by rw [uIcc_of_le hab]; exact fun h ↦ ha0.not_ge h.1))
  refine intervalIntegral.integral_mono_on hab
    (intervalIntegrable_radialEnergyDensity hε (by linarith) hL ha hb).abs
    (hinv.const_mul _) fun t ht ↦ ?_
  have ht0 : 0 < t := ha0.trans_le ht.1
  have h2εδ : 2 * ε ≤ δ := by linarith
  have hd0 := deriv_logCutoffProfile_nonneg hε h2εδ t
  have hd := deriv_logCutoffProfile_le hε hεδ ht0
  rw [radialEnergyDensity, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    deriv (logCutoffProfile ε δ) t ^ 2 * |L t| ≤
        (logCutoffConst / (t * Real.log (δ / ε))) ^ 2 * (K * t) :=
      mul_le_mul (pow_le_pow_left₀ hd0 hd 2) (hLK t (hsub ht)) (abs_nonneg _) (sq_nonneg _)
    _ = logCutoffConst ^ 2 * K / Real.log (δ / ε) ^ 2 * t⁻¹ := by field_simp

private theorem abs_integral_radialEnergyDensity_middle_sub_le
    (hε : 0 < ε) (hεδ : 4 * ε ≤ δ) (hL : ContinuousOn L (Icc 0 δ))
    (hC₁ : 0 ≤ C₁) (hLC : ∀ t ∈ Icc 0 δ, |L t - 2 * π * t| ≤ C₁ * t ^ 2) :
    let Λ := Real.log (δ / ε)
    |(∫ t in 2 * ε..δ / 2, radialEnergyDensity ε δ L t) -
      2 * π * (Λ - 2 * Real.log 2) / Λ ^ 2| ≤ C₁ / Λ ^ 2 * δ := by
  dsimp only
  set Λ := Real.log (δ / ε) with hΛdef
  have hΛ : 0 < Λ := Real.log_pos ((lt_div_iff₀ hε).2 (by linarith))
  have hδ : 0 < δ := by linarith
  have h2 : 2 * ε ∈ Icc 0 δ := ⟨by linarith, by linarith⟩
  have h3 : δ / 2 ∈ Icc 0 δ := ⟨by linarith, by linarith⟩
  have hfi := intervalIntegrable_radialEnergyDensity hε hδ hL h2 h3
  have hmid_eq :
      (∫ t in 2 * ε..δ / 2, radialEnergyDensity ε δ L t) -
        2 * π * (Λ - 2 * Real.log 2) / Λ ^ 2 =
      ∫ t in 2 * ε..δ / 2, (radialEnergyDensity ε δ L t - 2 * π / Λ ^ 2 * t⁻¹) := by
    have hinv := (intervalIntegrable_inv_iff (a := 2 * ε) (b := δ / 2)).mpr
      (.inr (by rw [uIcc_of_le (by linarith)]; exact fun h ↦ (by linarith [h.1])))
    rw [intervalIntegral.integral_sub hfi (hinv.const_mul _),
      intervalIntegral.integral_const_mul, integral_inv_of_pos (by linarith) (by linarith)]
    have hlog : Real.log (δ / 2 / (2 * ε)) = Λ - 2 * Real.log 2 := by
      have hratio : δ / 2 / (2 * ε) = δ / ε / 4 := by field_simp; ring
      have hfour : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [hratio, Real.log_div (div_ne_zero hδ.ne' hε.ne') (by norm_num),
        hfour, Real.log_pow]
      push_cast
      ring
    rw [hlog]
    field_simp
  rw [hmid_eq, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C₁ / Λ ^ 2) ?_).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  · intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have htm : t ∈ Icc (2 * ε) (δ / 2) := ⟨ht.1.le, ht.2⟩
    have hval : radialEnergyDensity ε δ L t - 2 * π / Λ ^ 2 * t⁻¹ =
        (L t - 2 * π * t) / (t ^ 2 * Λ ^ 2) := by
      simp only [radialEnergyDensity, deriv_logCutoffProfile_of_mem_Icc hε htm, ← hΛdef]
      field_simp
    have htΛ : 0 < t ^ 2 * Λ ^ 2 := mul_pos (pow_pos ht0 2) (pow_pos hΛ 2)
    rw [hval, Real.norm_eq_abs, abs_div, abs_of_pos htΛ, div_le_div_iff₀ htΛ (pow_pos hΛ 2)]
    have h := hLC t ⟨ht0.le, by linarith [ht.2]⟩
    calc |L t - 2 * π * t| * Λ ^ 2 ≤ C₁ * t ^ 2 * Λ ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = C₁ * (t ^ 2 * Λ ^ 2) := by ring
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- If the continuous real-valued radial weight is `2πt` up to an error bounded by `C₁ t²`,
the energy of the logarithmic cutoff differs from `2π / log (δ / ε)` by at most
`C / log (δ / ε)²`, with the displayed constant `C` independent of `ε`. -/
theorem abs_integral_deriv_logCutoffProfile_sq_mul_sub_le (hε : 0 < ε) (hεδ : 4 * ε ≤ δ)
    (hL : ContinuousOn L (Icc 0 δ))
    (hLC : ∀ t ∈ Icc 0 δ, |L t - 2 * π * t| ≤ C₁ * t ^ 2) :
    |(∫ t in 0..δ, deriv (logCutoffProfile ε δ) t ^ 2 * L t) - 2 * π / Real.log (δ / ε)| ≤
      (4 * π * Real.log 2 + 2 * logCutoffConst ^ 2 * (2 * π + C₁ * δ) * Real.log 2 +
        C₁ * δ) / Real.log (δ / ε) ^ 2 := by
  have hδ : 0 < δ := by linarith
  set Λ := Real.log (δ / ε)
  have hΛ : 0 < Λ := Real.log_pos ((lt_div_iff₀ hε).2 (by linarith))
  have hC₁ : 0 ≤ C₁ := by
    have h := hLC δ ⟨hδ.le, le_rfl⟩
    have := abs_nonneg (L δ - 2 * π * δ)
    nlinarith [sq_pos_of_pos hδ]
  set K := 2 * π + C₁ * δ
  have hLK (t : ℝ) (ht : t ∈ Icc 0 δ) : |L t| ≤ K * t := by
    have h := hLC t ht
    have habs := abs_add_le (L t - 2 * π * t) (2 * π * t)
    rw [sub_add_cancel, abs_of_nonneg (mul_nonneg (by positivity) ht.1)] at habs
    have : C₁ * t ^ 2 ≤ C₁ * δ * t := by
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hC₁ ht.1) |>.trans_eq (by ring)
    simp only [K]
    nlinarith
  have hlo := abs_integral_radialEnergyDensity_le hε hεδ hL hLK
    (a := ε) (b := 2 * ε) ⟨hε.le, by linarith⟩ ⟨by linarith, by linarith⟩ hε (by linarith)
  have hhi := abs_integral_radialEnergyDensity_le hε hεδ hL hLK
    (a := δ / 2) (b := δ) ⟨by linarith, by linarith⟩ ⟨hδ.le, le_rfl⟩
    (by linarith) (by linarith)
  have hlo_ratio : 2 * ε / ε = 2 := by field_simp
  have hhi_ratio : δ / (δ / 2) = 2 := by field_simp
  rw [hlo_ratio, abs_le] at hlo
  rw [hhi_ratio, abs_le] at hhi
  have hmid := abs_le.1 (abs_integral_radialEnergyDensity_middle_sub_le hε hεδ hL hC₁ hLC)
  have hsplit := integral_radialEnergyDensity_split hε hεδ hL
  dsimp only [radialEnergyDensity] at hsplit hlo hhi hmid
  rw [hsplit]
  have hfinal : 2 * π / Λ =
      2 * π * (Λ - 2 * Real.log 2) / Λ ^ 2 + 4 * π * Real.log 2 / Λ ^ 2 := by
    field_simp
    ring
  rw [hfinal, abs_le]
  have hsplitC : (4 * π * Real.log 2 + 2 * logCutoffConst ^ 2 * K * Real.log 2 + C₁ * δ) / Λ ^ 2 =
      4 * π * Real.log 2 / Λ ^ 2 + 2 * (logCutoffConst ^ 2 * K / Λ ^ 2 * Real.log 2) +
        C₁ / Λ ^ 2 * δ := by field_simp
  rw [hsplitC]
  have hπ : 0 ≤ 4 * π * Real.log 2 / Λ ^ 2 := by positivity
  constructor <;> linarith [hlo.1, hlo.2, hhi.1, hhi.2, hmid.1, hmid.2, hπ]

end TauCeti
