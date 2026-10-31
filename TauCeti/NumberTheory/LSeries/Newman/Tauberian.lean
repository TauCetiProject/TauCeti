/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Newman.Detour
public import TauCeti.NumberTheory.LSeries.Newman.Semicircle

/-!
# Newman's Tauberian theorem for bounded Laplace transforms

Let `f : ℝ → ℂ` be measurable and bounded by `M` on `[0, ∞)`, and let `G` be holomorphic on an
open set `Ω` containing the closed half-plane `0 ≤ re z`, agreeing with the Laplace transform
`∫ t in Ici 0, f t * exp (-z t)` on `0 < re z`. Newman's Tauberian theorem
(`newmanLaplace_tendsto_integral`) states that the improper integral `∫ t in 0..T, f t`
converges to `G 0` as `T → ∞`.

The proof assembles the contour estimates of the neighbouring files. Fix `R > 0` and choose a
detour `newmanDetour R δ` through the left half-plane inside `Ω`. With
`G_T z = ∫ t in 0..T, f t * exp (-z t)` and Newman's kernel `k_T z = exp (T z) (1 + z² / R²) / z`:

* Cauchy's formula for `(G - G_T) k_T` on the right semicircle closed by the detour, together
  with the deformation of the left semicircle into the detour for the entire function `G_T`,
  gives `integral_right_semicircle_add_integral_newmanDetour_mul_kernel`:
  the right semicircle integral of `(G - G_T) k_T` plus the detour integral of `G k_T` equals
  `2πi (G 0 - ∫ t in 0..T, f t)` plus the left semicircle integral of `G_T k_T`;
* the two semicircle contributions are at most `M / R` after division by `2πi`, and the
  detour integral of `G k_T` tends to `0` as `T → ∞`, so eventually
  `‖G 0 - ∫ t in 0..T, f t‖ ≤ 2 M / R + ε` (`eventually_norm_sub_intervalIntegral_le`);
* letting `R → ∞` gives the theorem.

No radius-independent continuation width is used: the detour depends on `R`.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set Metric Complex
open scoped Topology Real Interval

namespace TauCeti.LSeries

variable {f : ℝ → ℂ} {G : ℂ → ℂ} {M T R δ : ℝ}

/-- **Newman's contour identity.** Let `G` be holomorphic on an open convex set `U` containing
the right semicircle of radius `R > 0` and the detour `newmanDetour R δ` with `δ > 0`, and let
`G_T z = ∫ t in 0..T, f t * exp (-z t)`. Against Newman's kernel
`k_T z = exp (T z) (1 + z² / R²) / z`, the right semicircle integral of `(G - G_T) k_T`
(counterclockwise from `-R * I` to `R * I`) plus the detour integral of `G k_T` (from `R * I`
back to `-R * I`) equals `2πi (G 0 - ∫ t in 0..T, f t)` plus the left semicircle integral of
`G_T k_T` (counterclockwise from `R * I` to `-R * I`). All integrals include the velocity of
their parametrization. -/
theorem integral_right_semicircle_add_integral_newmanDetour_mul_kernel {U : Set ℂ}
    (hf : IntervalIntegrable f volume 0 T) (hR : 0 < R) (hδ : 0 < δ) (hU : IsOpen U)
    (hconv : Convex ℝ U) (hG : DifferentiableOn ℂ G U)
    (hcirc : ∀ θ ∈ Icc (-π / 2) (π / 2), circleMap 0 R θ ∈ U)
    (hdet : ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U) :
    (∫ θ in (-π / 2)..(π / 2), circleMap 0 R θ * I *
        ((G (circleMap 0 R θ) - ∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
          cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
            circleMap 0 R θ)) +
      ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
        (G (newmanDetour R δ s) * cexp (T * newmanDetour R δ s) *
          (1 + newmanDetour R δ s ^ 2 / (R : ℂ) ^ 2) / newmanDetour R δ s) =
      2 * π * I * (G 0 - ∫ t in (0 : ℝ)..T, f t) +
        ∫ θ in (π / 2)..(3 * π / 2), circleMap 0 R θ * I *
          ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
            cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
              circleMap 0 R θ) := by
  have hGT : Differentiable ℂ fun z : ℂ ↦ ∫ t in (0 : ℝ)..T, f t * cexp (-z * t) :=
    differentiable_intervalIntegral_mul_cexp_neg_mul hf
  -- Cauchy's formula for `(G - G_T) k_T` on the right semicircle closed by the detour.
  have hC := integral_right_semicircle_add_integral_newmanDetour
    (g := fun z ↦ (G z - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) *
      (1 + z ^ 2 / (R : ℂ) ^ 2))
    hR hδ hU hconv (((hG.sub hGT.differentiableOn).mul (by fun_prop)).mul (by fun_prop))
    hcirc hdet
  -- The detour replaces the left semicircle for the entire function `G_T k_T`.
  have hL := integral_left_semicircle_eq_integral_newmanDetour
    (g := fun z ↦ (∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) *
      (1 + z ^ 2 / (R : ℂ) ^ 2))
    hR hδ isOpen_univ convex_univ ((hGT.mul (by fun_prop)).mul (by fun_prop)).differentiableOn
    (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _)
  -- Split the detour integral of `(G - G_T) k_T`; both parts are continuous on `[-1, 1]`.
  have hI : [[(-1 : ℝ), 1]] = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hint₁ := intervalIntegrable_newmanDetour_mul_kernel (T := T) hR hδ
    (hG.continuousOn.comp (continuous_newmanDetour R δ).continuousOn fun s hs ↦ hdet s (hI ▸ hs))
  have hint₂ := intervalIntegrable_newmanDetour_mul_kernel (T := T)
    (w := fun z ↦ ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) hR hδ
    (hGT.continuous.comp_continuousOn (continuous_newmanDetour R δ).continuousOn)
  have h0 : (G 0 - ∫ t in (0 : ℝ)..T, f t * cexp (-0 * t)) * cexp (T * 0) *
      (1 + 0 ^ 2 / (R : ℂ) ^ 2) = G 0 - ∫ t in (0 : ℝ)..T, f t := by
    simp
  beta_reduce at hC hL
  rw [h0] at hC
  rw [show (∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
      ((G (newmanDetour R δ s) - ∫ t in (0 : ℝ)..T, f t * cexp (-newmanDetour R δ s * t)) *
        cexp (T * newmanDetour R δ s) * (1 + newmanDetour R δ s ^ 2 / (R : ℂ) ^ 2) /
          newmanDetour R δ s)) = _ from (intervalIntegral.integral_congr fun s _ ↦ by ring).trans
    (intervalIntegral.integral_sub hint₁ hint₂), ← hL] at hC
  linear_combination hC

/-- **Newman's estimate at a fixed radius.** Let `f` be measurable and bounded by `M` on
`[0, ∞)`, and let `G` be holomorphic on an open set `Ω` containing the closed half-plane
`0 ≤ re z` and equal to the Laplace transform of `f` on `0 < re z`. For every `R > 0` and
`ε > 0`, eventually in `T`, `‖G 0 - ∫ t in 0..T, f t‖ ≤ 2 M / R + ε`. -/
theorem eventually_norm_sub_intervalIntegral_le {Ω : Set ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) (hΩ : IsOpen Ω) (hcover : {z : ℂ | 0 ≤ z.re} ⊆ Ω)
    (hG : DifferentiableOn ℂ G Ω)
    (hLaplace : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), f t * cexp (-z * t))
    (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ‖G 0 - ∫ t in (0 : ℝ)..T, f t‖ ≤ 2 * M / R + ε := by
  obtain ⟨δ, hδ, U, hUΩ, hU, hconv, hcirc, hdet⟩ :=
    exists_convex_newmanDetour_subset hΩ hcover hR.le
  have hD := (tendsto_integral_newmanDetour_mul_kernel hR hδ (hG.continuousOn.mono
    (by rintro _ ⟨s, hs, rfl⟩; exact hUΩ (hdet s hs)))).div_const (2 * π * I)
  rw [zero_div] at hD
  filter_upwards [eventually_ge_atTop 0, (hD.norm.eventually (ge_mem_nhds (by simpa using hε)))]
    with T hT hDT
  have hfT : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr <|
      IntegrableOn.of_bound measure_Ioc_lt_top
        (hf.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self)) M
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hbound t (le_of_lt ht.1))
  have hid := integral_right_semicircle_add_integral_newmanDetour_mul_kernel hfT hR hδ hU hconv
    (hG.mono hUΩ) hcirc hdet
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hR' := norm_integral_right_semicircle_mul_kernel_le hf hbound hLaplace hR hT
  have hL' := norm_integral_left_semicircle_mul_kernel_le (f := f) (fun t ht ↦ hbound t ht.1) hR hT
  set A := ∫ θ in (-π / 2)..(π / 2), circleMap 0 R θ * I *
    ((G (circleMap 0 R θ) - ∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
      cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ)
  set B := ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
    (G (newmanDetour R δ s) * cexp (T * newmanDetour R δ s) *
      (1 + newmanDetour R δ s ^ 2 / (R : ℂ) ^ 2) / newmanDetour R δ s)
  set C := ∫ θ in (π / 2)..(3 * π / 2), circleMap 0 R θ * I *
    ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
      cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ)
  have he : G 0 - ∫ t in (0 : ℝ)..T, f t =
      A / (2 * π * I) + B / (2 * π * I) - C / (2 * π * I) := by
    rw [← add_div, ← sub_div, eq_div_iff h2πI]
    linear_combination -hid
  rw [he]
  calc _ ≤ ‖A / (2 * π * I)‖ + ‖B / (2 * π * I)‖ + ‖C / (2 * π * I)‖ := norm_sub_le_of_le
        (norm_add_le _ _) le_rfl
    _ ≤ M / R + ε + M / R := by gcongr
    _ = 2 * M / R + ε := by ring

/-- **Newman's Tauberian theorem.** Let `f : ℝ → ℂ` be measurable and bounded on `[0, ∞)`, and
let `G` be holomorphic on an open set `Ω` containing the closed half-plane `0 ≤ re z`, agreeing
with the Laplace transform `∫ t in Ici 0, f t * exp (-z t)` on the open half-plane `0 < re z`.
Then `∫ t in 0..T, f t` converges to `G 0` as `T → ∞`. -/
theorem newmanLaplace_tendsto_integral {Ω : Set ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) (hΩ : IsOpen Ω) (hcover : {z : ℂ | 0 ≤ z.re} ⊆ Ω)
    (hG : DifferentiableOn ℂ G Ω)
    (hLaplace : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) :
    Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (G 0)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (mem_Ici.mpr le_rfl))
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose `R` with `2 M / R ≤ ε / 2`, then apply the fixed-radius estimate with `ε / 4`.
  have hR : 0 < 4 * (M + 1) / ε := by positivity
  filter_upwards [eventually_norm_sub_intervalIntegral_le hf hbound hΩ hcover hG hLaplace hR
    (by positivity : 0 < ε / 4)] with T hT
  rw [dist_eq_norm']
  refine hT.trans_lt ?_
  have : 2 * M / (4 * (M + 1) / ε) ≤ ε / 2 := by
    rw [div_le_iff₀ hR]
    field_simp
    nlinarith
  linarith

end TauCeti.LSeries
