/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation
public import TauCeti.Analysis.Normed.Module.ModulusOfContinuity

/-!
# Heat regularization at the scale of a modulus of continuity

Let `g` be a bounded function on a finite-dimensional real inner product space `E` which moves by
at most `η` over distances at most `√t`, for some `t > 0`. This file shows that the heat
regularization `K_t ⋆ g` at the matching time is close to `g`, and that its derivatives are as
small as those of a function oscillating by `η` on the scale `√t`:

* `‖(K_t ⋆ g)(x) - g(x)‖ ≤ (1 + M₁) η`, where `M₁ = ∫ ‖y‖ K_1(y) dy` is
  `TauCeti.heatKernelMoment E 1`;
* `‖D^m (K_t ⋆ g)(x)‖ ≤ C η t^(-m/2)` for every `m ≥ 1`, with `C` depending only on `m` and `E`.

Neither bound involves the supremum of `g`, and the time `t` and the oscillation `η` enter only
through the scale-invariant combination above. For a uniformly continuous `g` with modulus `ω`,
taking `η = ω(√t)` gives regularizations `g_t` with `‖g_t - g‖ = O(ω(√t))`,
`‖D g_t‖ = O(ω(√t) t^(-1/2))` and `‖D² g_t‖ = O(ω(√t) t⁻¹)`. These are the approximants in the
comparison argument for the rate at which a parabolic equation attains uniformly continuous
initial data: the error `t ‖D² g_t‖` they create up to time `t` is again `O(ω(√t))`.

The proofs integrate the linear growth `‖g(x - z) - g(x)‖ ≤ (1 + ‖z‖ / √t) η`
(`TauCeti.dist_le_one_add_dist_div_mul`) against the heat kernel and its derivatives, using the
cancellation `∫ D^m K_t = 0` for `m ≥ 1`
(`TauCeti.iteratedFDeriv_heatKernel_convolution_eq_integral_sub`) and the weighted kernel bounds
`∫ ‖D^m K_t(z)‖ ‖z‖^α dz ≤ C t^((α - m)/2)`
(`TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le`) at `α = 0` and `α = 1`.

## Main declarations

* `TauCeti.norm_heatCauchyPotential_sub_le_of_dist_le`: the regularization is within `(1 + M₁) η`
  of the datum.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_convolution_le_of_dist_le`: the bound
  `C η t^(-m/2)` on its derivatives of order `m ≥ 1`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Section 8.1
  (smoothing of the initial datum in the Cauchy problem).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped Convolution NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : E → F} {t η : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] in
/-- A function moving by at most `η` over distances at most `√t` moves by at most
`(1 + ‖z‖ / √t) η` between `x - z` and `x`. -/
private theorem norm_sub_le_one_add_norm_div_sqrt_mul (ht : 0 < t)
    (hη : ∀ x y, dist x y ≤ √t → dist (g x) (g y) ≤ η) (x z : E) :
    ‖g (x - z) - g x‖ ≤ (1 + ‖z‖ / √t) * η := by
  simpa [dist_eq_norm] using dist_le_one_add_dist_div_mul (sqrt_pos.2 ht) hη (x - z) x

/-- **The regularization is close to the datum.** If a bounded continuous `g` moves by at most
`η` over distances at most `√t`, `t > 0`, then its heat regularization at time `t` satisfies
`‖u(t, x) - g(x)‖ ≤ (1 + M₁) η`, where `M₁ = ∫ ‖y‖ K_1(y) dy` is
`TauCeti.heatKernelMoment E 1`. -/
theorem norm_heatCauchyPotential_sub_le_of_dist_le [CompleteSpace F] {M : ℝ}
    (hgc : Continuous g) (hM : ∀ y, ‖g y‖ ≤ M) (ht : 0 < t)
    (hη : ∀ x y, dist x y ≤ √t → dist (g x) (g y) ≤ η) (x : E) :
    ‖heatCauchyPotential g t x - g x‖ ≤ (1 + heatKernelMoment E 1) * η := by
  have hK := integrable_heatKernel (E := E) one_pos
  have hw := integrable_norm_rpow_mul_heatKernel (E := E) one_pos zero_le_one
  simp only [rpow_one] at hw
  have hst := sqrt_pos.2 ht
  -- The datum is its own average against the probability density `K_1`.
  have hgx : g x = ∫ y : E, heatKernel 1 y • g x := by
    rw [integral_smul_const, integral_heatKernel one_pos, one_smul]
  rw [heatCauchyPotential_def, hgx, ← integral_sub
    (integrable_heatKernel_one_smul_sub_smul_of_norm_le hgc hM x _) (hK.smul_const _)]
  calc ‖∫ y, (heatKernel 1 y • g (x - √t • y) - heatKernel 1 y • g x)‖
      ≤ ∫ y : E, (η * heatKernel 1 y + η * (‖y‖ * heatKernel 1 y)) := by
        refine norm_integral_le_of_norm_le ((hK.const_mul η).add (hw.const_mul η))
          (ae_of_all _ fun y => ?_)
        rw [← smul_sub, norm_smul, norm_of_nonneg (heatKernel_pos one_pos y).le]
        have h := norm_sub_le_one_add_norm_div_sqrt_mul ht hη x (√t • y)
        rw [norm_smul, norm_of_nonneg hst.le, mul_div_cancel_left₀ _ hst.ne'] at h
        nlinarith [heatKernel_pos (E := E) one_pos y]
    _ = (1 + heatKernelMoment E 1) * η := by
        rw [integral_add (hK.const_mul η) (hw.const_mul η), integral_const_mul,
          integral_const_mul, integral_heatKernel one_pos, coe_heatKernelMoment]
        simp only [NNReal.coe_one, rpow_one]
        ring

/-- **Derivatives of the regularization.** For every order `m ≥ 1` there is a constant `C`,
depending only on `m` and `E`, such that if a bounded measurable `g` moves by at most `η` over
distances at most `√t`, `t > 0`, then `‖D^m (K_t ⋆ g)(x)‖ ≤ C η t^(-m/2)`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_convolution_le_of_dist_le {m : ℕ} (hm : m ≠ 0) :
    ∃ C ≥ 0, ∀ {g : E → F} {M t η : ℝ}, AEStronglyMeasurable g → (∀ᵐ y, ‖g y‖ ≤ M) → 0 < t →
      (∀ x y, dist x y ≤ √t → dist (g x) (g y) ≤ η) → ∀ x,
        ‖iteratedFDeriv ℝ m (heatKernel t ⋆ g) x‖ ≤ C * η * t ^ (-(m : ℝ) / 2) := by
  obtain ⟨C₀, hC₀, hC₀t⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m le_rfl
  obtain ⟨C₁, hC₁, hC₁t⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m zero_le_one
  refine ⟨C₀ + C₁, by positivity, fun {g M t η} hg hM ht hη x => ?_⟩
  have hη0 : 0 ≤ η := dist_nonneg.trans (hη x x (by simp))
  have hi₀ := integrable_norm_iteratedFDeriv_heatKernel_mul_rpow (E := E) ht m le_rfl
  have hi₁ := integrable_norm_iteratedFDeriv_heatKernel_mul_rpow (E := E) ht m zero_le_one
  simp only [rpow_zero, mul_one, rpow_one] at hi₀ hi₁ hC₀t hC₁t
  -- The two weighted kernel integrals combine into the single power `t^(-m/2)`.
  have hpow : (√t)⁻¹ * t ^ ((1 - m) / 2 : ℝ) = t ^ (-(m : ℝ) / 2) := by
    rw [sqrt_eq_rpow, ← rpow_neg ht.le, ← rpow_add ht]
    ring_nf
  rw [iteratedFDeriv_heatKernel_convolution_eq_integral_sub ht hg hM hm]
  calc ‖∫ z, (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z) - g x)‖
      ≤ ∫ z, (η * ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖ +
          η * (√t)⁻¹ * (‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖ * ‖z‖)) := by
        refine norm_integral_le_of_norm_le ((hi₀.const_mul η).add (hi₁.const_mul _))
          (ae_of_all _ fun z => ?_)
        rw [ContinuousMultilinearMap.norm_smulRight]
        have h := norm_sub_le_one_add_norm_div_sqrt_mul ht hη x z
        have hD := norm_nonneg (iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z)
        calc _ ≤ ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖ * ((1 + ‖z‖ / √t) * η) :=
              mul_le_mul_of_nonneg_left h hD
          _ = _ := by rw [div_eq_mul_inv]; ring
    _ = η * (∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖) +
          η * (√t)⁻¹ * ∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖ * ‖z‖ := by
        rw [integral_add (hi₀.const_mul η) (hi₁.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ η * (C₀ * t ^ ((0 - m) / 2 : ℝ)) + η * (√t)⁻¹ * (C₁ * t ^ ((1 - m) / 2 : ℝ)) := by
        gcongr
        · exact hC₀t t ht
        · exact hC₁t t ht
    _ = (C₀ + C₁) * η * t ^ (-(m : ℝ) / 2) := by
        rw [show ((0 : ℝ) - m) / 2 = -(m : ℝ) / 2 by ring, ← hpow]
        ring

end TauCeti
