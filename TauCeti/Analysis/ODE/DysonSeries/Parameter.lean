/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The left Dyson series of a family of paths depending on a real parameter

Let `B` be a real Banach algebra and `Ψ_p = TauCeti.dysonSeriesLeft p` the solution of
`Ψ' = p Ψ`, `Ψ(0) = 1`, for a continuous path `p : ℝ → B`. Its inverse is
`Ψ_p(r)⁻¹ = TauCeti.dysonSeries (-p) r` (`TauCeti.dysonSeriesLeft_mul_dysonSeries_neg`).

**Duhamel's formula.** For two continuous paths `p` and `q`,

`Ψ_q(t) - Ψ_p(t) = Ψ_p(t) ∫₀ᵗ Ψ_p(r)⁻¹ (q r - p r) Ψ_q(r) dr`

(`TauCeti.dysonSeriesLeft_sub_dysonSeriesLeft`): the product `Ψ_p(r)⁻¹ Ψ_q(r)` has derivative
`Ψ_p(r)⁻¹ (q r - p r) Ψ_q(r)` and starts at `1`. This is the counterpart, for left Dyson series
in an arbitrary real Banach algebra, of Duhamel's formula for operator-valued propagators of
integrable coefficients (`TauCeti.propagator_sub_propagator_eq_integral`).

**Derivative in a parameter.** Let `p μ r` depend on a real parameter `μ`, jointly continuously,
with a partial derivative `p' μ r = ∂_μ p μ r` that is also jointly continuous. Then
`μ ↦ Ψ_{p μ}(t)` is differentiable, with

`∂_μ Ψ_{p μ}(t) = Ψ_{p μ}(t) ∫₀ᵗ Ψ_{p μ}(r)⁻¹ p' μ r Ψ_{p μ}(r) dr`

(`TauCeti.hasDerivAt_dysonSeriesLeft_parameter`). By Duhamel's formula the difference quotient
at `μ` is `Ψ_{p μ}(t) ∫₀ᵗ Ψ_{p μ}(r)⁻¹ ((p ν r - p μ r) / (ν - μ)) Ψ_{p ν}(r) dr`; the middle
factor tends to `p' μ r` and is bounded by the mean value theorem, and `Ψ_{p ν}(r)` tends to
`Ψ_{p μ}(r)` boundedly, so dominated convergence gives the limit. For bounded operators this is
the variational equation of a linear ODE in its coefficients: it computes, for instance, how the
return map of a linearized Hamiltonian equation moves with the Hamiltonian.

**Against a preserved form.** When the propagator `Ψ_μ` of a family `S μ` of bounded operators
preserves a continuous bilinear map `B`, as the propagator of a linearized Hamiltonian equation
preserves the symplectic form, its inverse is its adjoint for `B`
(`TauCeti.apply_dysonSeries_neg_apply`). At a fixed vector `v` of `Ψ_μ(t)` the derivative above
then becomes `B v (∂_μ Ψ_μ(t) v) = ∫₀ᵗ B (Ψ_μ(r) v) (∂_μ S μ r (Ψ_μ(r) v)) dr`
(`TauCeti.apply_deriv_dysonSeriesLeft_apply_eq_integral`).

The holomorphic analogue for propagators of integrable coefficients is
`TauCeti.hasDerivAt_propagator`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open Filter Set intervalIntegral
open scoped Interval Topology

namespace TauCeti

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- **Duhamel's formula** for left Dyson series: for continuous paths `p` and `q`,
`Ψ_q(t) - Ψ_p(t) = Ψ_p(t) ∫₀ᵗ Ψ_p(r)⁻¹ (q r - p r) Ψ_q(r) dr`, where `Ψ_p = dysonSeriesLeft p`
and `Ψ_p(r)⁻¹ = dysonSeries (-p) r`. -/
theorem dysonSeriesLeft_sub_dysonSeriesLeft {p q : ℝ → B} (hp : Continuous p)
    (hq : Continuous q) (t : ℝ) :
    dysonSeriesLeft q t - dysonSeriesLeft p t =
      dysonSeriesLeft p t *
        ∫ r in 0..t, dysonSeries (-p) r * (q r - p r) * dysonSeriesLeft q r := by
  have hd (r : ℝ) : HasDerivAt (fun r ↦ dysonSeries (-p) r * dysonSeriesLeft q r)
      (dysonSeries (-p) r * (q r - p r) * dysonSeriesLeft q r) r :=
    ((hasDerivAt_dysonSeries hp.neg r).mul (hasDerivAt_dysonSeriesLeft hq r)).congr_deriv (by
      simp only [Pi.neg_apply]
      noncomm_ring)
  have hc : Continuous fun r ↦ dysonSeries (-p) r * (q r - p r) * dysonSeriesLeft q r :=
    ((continuous_dysonSeries hp.neg).mul (hq.sub hp)).mul (continuous_dysonSeriesLeft hq)
  rw [integral_eq_sub_of_hasDerivAt (fun r _ ↦ hd r) (hc.intervalIntegrable _ _),
    dysonSeries_zero, dysonSeriesLeft_zero, mul_one, mul_sub, ← mul_assoc,
    dysonSeriesLeft_mul_dysonSeries_neg hp, one_mul, mul_one]

/-- The difference quotient of `μ ↦ dysonSeriesLeft (p μ) t`, written by Duhamel's formula as an
integral whose middle factor is the difference quotient of the paths. -/
private theorem slope_dysonSeriesLeft_eq {p : ℝ → ℝ → B} (hp : ∀ μ, Continuous (p μ))
    (μ ν t : ℝ) :
    slope (fun μ ↦ dysonSeriesLeft (p μ) t) μ ν =
      dysonSeriesLeft (p μ) t * ∫ r in 0..t,
        dysonSeries (-p μ) r * slope (fun σ ↦ p σ r) μ ν * dysonSeriesLeft (p ν) r := by
  rw [slope_def_module, dysonSeriesLeft_sub_dysonSeriesLeft (hp μ) (hp ν), ← mul_smul_comm,
    ← integral_smul]
  simp only [slope_def_module, mul_smul_comm, smul_mul_assoc]

/-- **The derivative of the left Dyson series in a parameter.** If `p μ r` is jointly continuous
and has a jointly continuous partial derivative `p' μ r` in `μ`, then
`∂_μ Ψ_{p μ}(t) = Ψ_{p μ}(t) ∫₀ᵗ Ψ_{p μ}(r)⁻¹ p' μ r Ψ_{p μ}(r) dr`, where
`Ψ_{p μ} = dysonSeriesLeft (p μ)` and `Ψ_{p μ}(r)⁻¹ = dysonSeries (-p μ) r`. -/
theorem hasDerivAt_dysonSeriesLeft_parameter {p p' : ℝ → ℝ → B}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ μ r, HasDerivAt (fun μ ↦ p μ r) (p' μ r) μ) (μ t : ℝ) :
    HasDerivAt (fun μ ↦ dysonSeriesLeft (p μ) t)
      (dysonSeriesLeft (p μ) t *
        ∫ r in 0..t, dysonSeries (-p μ) r * p' μ r * dysonSeriesLeft (p μ) r) μ := by
  have hpμ (σ : ℝ) : Continuous (p σ) := hp.comp (Continuous.prodMk_right σ)
  have hΨ := continuous_parametric_dysonSeriesLeft hp
  have hW := continuous_dysonSeries (hpμ μ).neg
  -- Bounds on the compact set `[μ - 1, μ + 1] × [[0, t]]`.
  set I := Icc (μ - 1) (μ + 1)
  have hK : IsCompact (I ×ˢ [[0, t]]) := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hp'.continuousOn
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hΨ.continuousOn
  obtain ⟨C₃, hC₃⟩ := (isCompact_uIcc (a := 0) (b := t)).exists_bound_of_continuousOn
    hW.continuousOn
  have hμI : μ ∈ I := ⟨by linarith, by linarith⟩
  -- The difference quotients of the paths are bounded by `C₁` for parameters in `I`.
  have hslope {ν r : ℝ} (hν : ν ∈ I) (hr : r ∈ [[0, t]]) :
      ‖slope (fun σ ↦ p σ r) μ ν‖ ≤ C₁ := by
    rcases eq_or_ne ν μ with h | hne
    · rw [h, slope_same, norm_zero]
      exact (norm_nonneg _).trans (hC₁ (μ, r) ⟨hμI, hr⟩)
    have h := (convex_Icc (μ - 1) (μ + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun σ ↦ p σ r) (fun σ _ ↦ (hd σ r).hasDerivWithinAt)
      (fun σ hσ ↦ hC₁ (σ, r) ⟨hσ, hr⟩) hμI hν
    rw [slope_def_module, norm_smul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hne)), mul_comm]
    exact h
  rw [hasDerivAt_iff_tendsto_slope, funext (slope_dysonSeriesLeft_eq hpμ μ · t)]
  refine (continuous_const.mul continuous_id).continuousAt.tendsto.comp
    (tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C₃ * C₁ * C₂) ?_ ?_
      intervalIntegrable_const ?_)
  · -- Each integrand is continuous in `r`.
    refine Eventually.of_forall fun ν ↦ Continuous.aestronglyMeasurable ?_
    simp only [slope_def_module]
    exact (hW.mul (continuous_const.smul ((hpμ ν).sub (hpμ μ)))).mul
      (hΨ.comp (Continuous.prodMk_right ν))
  · -- For `ν ∈ I` the integrands are bounded by `C₃ * C₁ * C₂` on `[[0, t]]`.
    filter_upwards [nhdsWithin_le_nhds (Icc_mem_nhds (by linarith : μ - 1 < μ)
      (by linarith : μ < μ + 1))] with ν hν
    refine Eventually.of_forall fun r hr ↦ ?_
    have hr' : r ∈ [[0, t]] := uIoc_subset_uIcc hr
    refine (norm_mul_le _ _).trans <| (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
      (norm_nonneg _)).trans ?_
    have hC₃' := hC₃ r hr'
    have hC₁' := hslope hν hr'
    have hC₂' : ‖dysonSeriesLeft (p ν) r‖ ≤ C₂ := hC₂ (ν, r) ⟨hν, hr'⟩
    have hC₃₀ : 0 ≤ C₃ := (norm_nonneg _).trans hC₃'
    have hC₁₀ : 0 ≤ C₁ := (norm_nonneg _).trans hC₁'
    gcongr
  · -- Pointwise, the difference quotient tends to `p' μ r` and `Ψ_{p ν}(r)` to `Ψ_{p μ}(r)`.
    refine Eventually.of_forall fun r _ ↦ ?_
    refine ((tendsto_const_nhds.mul (hd μ r).tendsto_slope).mul ?_)
    exact ((hΨ.comp (continuous_id.prodMk continuous_const)).tendsto μ).mono_left
      nhdsWithin_le_nhds

/-- **The derivative of a propagator against a preserved form.** Let `S μ r` be jointly
continuous with a jointly continuous parameter derivative `S' μ r`, and let `S μ r` be skew for a
continuous bilinear map `B` at the parameter `μ`. If `v` is a fixed vector of the propagator
`Ψ_μ(t) = dysonSeriesLeft (S μ) t`, then
`B v (∂_μ Ψ_μ(t) v) = ∫₀ᵗ B (Ψ_μ(r) v) (S' μ r (Ψ_μ(r) v)) dr`. -/
theorem apply_deriv_dysonSeriesLeft_apply_eq_integral {X W : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {S S' : ℝ → ℝ → X →L[ℝ] X} (hS : Continuous (Function.uncurry S))
    (hS' : Continuous (Function.uncurry S')) (hd : ∀ μ r, HasDerivAt (fun μ ↦ S μ r) (S' μ r) μ)
    (B : X →L[ℝ] X →L[ℝ] W) {μ t : ℝ} (hskew : ∀ r u w, B (S μ r u) w + B u (S μ r w) = 0)
    {v : X} (hv : dysonSeriesLeft (S μ) t v = v) :
    B v (deriv (fun ν ↦ dysonSeriesLeft (S ν) t) μ v) =
      ∫ r in 0..t, B (dysonSeriesLeft (S μ) r v) (S' μ r (dysonSeriesLeft (S μ) r v)) := by
  have hSμ : Continuous (S μ) := hS.comp (Continuous.prodMk_right μ)
  have hc : Continuous fun r ↦ dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r :=
    ((continuous_dysonSeries hSμ.neg).mul (hS'.comp (Continuous.prodMk_right μ))).mul
      (continuous_dysonSeriesLeft hSμ)
  -- Move the outer `Ψ_μ(t)` and the inverses `Ψ_μ(r)⁻¹` into the first slot of `B`.
  have hrhs : (∫ r in 0..t, B (dysonSeriesLeft (S μ) r v) (S' μ r (dysonSeriesLeft (S μ) r v))) =
      ∫ r in 0..t, B v ((dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r) v) :=
    integral_congr fun r _ ↦ by
      simp only [mul_apply_eq_comp, apply_dysonSeries_neg_apply hSμ B hskew]
  calc B v (deriv (fun ν ↦ dysonSeriesLeft (S ν) t) μ v)
      = B (dysonSeriesLeft (S μ) t v) (dysonSeriesLeft (S μ) t
          ((∫ r in 0..t, dysonSeries (-S μ) r * S' μ r * dysonSeriesLeft (S μ) r) v)) := by
        rw [hv, (hasDerivAt_dysonSeriesLeft_parameter hS hS' hd μ t).deriv, mul_apply_eq_comp]
    _ = _ := by
      rw [apply_dysonSeriesLeft_apply_dysonSeriesLeft hSμ B hskew, hrhs,
        ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 t),
        (B v).intervalIntegral_comp_comm ((hc.clm_apply continuous_const).intervalIntegrable 0 t)]

end TauCeti
