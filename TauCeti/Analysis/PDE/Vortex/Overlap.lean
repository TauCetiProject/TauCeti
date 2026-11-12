/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Overlap
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Overlap of separated plane vortices

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. Let `x` and `y` be vortices on the whole plane with
`|α| → 1` at infinity, for instance the vortices of two clusters of zeros `D₁` and `D₂`. Moving the
second cluster to `D₂ - a` replaces `y` by its translate `y (· + a)`. Away from their zeros both
vortices are exponentially close to the vacuum, so the regions where they differ from the vacuum
interact only through exponentially small tails. This file makes that quantitative: the overlap of
their modulus defects `1 - |α|²`, and of their energy densities
`|F_a|² + |d_a α|² + (1 - |α|²)²`, decays exponentially in the separation `‖a‖`, pointwise and
after integration over the plane.

* The modulus defects satisfy
  `(1 - |α_x(z)|²) (1 - |α_y(z + a)|²) ≤ K exp (-(c ‖a‖))` for every rate `c < 1 / 2`
  (`TauCeti.Vortex.exists_one_sub_normSq_mul_one_sub_normSq_le_mul_exp`), and the same bound holds
  for the overlap integral `∫ (1 - |α_x(z)|²) (1 - |α_y(z + a)|²)`
  (`TauCeti.Vortex.exists_integral_one_sub_normSq_mul_one_sub_normSq_le_mul_exp`).
  On a vortex the curvature coefficient is `-(1 - |α|²) / 8`, so the curvatures overlap in the
  same way.
* The energy densities satisfy the same two bounds for every rate `c < 1`
  (`TauCeti.Vortex.exists_energyDensity_mul_energyDensity_le_mul_exp`,
  `TauCeti.Vortex.exists_integral_energyDensity_mul_energyDensity_le_mul_exp`).
* Both overlaps are integrable for every separation `a`
  (`TauCeti.Vortex.integrable_one_sub_normSq_mul_one_sub_normSq`,
  `TauCeti.Vortex.integrable_energyDensity_mul_energyDensity`).

The rates are those of the decay of a single vortex
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_energyDensity_le_mul_exp`), and the constants depend on the two vortices.
They come from the overlap estimates for nonnegative functions decaying at every rate below a
threshold (`TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt`,
`TauCeti.exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Topology

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
  (hpx : ContDiff ℝ 2 (fun w ↦ x w 2)) (hqx : ContDiff ℝ 2 (fun w ↦ x w 3))
  (hsolx : ∀ z, equation x z = 0)
  (hlimx : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hpy : ContDiff ℝ 2 (fun w ↦ y w 2)) (hqy : ContDiff ℝ 2 (fun w ↦ y w 3))
  (hsoly : ∀ z, equation y z = 0)
  (hlimy : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))

include hpx hqx hsolx hlimx hpy hqy hsoly hlimy

/-- **Pointwise overlap of the modulus defects of separated vortices.** For vortices `x` and `y`
on the whole plane with `|α| → 1` at infinity, the modulus defects of `x` and of the translate
`y (· + a)` satisfy `(1 - |α_x(z)|²) (1 - |α_y(z + a)|²) ≤ K exp (-(c ‖a‖))` for every rate
`c < 1 / 2`, with `K` independent of `z` and `a`. -/
theorem exists_one_sub_normSq_mul_one_sub_normSq_le_mul_exp {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ z a, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) *
      (1 - 4 * (y (z + a) 2 ^ 2 + y (z + a) 3 ^ 2)) ≤ K * Real.exp (-(c * ‖a‖)) :=
  TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt
    (fun z ↦ sub_nonneg.2 (normSq_le_one_of_tendsto hpx hqx hsolx hlimx z))
    (fun z ↦ sub_nonneg.2 (normSq_le_one_of_tendsto hpy hqy hsoly hlimy z))
    (fun _ hc ↦ exists_one_sub_normSq_le_mul_exp hpx hqx hsolx hlimx hc)
    (fun _ hc ↦ exists_one_sub_normSq_le_mul_exp hpy hqy hsoly hlimy hc) (by norm_num) hc

/-- **Overlap integral of the modulus defects of separated vortices.** For vortices `x` and `y`
on the whole plane with `|α| → 1` at infinity, the overlap
`∫ (1 - |α_x(z)|²) (1 - |α_y(z + a)|²)` of the modulus defects of `x` and of the translate
`y (· + a)` is at most `K exp (-(c ‖a‖))` for every rate `c < 1 / 2`, for every additive Haar
measure on the plane, with `K` independent of `a`. -/
theorem exists_integral_one_sub_normSq_mul_one_sub_normSq_le_mul_exp (μ : Measure ℂ)
    [μ.IsAddHaarMeasure] {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ a, ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) *
      (1 - 4 * (y (z + a) 2 ^ 2 + y (z + a) 3 ^ 2)) ∂μ ≤ K * Real.exp (-(c * ‖a‖)) :=
  TauCeti.exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt μ
    (fun z ↦ sub_nonneg.2 (normSq_le_one_of_tendsto hpx hqx hsolx hlimx z))
    (fun z ↦ sub_nonneg.2 (normSq_le_one_of_tendsto hpy hqy hsoly hlimy z))
    (fun _ hc ↦ exists_one_sub_normSq_le_mul_exp hpx hqx hsolx hlimx hc)
    (fun _ hc ↦ exists_one_sub_normSq_le_mul_exp hpy hqy hsoly hlimy hc) (by norm_num) hc

/-- **Integrability of the overlap of the modulus defects of separated vortices.** For vortices
`x` and `y` on the whole plane with `|α| → 1` at infinity, the overlap
`(1 - |α_x(z)|²) (1 - |α_y(z + a)|²)` of the modulus defects of `x` and of the translate
`y (· + a)` is integrable for every additive Haar measure on the plane. -/
theorem integrable_one_sub_normSq_mul_one_sub_normSq (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (a : ℂ) :
    Integrable (fun z ↦ (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) *
      (1 - 4 * (y (z + a) 2 ^ 2 + y (z + a) 3 ^ 2))) μ := by
  have hx₀ (z : ℂ) := sub_nonneg.2 (normSq_le_one_of_tendsto hpx hqx hsolx hlimx z)
  have hy₀ (z : ℂ) := sub_nonneg.2 (normSq_le_one_of_tendsto hpy hqy hsoly hlimy z)
  obtain ⟨Kx, hKx⟩ := exists_one_sub_normSq_le_mul_exp hpx hqx hsolx hlimx
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  obtain ⟨Ky, hKy⟩ := exists_one_sub_normSq_le_mul_exp hpy hqy hsoly hlimy
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  refine (TauCeti.integrable_norm_mul_norm_comp_add μ (by norm_num : (0 : ℝ) < 1 / 4)
    (integrable_one_sub_normSq μ hpx hqx hsolx hlimx).aestronglyMeasurable
    (integrable_one_sub_normSq μ hpy hqy hsoly hlimy).aestronglyMeasurable
    (fun z ↦ (Real.norm_of_nonneg (hx₀ z)).trans_le (hKx z))
    (fun z ↦ (Real.norm_of_nonneg (hy₀ z)).trans_le (hKy z)) a).congr (.of_forall fun z ↦ ?_)
  simp only [Real.norm_of_nonneg (hx₀ z), Real.norm_of_nonneg (hy₀ (z + a))]

variable (hbx : Continuous (fun w ↦ x w 0)) (hby : Continuous (fun w ↦ y w 0))

include hbx hby

/-- **Pointwise overlap of the energy densities of separated vortices.** For vortices `x` and `y`
on the whole plane with `|α| → 1` at infinity, the energy densities of `x` and of the translate
`y (· + a)` satisfy `e_x(z) e_y(z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < 1`, with `K`
independent of `z` and `a`. -/
theorem exists_energyDensity_mul_energyDensity_le_mul_exp {c : ℝ} (hc : c < 1) :
    ∃ K, ∀ z a, energyDensity x z * energyDensity y (z + a) ≤ K * Real.exp (-(c * ‖a‖)) :=
  TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt
    (fun z ↦ by rw [energyDensity_apply]; positivity)
    (fun z ↦ by rw [energyDensity_apply]; positivity)
    (fun _ hc ↦ exists_energyDensity_le_mul_exp hbx hpx hqx hsolx hlimx hc)
    (fun _ hc ↦ exists_energyDensity_le_mul_exp hby hpy hqy hsoly hlimy hc) one_pos hc

/-- **Overlap integral of the energy densities of separated vortices.** For vortices `x` and `y`
on the whole plane with `|α| → 1` at infinity, the overlap `∫ e_x(z) e_y(z + a)` of the energy
densities of `x` and of the translate `y (· + a)` is at most `K exp (-(c ‖a‖))` for every rate
`c < 1`, for every additive Haar measure on the plane, with `K` independent of `a`. -/
theorem exists_integral_energyDensity_mul_energyDensity_le_mul_exp (μ : Measure ℂ)
    [μ.IsAddHaarMeasure] {c : ℝ} (hc : c < 1) :
    ∃ K, ∀ a, ∫ z, energyDensity x z * energyDensity y (z + a) ∂μ ≤
      K * Real.exp (-(c * ‖a‖)) :=
  TauCeti.exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt μ
    (fun z ↦ by rw [energyDensity_apply]; positivity)
    (fun z ↦ by rw [energyDensity_apply]; positivity)
    (fun _ hc ↦ exists_energyDensity_le_mul_exp hbx hpx hqx hsolx hlimx hc)
    (fun _ hc ↦ exists_energyDensity_le_mul_exp hby hpy hqy hsoly hlimy hc) one_pos hc

/-- **Integrability of the overlap of the energy densities of separated vortices.** For vortices
`x` and `y` on the whole plane with `|α| → 1` at infinity, the overlap `e_x(z) e_y(z + a)` of the
energy densities of `x` and of the translate `y (· + a)` is integrable for every additive Haar
measure on the plane. -/
theorem integrable_energyDensity_mul_energyDensity (μ : Measure ℂ) [μ.IsAddHaarMeasure] (a : ℂ) :
    Integrable (fun z ↦ energyDensity x z * energyDensity y (z + a)) μ := by
  have hx₀ (z : ℂ) : 0 ≤ energyDensity x z := by rw [energyDensity_apply]; positivity
  have hy₀ (z : ℂ) : 0 ≤ energyDensity y z := by rw [energyDensity_apply]; positivity
  obtain ⟨Kx, hKx⟩ := exists_energyDensity_le_mul_exp hbx hpx hqx hsolx hlimx
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨Ky, hKy⟩ := exists_energyDensity_le_mul_exp hby hpy hqy hsoly hlimy
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine (TauCeti.integrable_norm_mul_norm_comp_add μ (by norm_num : (0 : ℝ) < 1 / 2)
    (aestronglyMeasurable_energyDensity hbx hpx hqx hsolx μ)
    (aestronglyMeasurable_energyDensity hby hpy hqy hsoly μ)
    (fun z ↦ (Real.norm_of_nonneg (hx₀ z)).trans_le (hKx z))
    (fun z ↦ (Real.norm_of_nonneg (hy₀ z)).trans_le (hKy z)) a).congr (.of_forall fun z ↦ ?_)
  simp only [Real.norm_of_nonneg (hx₀ z), Real.norm_of_nonneg (hy₀ (z + a))]

end TauCeti.Vortex
