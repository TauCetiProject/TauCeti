/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Smooth solutions of the stationary Schrödinger equation in the plane

Let `P` be a smooth, bounded, nonnegative potential on the plane `ℂ`, bounded below by a constant
`a > 0` outside a disc. For every smooth square-integrable `g`, the stationary Schrödinger equation

`-Δh + P h = g`

has a smooth solution `h ∈ H²(ℂ)` that solves it at every point
(`TauCeti.exists_contDiff_mem_realSobolevFunctions_neg_laplacian_add_mul_eq`).

The weak solution `h ∈ H²(ℂ)` comes from
`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`. Since
`2 > dim ℂ / 2`, it has a continuous representative
(`TauCeti.exists_continuous_ae_eq_of_mem_realSobolevFunctions`), which solves `Δh = P h - g` in the
sense of distributions. The right side is a smooth function of the position and of the value of
`h`, so the planar semilinear bootstrap
`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp` makes `h` smooth, and
`TauCeti.eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp` makes the equation hold
pointwise.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8 (weak solutions and their regularity).
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace TemperedDistribution
open scoped Laplacian ContDiff Distributions

/-- **Smooth solutions of the planar stationary Schrödinger equation.** Let `P` be a smooth,
essentially bounded, nonnegative potential on `ℂ` with `P ≥ a > 0` outside a disc, and let `g` be
smooth and square integrable. Then there is a smooth `h ∈ H²(ℂ)` with `-Δh + P h = g` at every
point. -/
theorem exists_contDiff_mem_realSobolevFunctions_neg_laplacian_add_mul_eq {P g : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hPb : MemLp P ⊤ volume) (hP₀ : ∀ z, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ z, R < ‖z‖ → a ≤ P z) (hg : ContDiff ℝ ∞ g) (hg₂ : MemLp g 2 volume) :
    ∃ h : ℂ → ℝ, ContDiff ℝ ∞ h ∧ h ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, -Δ h z + P z * h z = g z := by
  obtain ⟨h₀, hh₀, hw₀⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hPb (ae_of_all _ hP₀) ha (ae_of_all _ hPa) hg₂
  -- A continuous representative of the weak solution.
  obtain ⟨h, hc, hae⟩ := exists_continuous_ae_eq_of_mem_realSobolevFunctions
    (finrank_real_complex_lt_two_mul one_lt_two) hh₀
  have hh : h ∈ realSobolevFunctions ℂ 2 2 := mem_realSobolevFunctions_of_ae_eq hh₀ hae
  -- It solves `Δh = P h - g` in the sense of distributions.
  set F : ℂ × ℝ → ℝ := fun p ↦ P p.1 * p.2 - g p.1 with hF
  have hFs : ContDiff ℝ ∞ F := (hP.comp contDiff_fst).mul contDiff_snd |>.sub (hg.comp contDiff_fst)
  have hdist (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
      ∫ z, Δ (φ : ℂ → ℝ) z * h z = ∫ z, φ z * F (z, h z) := by
    have hφ : ContDiff ℝ ∞ (φ : ℂ → ℝ) := φ.contDiff
    have hφc : HasCompactSupport (φ : ℂ → ℝ) := φ.hasCompactSupport
    have hΔc : Continuous (Δ (φ : ℂ → ℝ)) := (hφ.of_le (by simp)).continuous_laplacian
    have hΔs : HasCompactSupport (Δ (φ : ℂ → ℝ)) := hφc.laplacian
    have hw := hw₀ φ (hφ.of_le (by simp)) hφc
    rw [integral_congr_ae (hae.mono fun z hz ↦ by rw [hz])] at hw
    have i₁ : Integrable (fun z ↦ Δ (φ : ℂ → ℝ) z * h z) :=
      (hΔc.mul hc).integrable_of_hasCompactSupport hΔs.mul_right
    have i₂ : Integrable (fun z ↦ φ z * (P z * h z)) :=
      (hφ.continuous.mul (hP.continuous.mul hc)).integrable_of_hasCompactSupport hφc.mul_right
    have i₃ : Integrable (fun z ↦ φ z * g z) :=
      (hφ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hφc.mul_right
    have e₁ : ∫ z, h z * (-Δ (φ : ℂ → ℝ) z + P z * φ z) =
        (∫ z, φ z * (P z * h z)) - ∫ z, Δ (φ : ℂ → ℝ) z * h z :=
      (integral_congr_ae (ae_of_all _ fun z ↦ by ring)).trans (integral_sub i₂ i₁)
    have e₂ : ∫ z, φ z * F (z, h z) = (∫ z, φ z * (P z * h z)) - ∫ z, φ z * g z :=
      (integral_congr_ae (ae_of_all _ fun z ↦ by simp only [hF]; ring)).trans
        (integral_sub i₂ i₃)
    have hgφ : ∫ z, g z * φ z = ∫ z, φ z * g z :=
      integral_congr_ae (ae_of_all _ fun z ↦ mul_comm (g z) (φ z))
    linarith [e₁.symm.trans (hw.trans hgφ)]
  have hsmooth := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (k := ⊤)
    (U := ⊤) hFs.contDiffOn hc.continuousOn hdist
  have hΔ := eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp (U := ⊤)
    (hFs.of_le (by simp)).contDiffOn hc.continuousOn hdist
  refine ⟨h, contDiffOn_univ.1 (by simpa using hsmooth), hh, fun z ↦ ?_⟩
  have := hΔ (mem_univ z)
  simp only [hF] at this
  rw [this]
  ring

end TauCeti
