/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Asymptotics
public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.Minimizer
import TauCeti.Analysis.PDE.Vortex.Regularity
import TauCeti.Analysis.PDE.Vortex.Variational

/-!
# Existence of plane vortices with prescribed zeros

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)`
(`TauCeti.Vortex.backgroundWeight`). Taubes's functional `I` on `H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional`) attains its minimum
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), and a minimizer `u` is a weak
solution of the reduced vortex equation

`Δu = (exp (2u) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`

(`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`). This file shows that `u` has a
smooth representative that solves the equation at every point of the plane
(`TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`).
The weak equation has the form treated in `TauCeti.Analysis.PDE.Vortex.Regularity`, with the
smooth coefficients `TauCeti.Vortex.backgroundWeight` and `TauCeti.Vortex.backgroundSource` of
`P`, whose smooth-regularity theorem applies.

The smooth representative `w` lies in `L²(ℂ)`, because `u` does, so it tends to zero at infinity
(`TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`). For monic `P`, the field
reconstructed from the amplitude `u₀ + w`, with `u₀ = -log (1 + ‖P‖²) / 2` the background
amplitude, and from the section `P` (`TauCeti.Vortex.amplitudeField`) is therefore a smooth
solution of the vortex equations with the degree-`m` end framing `α(z) (z / ‖z‖)⁻ᵐ → 1`
(`TauCeti.Vortex.exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto`). Its section is
`exp (u₀ + w) P` (`TauCeti.Vortex.sectionValue_amplitudeField`), whose zeros are those of `P`, with
multiplicity. This is the existence half of Taubes's classification of plane vortices by their
zero divisors; the uniqueness half is `TauCeti.Vortex.existsUnique_framedGaugeGroup_smul_eq`.

## Main results

* `TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`:
  a minimizer of Taubes's functional has a smooth representative solving the reduced vortex
  equation everywhere.
* `TauCeti.Vortex.exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto`: for monic `P` of
  degree `m ≥ 1`, there is a smooth square-integrable correction `w` for which the field
  reconstructed from `u₀ + w` and `P` is a smooth framed degree-`m` vortex.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace InnerProductSpace Laplacian
open scoped ContDiff Distributions Gradient RealInnerProductSpace

namespace TauCeti.Vortex

variable {P : Polynomial ℂ}

/-- **Smoothness of the minimizer of Taubes's functional.** Let `P` have degree at least one and
let `u ∈ H¹(ℂ)` minimize Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P`. Then `u`
agrees almost everywhere with a smooth function `w` that solves the reduced vortex equation

`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`,    `h = ‖P‖² / (1 + ‖P‖²)`,

at every point of the plane. -/
theorem exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ W1p.value u =ᵐ[volume] w ∧
      ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  -- The weak Euler–Lagrange equation, written with the coefficients `h` and `k` of the reduced
  -- equation `Δw = h (exp (2w) - 1) / 8 + k`.
  have hw : ∀ φ : 𝓓((⊤ : Opens ℂ), ℝ),
      ∫ z in (⊤ : Opens ℂ), ⟪W1p.gradient u z, ∇ (φ : ℂ → ℝ) z⟫ =
        -∫ z in (⊤ : Opens ℂ), (backgroundWeight P.eval z *
          (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * φ z := by
    intro φ
    have h := integral_inner_gradient_add_integral_mul_eq_zero hm hu
      (φ.contDiff.of_le (by exact_mod_cast le_top)) φ.hasCompactSupport
    simp only [Opens.coe_top, Measure.restrict_univ]
    rw [eq_neg_iff_add_eq_zero, ← h]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
    ring
  obtain ⟨g, hg, hug, hΔ⟩ :=
    exists_contDiffOn_ae_eq_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg
      Complex.finrank_real_complex (contDiff_backgroundWeight
        ((P.differentiable.contDiff).restrict_scalars ℝ)).contDiffOn
      (contDiff_backgroundSource P.differentiable).contDiffOn hw
  refine ⟨g, contDiffOn_univ.1 (by simpa using hg), by simpa using hug, fun z => ?_⟩
  rw [hΔ z (by simp), backgroundSource_def]
  ring

/-- **Existence of framed plane vortices with prescribed zeros.** Let `P` be a monic complex
polynomial of degree `m ≥ 1` and let `u₀ = -log (1 + ‖P‖²) / 2` be its background amplitude. There
is a smooth square-integrable function `w` on the plane such that the field reconstructed from the
amplitude `u₀ + w` and the section `P` is smooth, solves the vortex equations everywhere, and has
the degree-`m` end framing `α(z) (z / ‖z‖)⁻ᵐ → 1` at infinity. Its section is `exp (u₀ + w) P`
(`TauCeti.Vortex.sectionValue_amplitudeField`), so its zeros are those of `P`, with
multiplicity. -/
theorem exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto (hP : P.Monic)
    (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ MemLp w 2 ∧
      ContDiff ℝ ∞ (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) ∧
      (∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z = 0) ∧
      Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  obtain ⟨w, hw, huw, hΔ⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm hu
  have hw2 : MemLp w 2 := by
    have hL := Lp.memLp (W1p.value u)
    simp only [Opens.coe_top, Measure.restrict_univ] at hL
    exact hL.ae_eq huw
  have hP' : ContDiff ℝ ∞ P.eval := (P.differentiable.contDiff).restrict_scalars ℝ
  obtain ⟨hsol, hfr⟩ := equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp hP hm
    (hw.of_le (by simp)) hw2 one_le_two ENNReal.ofNat_ne_top hΔ
  exact ⟨w, hw, hw2, contDiff_amplitudeField (n := ⊤)
    ((contDiff_backgroundAmplitude hP').add hw) hP', hsol, hfr⟩

end TauCeti.Vortex
