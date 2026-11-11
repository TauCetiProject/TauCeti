/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Asymptotics
public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
public import TauCeti.Analysis.PDE.Vortex.Variational
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.Minimizer
import TauCeti.Analysis.PDE.Vortex.Regularity

/-!
# Existence of plane vortices with prescribed zeros

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)`
(`TauCeti.Vortex.backgroundWeight`) and `k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`
(`TauCeti.Vortex.backgroundSource`). Taubes's functional `I` on `H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional`) has a minimizer
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), which solves the reduced vortex
equation

`Δw = h (exp (2w) - 1) / 8 + k`

weakly (`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`). The coefficients `h`
and `k` are smooth, so the regularity theorem for the reduced equation,
`TauCeti.Vortex.exists_contDiff_two_ae_eq_and_laplacian_eq`, makes the minimizer a classical
solution: it agrees almost everywhere with a `C²` function `w` that
solves the equation at every point of the plane
(`TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`).

This `w` is square integrable, so by the decay theorem for the reduced equation it tends to zero
at infinity. For monic `P`, the field reconstructed from the amplitude `u₀ + w`, with `u₀` the
background amplitude, and the section `P`, whose section is `exp (u₀ + w) P` and so has the zeros
of `P` with their multiplicities, is therefore a vortex with the degree-`m` end framing
`α(z) (z / ‖z‖)⁻ᵐ → 1` (`TauCeti.Vortex.exists_equation_amplitudeField_eq_zero_and_tendsto`).
This is the existence half of Taubes's classification of plane vortices by their zero divisors,
for each effective divisor of positive degree written as the zero divisor of a monic polynomial.
Uniqueness and the higher regularity of the solution are not treated here.

## Main results

* `TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`:
  a minimizer of Taubes's functional agrees almost everywhere with a `C²` classical solution of
  the reduced vortex equation.
* `TauCeti.Vortex.exists_equation_amplitudeField_eq_zero_and_tendsto`: for every monic `P` of
  positive degree there is a `C²` square-integrable `w` whose reconstructed field is a framed
  vortex with section `exp (u₀ + w) P`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open _root_.MeasureTheory Filter InnerProductSpace Laplacian Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {P : Polynomial ℂ}

/-- **A minimizer of Taubes's functional is a classical solution.** Let `P` be a complex
polynomial of degree at least one, and let `u ∈ H¹(ℂ)` minimize Taubes's functional `I`. Then `u`
agrees almost everywhere with a `C²` function `w` solving the reduced vortex equation
`Δw = h (exp (2w) - 1) / 8 + k` at every point of the plane, with `h = ‖P‖² / (1 + ‖P‖²)` and
`k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`. -/
theorem exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    ∃ w : ℂ → ℝ, ContDiff ℝ 2 w ∧ W1p.value u =ᵐ[volume] w ∧
      ∀ z, Δ w z = backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) / 8 +
        backgroundSource P.eval z := by
  have hP : Differentiable ℂ P.eval := P.differentiable
  refine exists_contDiff_two_ae_eq_and_laplacian_eq Complex.finrank_real_complex
    (contDiff_backgroundWeight (hP.contDiff.restrict_scalars ℝ)) (contDiff_backgroundSource hP)
    fun φ hφ hφc => ?_
  -- The weak Euler–Lagrange equation, with its integrand rewritten in the background coefficients.
  rw [← integral_inner_gradient_add_integral_mul_eq_zero hm hu
    (hφ.of_le (by exact_mod_cast le_top)) hφc]
  congr 2
  ext z
  rw [backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
  ring

/-- **Existence of plane vortices with prescribed zeros.** Let `P` be a monic complex polynomial
of degree `m ≥ 1`. There is a `C²` square-integrable function `w` on the plane such that the field
reconstructed from the amplitude `u₀ + w`, with `u₀` the background amplitude, and the section
`P` solves the vortex equations at every point and has the degree-`m` end framing
`α(z) (z / ‖z‖)⁻ᵐ → 1`. Its section is `exp (u₀ + w) P`, whose zeros are those of `P`. -/
theorem exists_equation_amplitudeField_eq_zero_and_tendsto (hP : P.Monic)
    (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ 2 w ∧ MemLp w 2 ∧
      (∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z = 0) ∧
      Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  obtain ⟨w, hw, huw, hΔ⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm hu
  have hwp : MemLp w 2 := by
    have hu2 := Lp.memLp (W1p.value u)
    simp only [Opens.coe_top, Measure.restrict_univ] at hu2
    exact hu2.ae_eq huw
  refine ⟨w, hw, hwp, equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp hP hm hw
    hwp one_le_two ENNReal.ofNat_ne_top fun z => ?_⟩
  rw [hΔ z, backgroundSource_def]
  ring

end TauCeti.Vortex
