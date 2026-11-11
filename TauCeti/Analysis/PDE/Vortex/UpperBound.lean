/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.WholeSpace

/-!
# The minimizer of Taubes's functional is bounded above

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`. A minimizer `u ∈ H¹(ℂ)` of Taubes's functional
`TauCeti.Vortex.sobolevReducedFunctional P` is a weak solution of the reduced vortex equation

`Δu = (exp (2u) h - 1) / 8 + g`

(`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_value_eq_zero`). The nonlinear term
`exp (2u) h` of an `H¹` function is a priori only locally integrable, which is too weak for the
regularity theory of the equation. Since `exp (2u) h ≥ 0` and `g ≥ 0`, however, the right-hand
side is at least `-1/8`, so `u` is a weak subsolution of `-Δu ≤ 1/8`:

`∫ ⟪∇u, ∇v⟫ ≤ (1/8) ∫ v`

for every bounded nonnegative `v ∈ H¹(ℂ)` vanishing outside a set of finite measure
(`TauCeti.Vortex.integral_inner_gradient_le_of_forall_sobolevReducedFunctional_le`). De Giorgi's
local bound on unit discs, in the form `TauCeti.PDE.exists_ae_value_le_mul_sqrt_integral_add`,
then shows that `u` is essentially bounded above on the whole plane
(`TauCeti.Vortex.exists_ae_value_le_of_forall_sobolevReducedFunctional_le`). Consequently
`exp (2u) h` is essentially bounded, and the right-hand side of the reduced equation is the sum
of a bounded function and the smooth function `g - 1/8`. This is the first step of the
regularity of the minimizer; its Hölder continuity and smoothness are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti.Vortex

variable {P : Polynomial ℂ}

/-- **A minimizer of Taubes's functional is a weak subsolution of `-Δu ≤ 1/8`.** Let
`u ∈ H¹(ℂ)` minimize `TauCeti.Vortex.sobolevReducedFunctional P`, and let `v ∈ H¹(ℂ)` be
nonnegative, bounded, and vanish outside a set of finite measure. Then
`∫ ⟪∇u, ∇v⟫ ≤ (1/8) ∫ v`. -/
theorem integral_inner_gradient_le_of_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    {v : W1p (volume : Measure ℂ) ⊤ 2} {K : Set ℂ} (hK : volume K ≠ ∞) {M : ℝ}
    (hv : ∀ᵐ z, 0 ≤ W1p.value v z) (hvM : ∀ᵐ z, W1p.value v z ≤ M)
    (hvK : ∀ᵐ z, z ∉ K → W1p.value v z = 0) :
    ∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫ ≤ 1 / 8 * ∫ z, W1p.value v z := by
  have hEL := integral_inner_gradient_add_integral_mul_value_eq_zero hm hu hK (M := M)
    (by filter_upwards [hv, hvM] with z h0 hM; rwa [abs_of_nonneg h0]) hvK
  have hv0 : 0 ≤ ∫ z, W1p.value v z := integral_nonneg_of_ae hv
  -- The right-hand side of the reduced equation is at least `-1/8`.
  have hF : ∀ᵐ z, 0 ≤ ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 /
      (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 + 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) *
      W1p.value v z + W1p.value v z / 8 := by
    filter_upwards [hv] with z hz
    have h₁ : 0 ≤ Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)) :=
      by positivity
    have h₂ : 0 ≤ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by positivity
    nlinarith [mul_nonneg h₁ hz, mul_nonneg h₂ hz]
  by_cases hint : Integrable fun z => ((Real.exp (2 * W1p.value u z) * (‖P.eval z‖ ^ 2 /
      (1 + ‖P.eval z‖ ^ 2)) - 1) / 8 + 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) *
      W1p.value v z
  · -- `v` is bounded and vanishes outside a set of finite measure, so it is integrable.
    have hvint : Integrable (W1p.value v) :=
      (Measure.integrableOn_of_bounded (M := M) hK
        (W1p.memLp_value v).aestronglyMeasurable
        (ae_restrict_of_ae (by
          filter_upwards [hv, hvM] with z h0 hM
          rwa [Real.norm_eq_abs, abs_of_nonneg h0]))).integrable_of_ae_notMem_eq_zero hvK
    have h := integral_nonneg_of_ae hF
    rw [integral_add hint (hvint.div_const 8), integral_div] at h
    linarith
  · -- Otherwise the second integral vanishes and the equation reads `∫ ⟪∇u, ∇v⟫ = 0`.
    rw [integral_undef hint] at hEL
    linarith

/-- **The minimizer of Taubes's functional is essentially bounded above.** If `P` has degree at
least one and `u ∈ H¹(ℂ)` minimizes `TauCeti.Vortex.sobolevReducedFunctional P`, then there is a
constant `C` with `u ≤ C` almost everywhere on `ℂ`. Since `‖P‖² / (1 + ‖P‖²) ≤ 1`, the nonlinear
term `exp (2u) ‖P‖² / (1 + ‖P‖²)` of the reduced vortex equation is then at most `exp (2C)`
almost everywhere. -/
theorem exists_ae_value_le_of_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w) :
    ∃ C : ℝ, ∀ᵐ z, W1p.value u z ≤ C := by
  obtain ⟨D, -, hD⟩ := PDE.exists_ae_value_le_mul_sqrt_integral_add (E := ℂ)
  exact ⟨_, hD (by norm_num) fun v K M hK hv hvM hvK =>
    integral_inner_gradient_le_of_forall_sobolevReducedFunctional_le hm hu hK hv hvM hvK⟩

end TauCeti.Vortex
