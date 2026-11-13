/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Background
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.InnerProductSpace.Laplacian.LpDecay

/-!
# Decay of solutions of the reduced vortex equation

Let `P` be a complex polynomial. With `h = ‖P‖² / (1 + ‖P‖²)` (`TauCeti.Vortex.backgroundWeight`)
and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`, Taubes's reduced vortex equation for a real function `w` on the
plane is

`Δw = (exp (2w) h - 1) / 8 + g`.

Taubes's variational method produces a solution `w` in the Sobolev space `H¹(ℂ)`, so `w` is
square integrable, but the prescribed-zero vortex problem asks for the boundary condition
`w → 0` at infinity
(`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`).
This file shows that the equation supplies it: a `C²` solution in `Lᵖ(ℂ)`, `1 ≤ p < ∞`, tends to
zero at infinity (`TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`).

The argument uses only the signs and sizes of the coefficients. Since `exp (2w) h ≥ 0` and
`g ≥ 0`, the equation gives `Δw ≥ -1/8`, and an `Lᵖ` function with Laplacian bounded below is
eventually at most `1` (`TauCeti.eventually_le_of_memLp_of_neg_le_laplacian`). Where `w ≤ 1`,
the bounds `h ≤ 1` and `g → 0`
(`Polynomial.tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact`) bound `Δw`
above as well, and an `Lᵖ` function with bounded Laplacian tends to zero
(`TauCeti.tendsto_cocompact_of_memLp_of_abs_laplacian_le`).

For a monic `P` of degree `m ≥ 1`, the field reconstructed from the amplitude `u₀ + w` and the
section `P` (`TauCeti.Vortex.amplitudeField`, with `u₀` the background amplitude) is therefore a
vortex with the degree-`m` end framing `α(z) (z / ‖z‖)⁻ᵐ → 1`
(`TauCeti.Vortex.equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp`). Its section
is `exp (u₀ + w) P`, whose zeros are those of `P` since the exponential factor never vanishes
(`TauCeti.Vortex.isZeroMultiplicity_sectionValue_amplitudeField_prod_sub` records the
multiplicities when `P` is written as a product of linear factors). Thus a `C²`
square-integrable solution of the reduced equation, such as a regular minimizer of Taubes's
functional, gives the vortex with zero divisor `P`. The existence of such a solution is not
proved here.

## Main results

* `TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`: an `Lᵖ` solution of the reduced
  equation, `C²` near infinity, tends to zero at infinity.
* `TauCeti.Vortex.equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp`: a `C²`
  solution in `Lᵖ` on the whole plane reconstructs a framed degree-`m` vortex.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian MeasureTheory
open scoped ENNReal

variable {w : ℂ → ℝ} {p : ℝ≥0∞}

/-- **Decay of `Lᵖ` solutions of the reduced vortex equation.** If `w` lies in `Lᵖ(ℂ)`,
`1 ≤ p < ∞`, and outside a compact set is `C²` and solves the reduced equation
`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`, with `h = ‖P‖² / (1 + ‖P‖²)`, then
`w → 0` at infinity. -/
theorem tendsto_cocompact_of_memLp_of_laplacian_eq {P : Polynomial ℂ}
    (hw : ∀ᶠ z in cocompact ℂ, ContDiffAt ℝ 2 w z) (hwp : MemLp w p) (hp : 1 ≤ p)
    (hp' : p ≠ ∞)
    (heq : ∀ᶠ z in cocompact ℂ, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) :
    Tendsto w (cocompact ℂ) (𝓝 0) := by
  -- Both nonlinear terms are nonnegative, so `Δw ≥ -1/8`, and `w ≤ 1` near infinity.
  have hlow : ∀ᶠ z in cocompact ℂ, -(1 / 8) ≤ Δ w z := heq.mono fun z hz => by
    rw [hz]
    have := mul_nonneg (Real.exp_pos (2 * w z)).le (backgroundWeight_nonneg P.eval z)
    have : 0 ≤ 2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by positivity
    linarith
  have hle := eventually_le_of_memLp_of_neg_le_laplacian hw hwp hp hp' hlow one_pos
  -- Where `w ≤ 1`, `exp (2w) h ≤ exp 2`; the source term tends to zero, so it is at most `1`.
  have hsrc := (tendsto_order.1
    (Polynomial.tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact P)).2 1
    one_pos
  refine tendsto_cocompact_of_memLp_of_abs_laplacian_le hw hwp hp hp'
    (K := Real.exp 2 + 2) ?_
  filter_upwards [heq, hle, hsrc, hlow] with z hz hwz hgz hlowz
  have hexp : Real.exp (2 * w z) * backgroundWeight P.eval z ≤ Real.exp 2 :=
    (mul_le_of_le_one_right (Real.exp_pos _).le (backgroundWeight_lt_one P.eval z).le).trans
      (Real.exp_le_exp.2 (by linarith))
  rw [Polynomial.deriv] at hz
  rw [abs_le]
  constructor
  · linarith [Real.exp_pos 2]
  · rw [hz]
    have : 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ 2 := by
      rw [mul_div_assoc]
      linarith
    linarith [Real.exp_pos 2]

/-- **A square-integrable solution of the reduced equation is a framed vortex.** Let `P` be a
monic polynomial of degree `m ≥ 1` and `w` a `C²` function in `Lᵖ(ℂ)`, `1 ≤ p < ∞`, solving the
reduced equation `Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` on the whole plane. Then the
field reconstructed from the amplitude `u₀ + w` and the section `P` solves the vortex equation
everywhere, and its section has the degree-`m` end framing `α(z) (z / ‖z‖)⁻ᵐ → 1`. -/
theorem equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp {P : Polynomial ℂ}
    (hP : P.Monic) (hm : 0 < P.natDegree) (hw : ContDiff ℝ 2 w) (hwp : MemLp w p) (hp : 1 ≤ p)
    (hp' : p ≠ ∞)
    (heq : ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) :
    (∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z = 0) ∧
      Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) :=
  ⟨fun z => (equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff
      (P.differentiable.analyticAt z) hw.contDiffAt).2 (heq z),
    (tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff hP hm w).2
      (tendsto_cocompact_of_memLp_of_laplacian_eq (Eventually.of_forall fun _ => hw.contDiffAt)
        hwp hp hp' (Eventually.of_forall heq))⟩

end TauCeti.Vortex
