/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.AtInfinity
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Sobolev.Poincare.Planar
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Taubes's functional for the prescribed-zero vortex problem and its coercivity

Let `P` be a complex polynomial of degree `m ≥ 1`, and put

`h = ‖P‖² / (1 + ‖P‖²)`,    `g = 2 ‖P'‖² / (1 + ‖P‖²)²`.

By `TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`, a vortex with
zero divisor `P` is obtained from a solution `w` of the reduced equation

`Δw = (exp (2w) h - 1) / 8 + g`,    `w → 0` at infinity.

This is formally the Euler–Lagrange equation of Taubes's functional

`I(w) = ∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) w`

(`TauCeti.Vortex.reducedFunctional`): the derivative in `w` of the last two integrands is
`(exp (2w) h - 1) / 8 + g`, because `(h - 1) / 8 = -(1 + ‖P‖²)⁻¹ / 8`. The middle integrand is
nonnegative and convex in `w`, and the coefficient `(h - 1) / 8 + g` of the linear term is square
integrable (`TauCeti.Vortex.memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight`). Taubes
obtains the vortex with prescribed zeros as the minimizer of `I`.

The direct method minimizes `I` on `H¹(ℂ) = W^{1,2}(ℂ)`. There `I` is
`TauCeti.Vortex.sobolevReducedFunctional`, with values in `EReal`: the Dirichlet energy
`‖∇u‖₂² / 2` and the linear term are finite, and the potential is an extended nonnegative integral,
so `I(u) = ⊤` exactly when the potential is not integrable. On compactly supported `C¹` functions
the two functionals agree (`TauCeti.Vortex.sobolevReducedFunctional_eq_reducedFunctional`).

The difficulty is coercivity. The potential grows exponentially for positive `u` but only
linearly for negative `u`, and `h` vanishes at the zeros of `P`, so it does not control `‖u‖₂²`
directly. Outside a disc, where `h ≥ 1 / 2`, it bounds `∫ (√(1 + u²) - 1)`, and the planar
estimate `TauCeti.W1p.exists_norm_value_sq_le_of_finrank_eq_two` then bounds `‖u‖₂²` by a constant
times the power `3 / 2` of one plus the energy `‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u)`.
Since the linear term is at most the square root of `‖u‖₂²` times a constant, it is dominated by
the energy. This gives, on `H¹(ℂ)`:

* `TauCeti.Vortex.exists_le_two_mul_sobolevReducedFunctional_add`: the energy is at most
  `2 I(u) + C`;
* `TauCeti.Vortex.exists_le_sobolevReducedFunctional`: `I` is bounded below;
* `TauCeti.Vortex.exists_norm_le_of_sobolevReducedFunctional_le`: each sublevel set of `I` is
  bounded in `H¹(ℂ)`.

For compactly supported `C¹` functions these specialize to
`TauCeti.Vortex.exists_le_two_mul_reducedFunctional_add`,
`TauCeti.Vortex.exists_le_reducedFunctional` and
`TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`. The weak lower semicontinuity of `I`
and the existence of a minimizer are in `TauCeti.Analysis.PDE.Vortex.Minimizer`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Metric Set
open scoped ENNReal Gradient

/-- **Taubes's functional** for the vortex with zero divisor `P`:

`I(w) = ∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) w`,

where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. Formally, its Euler–Lagrange
equation is the reduced equation `Δw = (exp (2w) h - 1) / 8 + g` for the correction `w` of the
background amplitude `TauCeti.Vortex.backgroundAmplitude`. -/
def reducedFunctional (P : Polynomial ℂ) (w : ℂ → ℝ) : ℝ :=
  (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
    (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 +
    ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * w z

/-- The defining formula of Taubes's functional. -/
theorem reducedFunctional_def (P : Polynomial ℂ) (w : ℂ → ℝ) :
    reducedFunctional P w =
      (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * w z := (rfl)

/-! ### Pointwise estimates -/

/-- The elementary algebra behind the bound on `∫ w²`: if `W ≤ 64 k M + k² S` and
`k² ≤ β (1 + M)`, then `W² ≤ (8192 β + 2 β² S²) (1 + M)³`. -/
private theorem sq_le_mul_one_add_pow_three {W k M S β : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hβ : 0 ≤ β) (hW1 : W ≤ 64 * k * M + k ^ 2 * S)
    (hk2 : k ^ 2 ≤ β * (1 + M)) :
    W ^ 2 ≤ (8192 * β + 2 * β ^ 2 * S ^ 2) * (1 + M) ^ 3 := by
  have h1M : 1 ≤ 1 + M := by linarith
  calc W ^ 2 ≤ (64 * k * M + k ^ 2 * S) ^ 2 := pow_le_pow_left₀ hW hW1 2
    _ ≤ 8192 * k ^ 2 * M ^ 2 + 2 * (k ^ 2) ^ 2 * S ^ 2 := by
        nlinarith [sq_nonneg (64 * k * M - k ^ 2 * S)]
    _ ≤ 8192 * (β * (1 + M)) * (1 + M) ^ 2 + 2 * (β * (1 + M)) ^ 2 * S ^ 2 := by
        gcongr
        nlinarith
    _ ≤ (8192 * β + 2 * β ^ 2 * S ^ 2) * (1 + M) ^ 3 := by
        have : (1 + M) ^ 2 ≤ (1 + M) ^ 3 := pow_le_pow_right₀ h1M (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * β ^ 2 * S ^ 2)]

/-- If `x⁴ ≤ D (1 + M)³` with `D, M ≥ 0`, then `x ≤ (1 + M) / 2 + 8 D`: a quantity of order
`(1 + M) ^ (3/4)` is absorbed by half of `1 + M`. -/
private theorem le_div_two_add_of_pow_four_le {x D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hx4 : x ^ 4 ≤ D * (1 + M) ^ 3) : x ≤ (1 + M) / 2 + 8 * D := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 1 + M < 2 * x := by linarith
  have h2 : 8 * D < x := by linarith
  have h3 : (1 + M) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by linarith) h1.le 3
  have h4 : D * (1 + M) ^ 3 ≤ 8 * D * x ^ 3 := by nlinarith
  have h5 : 8 * D * x ^ 3 < x * x ^ 3 :=
    mul_lt_mul_of_pos_right h2 (pow_pos (by linarith) 3)
  nlinarith

/-! ### Taubes's functional on `H¹(ℂ)` -/

/-- **Taubes's functional on `H¹(ℂ) = W^{1,2}(ℂ)`**, with values in `EReal`:

`I(u) = ‖∇u‖₂² / 2 + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u + (1 / 16) ∫⁻ h (exp (2u) - 1 - 2u)`,

where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. The first two terms are finite for
every `u`. The potential is a nonnegative extended integral, so `I(u) = ⊤` exactly when it is not
integrable (`TauCeti.Vortex.sobolevReducedFunctional_eq_coe`,
`TauCeti.Vortex.sobolevReducedFunctional_eq_top`). On compactly supported `C¹` functions this is
`TauCeti.Vortex.reducedFunctional`
(`TauCeti.Vortex.sobolevReducedFunctional_eq_reducedFunctional`). -/
def sobolevReducedFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : EReal :=
  ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
    (((∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal)

/-- The defining formula of Taubes's functional on `H¹(ℂ)`. -/
theorem sobolevReducedFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 /
          (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
        (((∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal) :=
  (rfl)

variable {P : Polynomial ℂ}

/-- The value of an element of `H¹(ℂ)` is square integrable for Lebesgue measure. -/
private theorem memLp_value (u : W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (W1p.value u : ℂ → ℝ) 2 := by
  have h := Lp.memLp (W1p.value u)
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
  exact h

/-- The potential `h (exp (2u) - 1 - 2u)` of an element of `H¹(ℂ)` is measurable. -/
private theorem aestronglyMeasurable_potential (u : W1p (volume : Measure ℂ) ⊤ 2) :
    AEStronglyMeasurable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
  have hh : Continuous fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    fun_prop (disch := intro z; positivity)
  have hΦ : Continuous fun t : ℝ ↦ Real.exp (2 * t) - 1 - 2 * t := by fun_prop
  exact hh.aestronglyMeasurable.mul (hΦ.comp_aestronglyMeasurable
    (memLp_value u).aestronglyMeasurable)

/-- The potential `h (exp (2w) - 1 - 2w)` is nonnegative. -/
private theorem potential_nonneg (w : ℂ → ℝ) (z : ℂ) :
    0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
  mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)

/-- The integral of the potential `h (exp (2w) - 1 - 2w)` is nonnegative. -/
private theorem integral_potential_nonneg (w : ℂ → ℝ) :
    0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
  integral_nonneg fun z ↦ potential_nonneg w z

/-- When the potential is integrable, Taubes's functional on `H¹(ℂ)` is the real number
`‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u`. -/
theorem sobolevReducedFunctional_eq_coe {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :
    sobolevReducedFunctional P u =
      ((‖W1p.gradient u‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) := by
  have hE := integral_potential_nonneg (P := P) (W1p.value u)
  have h16 : ENNReal.ofReal (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 =
      ENNReal.ofReal ((∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [sobolevReducedFunctional_def, ← ofReal_integral_eq_lintegral_ofReal hu
    (ae_of_all _ (potential_nonneg _)), h16, EReal.coe_ennreal_ofReal,
    max_eq_left (by positivity), ← EReal.coe_add]
  congr 1
  ring

/-- When the potential is not integrable, Taubes's functional on `H¹(ℂ)` is `⊤`. -/
theorem sobolevReducedFunctional_eq_top {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ¬Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :
    sobolevReducedFunctional P u = ⊤ := by
  have hinf : ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) = ⊤ := by
    by_contra hne
    exact hu ⟨aestronglyMeasurable_potential u, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (potential_nonneg _))).2 (lt_top_iff_ne_top.2 hne)⟩
  rw [sobolevReducedFunctional_def, hinf, ENNReal.top_div_of_ne_top (by norm_num),
    EReal.coe_ennreal_top, EReal.coe_add_top]

/-- Taubes's functional vanishes at `0`. -/
@[simp]
theorem sobolevReducedFunctional_zero : sobolevReducedFunctional P 0 = 0 := by
  have hv0 : W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) = 0 := by
    rw [← W1p.valueL_apply, map_zero]
  have hg0 : W1p.gradient (0 : W1p (volume : Measure ℂ) ⊤ 2) = 0 := by
    rw [← W1p.gradientL_apply, map_zero]
  have h0 : (W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) : ℂ → ℝ) =ᵐ[volume] 0 := by
    have h := Lp.coeFn_zero ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : TopologicalSpace.Opens ℂ) :
      Set ℂ))
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    rw [hv0]
    exact h
  have hpot : (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) z) - 1 -
        2 * W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) z)) =ᵐ[volume] 0 :=
    h0.mono fun z hz ↦ by simp [hz]
  have hlin : (fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) z) =ᵐ[volume] 0 :=
    h0.mono fun z hz ↦ by simp [hz]
  have hint : Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) z) - 1 -
        2 * W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) z)) :=
    (integrable_congr hpot).2 (integrable_zero ℂ ℝ volume)
  rw [sobolevReducedFunctional_eq_coe hint, integral_congr_ae hpot, integral_congr_ae hlin, hg0]
  simp

/-- The squared `L²` norm of the weak gradient of a representative of a compactly supported `C¹`
function `w` is the Dirichlet energy `∫ ‖Dw‖²`. -/
private theorem norm_gradient_sq_eq {w : ℂ → ℝ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hg : (W1p.gradient u : ℂ → ℂ) =ᵐ[volume] ∇ w) :
    ‖W1p.gradient u‖ ^ 2 = ∫ z, ‖fderiv ℝ w z‖ ^ 2 := by
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  exact integral_congr_ae (hg.mono fun z hz ↦ by simp only [hz, norm_gradient_eq_norm_fderiv])

/-- On a compactly supported continuous function `w` whose gradient represents the weak gradient
of `u ∈ H¹(ℂ)`, Taubes's functional on `H¹(ℂ)` is `TauCeti.Vortex.reducedFunctional`. Every
compactly supported `C¹` function has such a representative, by
`TauCeti.W1p.exists_value_gradient_ae_eq_of_contDiffOn`. -/
theorem sobolevReducedFunctional_eq_reducedFunctional {w : ℂ → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : (W1p.value u : ℂ → ℝ) =ᵐ[volume] w) (hg : (W1p.gradient u : ℂ → ℂ) =ᵐ[volume] ∇ w) :
    sobolevReducedFunctional P u = reducedFunctional P w := by
  have hpot : (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) =ᵐ[volume]
      fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    hv.mono fun z hz ↦ by simp only [hz]
  have hE := integral_congr_ae hpot
  have hlin : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * w z :=
    integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])
  rw [sobolevReducedFunctional_eq_coe ((integrable_congr hpot).2
    (integrable_mul_exp_sub_one_sub P hw hws)), reducedFunctional_def, hE, hlin,
    norm_gradient_sq_eq hg]

/-- Every compactly supported `C¹` function `w` is represented in `H¹(ℂ)`, with the same value of
Taubes's functional and the same `L²` norms of `w` and `Dw`. -/
private theorem exists_sobolevReducedFunctional_eq {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2,
      sobolevReducedFunctional P u = reducedFunctional P w ∧
      ‖W1p.value u‖ ^ 2 = ∫ z, w z ^ 2 ∧ ‖W1p.gradient u‖ ^ 2 = ∫ z, ‖fderiv ℝ w z‖ ^ 2 ∧
      (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) =
        ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  obtain ⟨u, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn
    (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2) hw.contDiffOn
    (hw.continuous.memLp_of_hasCompactSupport hws) (hws.memLp_gradient hw)
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hv hg
  refine ⟨u, sobolevReducedFunctional_eq_reducedFunctional hw.continuous hws hv hg, ?_, ?_,
    integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])⟩
  · rw [← W1p.integral_value_sq_eq_norm_value_sq]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])
  · exact norm_gradient_sq_eq hg

/-! ### Coercivity -/

/-- The coefficient `g - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's functional, where
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`, is square integrable when `P` has degree at least one. -/
theorem memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) 2 := by
  have h1 := (P.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).const_mul 2
  have h2 := (Polynomial.memLp_inv_one_add_norm_eval_sq hm).const_mul (1 / 8 : ℝ)
  convert h1.sub h2 using 1
  funext z
  simp only [Pi.sub_apply]
  ring

/-- The coercion of `2 a + b` from `ℝ` to `EReal`. -/
private theorem coe_two_mul_add (a b : ℝ) : ((2 * a + b : ℝ) : EReal) = 2 * (a : EReal) + b := by
  rw [EReal.coe_add, EReal.coe_mul]
  rfl

/-- Outside a disc where `‖P‖ ≥ 1`, so that `h ≥ 1 / 2`, the modular `√(1 + w²) - 1` is at most
twice the potential term `h (exp (2w) - 1 - 2w)`. -/
private theorem setIntegral_compl_closedBall_le {R : ℝ}
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖P.eval z‖) {w : ℂ → ℝ}
    (hw : AEStronglyMeasurable w)
    (hpint : Integrable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) :
    ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1) ≤
      2 * ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  have hle (z : ℂ) (hz : z ∈ (closedBall (0 : ℂ) R)ᶜ) : √(1 + w z ^ 2) - 1 ≤
      2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) := by
    have h1 := hR z hz
    have hh : 1 / 2 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have := Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (w z)
    have := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (w z)
    nlinarith
  have hmod : IntegrableOn (fun z ↦ √(1 + w z ^ 2) - 1) (closedBall (0 : ℂ) R)ᶜ := by
    refine (hpint.const_mul 2).integrableOn.mono' ((by fun_prop : Continuous fun t : ℝ ↦
      √(1 + t ^ 2) - 1).comp_aestronglyMeasurable hw).restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_closedBall.compl] with z hz
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (Real.one_le_sqrt_one_add_sq _))]
    exact hle z hz
  rw [← integral_const_mul]
  calc ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1)
      ≤ ∫ z in (closedBall (0 : ℂ) R)ᶜ, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) :=
        setIntegral_mono_on hmod (hpint.const_mul 2).integrableOn
          measurableSet_closedBall.compl hle
    _ ≤ ∫ z, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) :=
        setIntegral_le_integral (hpint.const_mul 2)
          (Eventually.of_forall fun z ↦ mul_nonneg zero_le_two (potential_nonneg w z))

/-- The energy `‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u)` controls `‖u‖₂²`: its square is at
most a constant times the cube of one plus the energy. -/
private theorem exists_sq_norm_value_sq_le (hm : 0 < P.natDegree) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      (Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      (‖W1p.value u‖ ^ 2) ^ 2 ≤ γ * (1 + (‖W1p.gradient u‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16)) ^ 3 := by
  obtain ⟨C₀, hC₀, hpl⟩ :=
    W1p.exists_norm_value_sq_le_of_finrank_eq_two (volume : Measure ℂ) Complex.finrank_real_complex
  -- A nonconstant polynomial has modulus at least one outside a closed disc.
  obtain ⟨R, -, hR⟩ := (hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp
    (by
      rw [cobounded_eq_cocompact]
      exact (P.tendsto_norm_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp hm)
        tendsto_norm_cocompact_atTop).eventually_ge_atTop 1 :
      ∀ᶠ z in Bornology.cobounded ℂ, 1 ≤ ‖P.eval z‖)
  set S := volume.real (closedBall (0 : ℂ) R)
  set β := 8 + 4 * C₀ ^ 2
  refine ⟨8192 * β + 2 * β ^ 2 * S ^ 2, by positivity, fun u hpint ↦ ?_⟩
  set G := ‖W1p.gradient u‖
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  set M := G ^ 2 / 2 + E / 16
  set k := 2 + C₀ * G
  have hE : 0 ≤ E := integral_potential_nonneg _
  have hk : 0 ≤ k := by positivity
  -- The planar estimate with `s` the disc: `‖u‖₂² ≤ 2 k (2 E) + k² S ≤ 64 k M + k² S`.
  have hW1 : ‖W1p.value u‖ ^ 2 ≤ 64 * k * M + k ^ 2 * S := by
    have h := hpl u (closedBall (0 : ℂ) R) measurableSet_closedBall measure_closedBall_lt_top.ne
    have h2 := mul_le_mul_of_nonneg_left (setIntegral_compl_closedBall_le hR
      (memLp_value u).aestronglyMeasurable hpint) (by positivity : 0 ≤ 2 * k)
    have h3 : 2 * k * (2 * E) ≤ 64 * k * M := by
      have : E ≤ 16 * M := by simp only [M]; nlinarith [sq_nonneg G]
      nlinarith
    linarith
  -- `k² ≤ 8 + 2 C₀² G² ≤ β (1 + M)`.
  have hk2 : k ^ 2 ≤ β * (1 + M) := by
    have : k ^ 2 ≤ 8 + 2 * C₀ ^ 2 * G ^ 2 := by
      simp only [k]
      nlinarith [sq_nonneg (2 - C₀ * G)]
    have : G ^ 2 ≤ 2 * M := by simp only [M]; linarith
    simp only [β]
    nlinarith [sq_nonneg C₀]
  exact sq_le_mul_one_add_pow_three (by positivity) (by positivity) (by positivity) hW1 hk2

/-- **Coercivity of Taubes's functional on `H¹(ℂ)`.** For a complex polynomial `P` of degree at
least one there is a constant `C` such that every `u ∈ H¹(ℂ)` with integrable potential satisfies

`‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) ≤ 2 I(u) + C`,

where `I` is `TauCeti.Vortex.sobolevReducedFunctional P` and `h = ‖P‖² / (1 + ‖P‖²)`. -/
theorem exists_le_two_mul_sobolevReducedFunctional_add (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      (Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      ((‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 : ℝ) : EReal) ≤
        2 * sobolevReducedFunctional P u + C := by
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_norm_value_sq_le hm
  set c : ℂ → ℝ := fun z ↦
    2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8
  have hc : MemLp c 2 := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  set K := ∫ z, c z ^ 2
  set D := K ^ 2 * γ
  refine ⟨1 + 16 * D, fun u hpint ↦ ?_⟩
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  set M := ‖W1p.gradient u‖ ^ 2 / 2 + E / 16
  have hM : 0 ≤ M := by
    have : 0 ≤ E := integral_potential_nonneg _
    positivity
  -- The linear term: `x = |∫ c u|` has `x² ≤ K ‖u‖₂²`, hence `x⁴ ≤ D (1 + M)³`.
  set x := |∫ z, c z * W1p.value u z|
  have hx2 : x ^ 2 ≤ K * ‖W1p.value u‖ ^ 2 := by
    rw [sq_abs, ← W1p.integral_value_sq_eq_norm_value_sq]
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
    exact sq_integral_mul_le_integral_sq_mul_integral_sq hc (memLp_value u)
  have hx4 : x ^ 4 ≤ D * (1 + M) ^ 3 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ ≤ (K * ‖W1p.value u‖ ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg x) hx2 2
      _ = K ^ 2 * (‖W1p.value u‖ ^ 2) ^ 2 := by ring
      _ ≤ K ^ 2 * (γ * (1 + M) ^ 3) := by gcongr; exact hsq u hpint
      _ = D * (1 + M) ^ 3 := by simp only [D]; ring
  have hxM := le_div_two_add_of_pow_four_le (by positivity) hM hx4
  have key : M ≤ 2 * (M + ∫ z, c z * W1p.value u z) + (1 + 16 * D) := by
    linarith [neg_abs_le (∫ z, c z * W1p.value u z)]
  rw [sobolevReducedFunctional_eq_coe hpint, ← coe_two_mul_add, EReal.coe_le_coe_iff]
  exact key

/-- Taubes's functional on `H¹(ℂ)` is bounded below. -/
theorem exists_le_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2, (C : EReal) ≤ sobolevReducedFunctional P u := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_sobolevReducedFunctional_add hm
  refine ⟨-C / 2, fun u ↦ ?_⟩
  by_cases hpint : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  · have h := hC u hpint
    have hE := integral_potential_nonneg (P := P) (W1p.value u)
    rw [sobolevReducedFunctional_eq_coe hpint, ← coe_two_mul_add, EReal.coe_le_coe_iff] at h
    rw [sobolevReducedFunctional_eq_coe hpint, EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg ‖W1p.gradient u‖]
  · rw [sobolevReducedFunctional_eq_top hpint]
    exact le_top

/-- **Bounded sublevel sets.** For a complex polynomial `P` of degree at least one and every
level `t`, the elements `u ∈ H¹(ℂ)` with `I(u) ≤ t` are bounded in `H¹(ℂ)`; here `I` is
`TauCeti.Vortex.sobolevReducedFunctional P`. -/
theorem exists_norm_le_of_sobolevReducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2, sobolevReducedFunctional P u ≤ t → ‖u‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_le_two_mul_sobolevReducedFunctional_add hm
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_norm_value_sq_le hm
  set B := 2 * t + C₁
  refine ⟨√(2 * B + 1 + γ * (1 + B) ^ 3), fun u ht ↦ ?_⟩
  have hpint : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
    by_contra hpint
    rw [sobolevReducedFunctional_eq_top hpint] at ht
    exact EReal.coe_ne_top t (top_le_iff.mp ht)
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  set G := ‖W1p.gradient u‖
  set W := ‖W1p.value u‖ ^ 2
  have hE : 0 ≤ E := integral_potential_nonneg _
  have hMB : G ^ 2 / 2 + E / 16 ≤ B := by
    have hI := sobolevReducedFunctional_eq_coe hpint
    have h := hC₁ u hpint
    rw [hI, ← coe_two_mul_add, EReal.coe_le_coe_iff] at h
    rw [hI, EReal.coe_le_coe_iff] at ht
    simp only [B]
    linarith
  have hW2 : W ^ 2 ≤ γ * (1 + B) ^ 3 := by
    refine (hsq u hpint).trans (mul_le_mul_of_nonneg_left ?_ hγ)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hW : W ≤ 1 + γ * (1 + B) ^ 3 := by nlinarith [sq_nonneg (W - 1)]
  rw [← Real.sqrt_sq (norm_nonneg u), W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg G])

/-- **Coercivity of Taubes's functional.** For a complex polynomial `P` of degree at least one
there is a constant `C` such that every compactly supported `C¹` function `w` satisfies

`∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) ≤ 2 I(w) + C`,

where `I` is `TauCeti.Vortex.reducedFunctional P` and `h = ‖P‖² / (1 + ‖P‖²)`. -/
theorem exists_le_two_mul_reducedFunctional_add (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
          (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 ≤
        2 * reducedFunctional P w + C := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_sobolevReducedFunctional_add hm
  refine ⟨C, fun w hw hws ↦ ?_⟩
  obtain ⟨u, hI, -, hG, hE⟩ := exists_sobolevReducedFunctional_eq (P := P) hw hws
  have hpint : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
    by_contra hpint
    rw [sobolevReducedFunctional_eq_top hpint] at hI
    exact EReal.coe_ne_top _ hI.symm
  have h := hC u hpint
  rw [hI, hG, hE, ← coe_two_mul_add, EReal.coe_le_coe_iff] at h
  exact h

/-- Taubes's functional is bounded below on compactly supported `C¹` functions. -/
theorem exists_le_reducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → C ≤ reducedFunctional P w := by
  obtain ⟨C, hC⟩ := exists_le_sobolevReducedFunctional hm
  refine ⟨C, fun w hw hws ↦ ?_⟩
  obtain ⟨u, hI, -⟩ := exists_sobolevReducedFunctional_eq (P := P) hw hws
  exact EReal.coe_le_coe_iff.mp (hI ▸ hC u)

/-- **Bounded sublevel sets.** For a complex polynomial `P` of degree at least one and every
level `t`, the compactly supported `C¹` functions `w` with `I(w) ≤ t` have uniformly bounded
Dirichlet energy `∫ ‖Dw‖²` and `L²` norm `∫ w²`; here `I` is
`TauCeti.Vortex.reducedFunctional P`. -/
theorem exists_integral_le_of_reducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → reducedFunctional P w ≤ t →
      ∫ z, ‖fderiv ℝ w z‖ ^ 2 ≤ C ∧ ∫ z, w z ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_sobolevReducedFunctional_le hm t
  refine ⟨C ^ 2, fun w hw hws ht ↦ ?_⟩
  obtain ⟨u, hI, hW, hG, -⟩ := exists_sobolevReducedFunctional_eq (P := P) hw hws
  have hu := hC u (by rw [hI]; exact_mod_cast ht)
  have hsq := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  have hu2 : ‖u‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  rw [← hW, ← hG]
  constructor <;> nlinarith [sq_nonneg ‖W1p.value u‖, sq_nonneg ‖W1p.gradient u‖]

end TauCeti.Vortex
