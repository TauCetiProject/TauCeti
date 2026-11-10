/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.AtInfinity
public import TauCeti.Analysis.Sobolev.Poincare.Planar
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Taubes's functional for the prescribed-zero vortex problem

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
integrable. Taubes obtains the vortex with prescribed zeros as the minimizer of `I`.

## The functional on `H¹(ℂ)`

The direct method needs `I` on the Hilbert space `H¹(ℂ) = W^{1,2}(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional`). There the potential term is the extended integral of
a nonnegative function, which may be `∞`, so the functional takes values in `EReal`. It is finite
exactly when the potential is integrable (`TauCeti.Vortex.sobolevReducedFunctional_ne_top_iff`),
and it agrees with `I` on compactly supported `C¹` corrections
(`TauCeti.Vortex.sobolevReducedFunctional_eq_reducedFunctional`).

## Coercivity

The middle term grows exponentially for positive `w` but only linearly for negative `w`, and `h`
vanishes at the zeros of `P`, so it does not control `∫ w²` directly. Outside a disc, where
`h ≥ 1 / 2`, it bounds `∫ (√(1 + w²) - 1)`, and the planar estimate
`TauCeti.W1p.exists_norm_value_sq_le_of_finrank_eq_two` then bounds `∫ w²` by a constant times
the power `3 / 2` of one plus the energy `∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w)`. Since
the linear term is at most the square root of `∫ w²` times a constant, it is dominated by the
energy. For compactly supported `C¹` functions this gives:

* `TauCeti.Vortex.exists_le_two_mul_reducedFunctional_add`: the energy is at most `2 I(w) + C`;
* `TauCeti.Vortex.exists_le_reducedFunctional`: `I` is bounded below;
* `TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`: on each sublevel set of `I`,
  `∫ ‖Dw‖²` and `∫ w²` are bounded, with a constant independent of `w`.

On `H¹(ℂ)` the functional is bounded below
(`TauCeti.Vortex.exists_le_sobolevReducedFunctional`) and its sublevel sets are bounded
(`TauCeti.Vortex.exists_norm_le_of_sobolevReducedFunctional_le`).

## Existence of a minimizer

The quadratic and linear terms are convex and continuous, and the potential term is weakly lower
semicontinuous (`TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub`), so the
functional is weakly lower semicontinuous on `H¹(ℂ)`
(`TauCeti.Vortex.lowerSemicontinuous_sobolevReducedFunctional`). Closed balls of the Hilbert
space `H¹(ℂ)` are weakly compact, so the functional attains its minimum on a ball containing the
sublevel set below `I(0) = 0`, which is then a global minimum
(`TauCeti.Vortex.exists_isMinOn_sobolevReducedFunctional`). The weak Euler–Lagrange equation of
the minimizer and its regularity are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Metric Set TopologicalSpace
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

/-- **Taubes's functional on `H¹(ℂ)`** for the vortex with zero divisor `P`:

`I(u) = ‖∇u‖₂² / 2 + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u + (1 / 16) ∫ h (exp (2u) - 1 - 2u)`,

with `h` and `g` as in `TauCeti.Vortex.reducedFunctional`, for `u` in the Sobolev space
`W^{1,2}(ℂ)`, with value `TauCeti.W1p.value u` and weak gradient `TauCeti.W1p.gradient u`. The
potential term is the extended integral of a nonnegative function, so `I(u) = ⊤` exactly when it
is not integrable (`TauCeti.Vortex.sobolevReducedFunctional_ne_top_iff`). -/
def sobolevReducedFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : EReal :=
  ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
    (((∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal)

/-- The defining formula of Taubes's functional on `H¹(ℂ)`. -/
theorem sobolevReducedFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
        (((∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal) :=
  (rfl)

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

/-- The bound on `∫ w²` from the planar estimate: if `W ≤ 2 k Q + k² S` with `k = 2 + C₀ a`, and
the modular `Q` is at most twice the potential `E`, then `W² ≤ γ (1 + M)³` for the energy
`M = a² / 2 + E / 16` and a constant `γ` depending only on `C₀` and `S`. -/
private theorem sq_le_of_le_planar {C₀ S a E Q W : ℝ} (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a) (hE : 0 ≤ E)
    (hW : 0 ≤ W) (hWQ : W ≤ 2 * (2 + C₀ * a) * Q + (2 + C₀ * a) ^ 2 * S) (hQ : Q ≤ 2 * E) :
    W ^ 2 ≤ (8192 * (8 + 4 * C₀ ^ 2) + 2 * (8 + 4 * C₀ ^ 2) ^ 2 * S ^ 2) *
      (1 + (a ^ 2 / 2 + E / 16)) ^ 3 := by
  set M := a ^ 2 / 2 + E / 16
  set k := 2 + C₀ * a
  have hk : 0 ≤ k := by positivity
  refine sq_le_mul_one_add_pow_three (k := k) hW (by positivity) (by positivity) ?_ ?_
  · -- `2 k Q ≤ 2 k (2 E) ≤ 64 k M`.
    have h2 : 2 * k * Q ≤ 2 * k * (2 * E) := mul_le_mul_of_nonneg_left hQ (by positivity)
    have h3 : 2 * k * (2 * E) ≤ 64 * k * M := by
      have : E ≤ 16 * M := by simp only [M]; nlinarith [sq_nonneg a]
      nlinarith
    linarith
  · -- `k² ≤ 8 + 2 C₀² a² ≤ (8 + 4 C₀²) (1 + M)`.
    have : k ^ 2 ≤ 8 + 2 * C₀ ^ 2 * a ^ 2 := by
      simp only [k]
      nlinarith [sq_nonneg (2 - C₀ * a)]
    have : a ^ 2 ≤ 2 * M := by simp only [M]; linarith
    nlinarith [sq_nonneg C₀]

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

/-- Absorbing the linear term: if `L² ≤ K W` and `W² ≤ γ (1 + M)³` with `M ≥ 0`, then
`M ≤ 2 (M + L) + 1 + 16 K² γ`. -/
private theorem le_two_mul_add_add_of_sq_le {M W L K γ : ℝ} (hM : 0 ≤ M) (hγ : 0 ≤ γ)
    (hL : L ^ 2 ≤ K * W) (hW : W ^ 2 ≤ γ * (1 + M) ^ 3) :
    M ≤ 2 * (M + L) + (1 + 16 * (K ^ 2 * γ)) := by
  have hx4 : |L| ^ 4 ≤ K ^ 2 * γ * (1 + M) ^ 3 := by
    calc |L| ^ 4 = (L ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
      _ ≤ (K * W) ^ 2 := pow_le_pow_left₀ (sq_nonneg L) hL 2
      _ = K ^ 2 * W ^ 2 := by ring
      _ ≤ K ^ 2 * (γ * (1 + M) ^ 3) := by gcongr
      _ = K ^ 2 * γ * (1 + M) ^ 3 := by ring
  have hxM := le_div_two_add_of_pow_four_le (by positivity) hM hx4
  linarith [neg_abs_le L]

/-! ### Sobolev corrections -/

variable {P : Polynomial ℂ}

/-- The whole-space restriction of Lebesgue measure on the plane is Lebesgue measure. -/
private theorem volume_restrict_top :
    (volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ) = volume := by
  simp

private theorem memLp_value (u : W1p (volume : Measure ℂ) ⊤ 2) : MemLp (W1p.value u) 2 := by
  simpa only [volume_restrict_top] using Lp.memLp (W1p.value u)

private theorem integral_value_sq (u : W1p (volume : Measure ℂ) ⊤ 2) :
    ∫ z, W1p.value u z ^ 2 = ‖W1p.value u‖ ^ 2 := by
  rw [← W1p.integral_value_sq_eq_norm_value_sq]
  simp only [volume_restrict_top]

/-- The coefficient `g - (1 + ‖P‖²)⁻¹ / 8` of the linear term is square integrable. -/
private theorem memLp_coefficient (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) 2 := by
  have h1 := (P.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).const_mul 2
  have h2 := (Polynomial.memLp_inv_one_add_norm_eval_sq hm).const_mul (1 / 8 : ℝ)
  convert h1.sub h2 using 1
  funext z
  simp only [Pi.sub_apply]
  ring

private theorem potential_nonneg (P : Polynomial ℂ) (z : ℂ) (t : ℝ) :
    0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * t) - 1 - 2 * t) :=
  mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg t)

private theorem aestronglyMeasurable_potential {w : ℂ → ℝ} (hw : AEStronglyMeasurable w) :
    AEStronglyMeasurable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  have hh : Continuous fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    fun_prop (disch := intro z; positivity)
  exact hh.aestronglyMeasurable.mul
    ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (2 * t) - 1 - 2 * t).comp_aestronglyMeasurable
      hw)

/-- Outside a disc where `‖P‖ ≥ 1`, so that `h ≥ 1 / 2`, the modular `√(1 + w²) - 1` is at most
twice the potential term `h (exp (2w) - 1 - 2w)`. -/
private theorem setIntegral_compl_closedBall_le {R : ℝ}
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖P.eval z‖) {w : ℂ → ℝ} (hw : MemLp w 2)
    (hpint : Integrable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) :
    ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1) ≤
      2 * ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  rw [← integral_const_mul]
  calc ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1)
      ≤ ∫ z in (closedBall (0 : ℂ) R)ᶜ, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) := by
        refine setIntegral_mono_on (integrable_sqrt_one_add_sq_sub_one hw).integrableOn
          (hpint.const_mul 2).integrableOn measurableSet_closedBall.compl fun z hz ↦ ?_
        have h1 := hR z hz
        have hh : 1 / 2 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        have := Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (w z)
        have := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (w z)
        nlinarith
    _ ≤ ∫ z, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) :=
        setIntegral_le_integral (hpint.const_mul 2)
          (Eventually.of_forall fun z ↦ mul_nonneg zero_le_two (potential_nonneg P z _))

/-- The coercivity estimates on `H¹(ℂ)`, for corrections `u` with integrable potential: the energy
`M = ‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u)` satisfies `M ≤ 2 I(u) + C`, and
`‖u‖₂⁴ ≤ γ (1 + M)³`. -/
private theorem exists_coercivity (hm : 0 < P.natDegree) :
    ∃ C γ : ℝ, 0 ≤ γ ∧ ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 ≤
        2 * (‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
            (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
          ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
            (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) + C ∧
      (‖W1p.value u‖ ^ 2) ^ 2 ≤ γ * (1 + (‖W1p.gradient u‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16)) ^ 3 := by
  obtain ⟨C₀, hC₀, hpl⟩ := W1p.exists_norm_value_sq_le_of_finrank_eq_two (volume : Measure ℂ)
    Complex.finrank_real_complex
  -- A nonconstant polynomial has modulus at least one outside a closed disc.
  obtain ⟨R, -, hR⟩ := (hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp
    (by
      rw [cobounded_eq_cocompact]
      exact (P.tendsto_norm_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp hm)
        tendsto_norm_cocompact_atTop).eventually_ge_atTop 1 :
      ∀ᶠ z in Bornology.cobounded ℂ, 1 ≤ ‖P.eval z‖)
  set S := volume.real (closedBall (0 : ℂ) R)
  set γ := 8192 * (8 + 4 * C₀ ^ 2) + 2 * (8 + 4 * C₀ ^ 2) ^ 2 * S ^ 2
  have hc := memLp_coefficient hm
  set K := ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) ^ 2
  refine ⟨1 + 16 * (K ^ 2 * γ), γ, by positivity, fun u hpot ↦ ?_⟩
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  have hE : 0 ≤ E := integral_nonneg fun z ↦ potential_nonneg P z _
  -- The planar estimate with `s` the disc, where the modular is controlled by the potential.
  have hW2 := sq_le_of_le_planar hC₀ (norm_nonneg (W1p.gradient u)) hE (sq_nonneg _)
    (hpl u (closedBall (0 : ℂ) R) measurableSet_closedBall measure_closedBall_lt_top.ne)
    (setIntegral_compl_closedBall_le hR (memLp_value u) hpot)
  refine ⟨?_, hW2⟩
  -- The linear term: Cauchy–Schwarz against the square integrable coefficient.
  have hL := sq_integral_mul_le_integral_sq_mul_integral_sq hc (memLp_value u)
  rw [integral_value_sq] at hL
  exact le_two_mul_add_add_of_sq_le (by positivity) (by positivity) hL hW2

/-- On each sublevel set of `I`, the corrections `u` with integrable potential have bounded
`‖∇u‖₂²` and `‖u‖₂²`. -/
private theorem exists_norm_sq_le_of_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ D : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z ≤ t →
      ‖W1p.gradient u‖ ^ 2 ≤ D ∧ ‖W1p.value u‖ ^ 2 ≤ D := by
  obtain ⟨C, γ, hγ, hcoer⟩ := exists_coercivity hm
  set B := 2 * t + C
  refine ⟨max (2 * B) (1 + γ * (1 + B) ^ 3), fun u hpot ht ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hcoer u hpot
  set A := ‖W1p.gradient u‖ ^ 2
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  set W := ‖W1p.value u‖ ^ 2
  have hA : 0 ≤ A := by positivity
  have hE : 0 ≤ E := integral_nonneg fun z ↦ potential_nonneg P z _
  have hMB : A / 2 + E / 16 ≤ B := by simp only [B]; linarith
  refine ⟨le_max_of_le_left (by linarith), le_max_of_le_right ?_⟩
  have hW2 : W ^ 2 ≤ γ * (1 + B) ^ 3 :=
    h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 3) hγ)
  nlinarith [sq_nonneg (W - 1)]

private theorem norm_gradient_sq_eq {w : ℂ → ℝ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hg : W1p.gradient u =ᵐ[volume] ∇ w) :
    ‖W1p.gradient u‖ ^ 2 = ∫ z, ‖fderiv ℝ w z‖ ^ 2 := by
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [volume_restrict_top]
  exact integral_congr_ae (hg.mono fun z hz ↦ by simp only [hz, norm_gradient_eq_norm_fderiv])

private theorem norm_value_sq_eq {w : ℂ → ℝ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : W1p.value u =ᵐ[volume] w) : ‖W1p.value u‖ ^ 2 = ∫ z, w z ^ 2 := by
  rw [← integral_value_sq]
  exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- The potential and the linear term only see the value of a correction almost everywhere. -/
private theorem potential_linear_congr {w : ℂ → ℝ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : W1p.value u =ᵐ[volume] w) :
    (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) =ᵐ[volume]
      (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) ∧
    (fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) =ᵐ[volume]
      (fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * w z) :=
  ⟨hv.mono fun z hz ↦ by simp only [hz], hv.mono fun z hz ↦ by simp only [hz]⟩

/-! ### The functional on `H¹(ℂ)` -/

/-- **Taubes's functional is finite exactly when its potential term is integrable.** -/
theorem sobolevReducedFunctional_ne_top_iff {u : W1p (volume : Measure ℂ) ⊤ 2} :
    sobolevReducedFunctional P u ≠ ⊤ ↔
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) := by
  have hnn : 0 ≤ᵐ[volume] fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
    Eventually.of_forall fun z ↦ potential_nonneg P z _
  rw [Integrable, hasFiniteIntegral_iff_ofReal hnn, sobolevReducedFunctional_def,
    and_iff_right (aestronglyMeasurable_potential (memLp_value u).aestronglyMeasurable),
    lt_top_iff_ne_top]
  constructor
  · intro h htop
    rw [htop, ENNReal.top_div_of_ne_top (by norm_num), EReal.coe_ennreal_top,
      EReal.coe_add_top] at h
    exact h rfl
  · intro h
    rw [← EReal.coe_ennreal_toReal (ENNReal.div_ne_top h (by norm_num)), ← EReal.coe_add]
    exact EReal.coe_ne_top _

/-- When its potential term is integrable, Taubes's functional on `H¹(ℂ)` is the real number

`‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u`. -/
theorem sobolevReducedFunctional_eq_coe {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hpot : Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) :
    sobolevReducedFunctional P u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) := by
  have hE : 0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
    integral_nonneg fun z ↦ potential_nonneg P z _
  rw [sobolevReducedFunctional_def, ← ofReal_integral_eq_lintegral_ofReal hpot
    (Eventually.of_forall fun z ↦ potential_nonneg P z _), ← ENNReal.ofReal_ofNat 16,
    ← ENNReal.ofReal_div_of_pos (by norm_num), EReal.coe_ennreal_ofReal,
    max_eq_left (div_nonneg hE (by norm_num)), ← EReal.coe_add]
  congr 1
  ring

/-- **Agreement with `TauCeti.Vortex.reducedFunctional`.** If the value of `u ∈ H¹(ℂ)` is a
compactly supported `C¹` function `w` and its weak gradient is `∇w`, both almost everywhere, then
Taubes's functional takes the same value at `u` and at `w`. -/
theorem sobolevReducedFunctional_eq_reducedFunctional {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : W1p.value u =ᵐ[volume] w) (hg : W1p.gradient u =ᵐ[volume] ∇ w) :
    sobolevReducedFunctional P u = reducedFunctional P w := by
  obtain ⟨hpot, hlin⟩ := potential_linear_congr (P := P) hv
  rw [sobolevReducedFunctional_eq_coe
      ((integrable_mul_exp_sub_one_sub P hw.continuous hws).congr hpot.symm),
    reducedFunctional_def, norm_gradient_sq_eq hg, integral_congr_ae hpot,
    integral_congr_ae hlin]

/-- Taubes's functional vanishes at the zero correction. -/
@[simp]
theorem sobolevReducedFunctional_zero (P : Polynomial ℂ) : sobolevReducedFunctional P 0 = 0 := by
  have hv : W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) =ᵐ[volume] (0 : ℂ → ℝ) := by
    rw [← W1p.valueL_apply, map_zero]
    simpa only [volume_restrict_top] using
      Lp.coeFn_zero ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))
  have hg : W1p.gradient (0 : W1p (volume : Measure ℂ) ⊤ 2) = 0 := by
    rw [← W1p.gradientL_apply, map_zero]
  obtain ⟨hpot, hlin⟩ := potential_linear_congr (P := P) hv
  rw [sobolevReducedFunctional_eq_coe ((integrable_zero _ _ _).congr (hpot.trans
      (Eventually.of_forall fun z ↦ by simp)).symm), integral_congr_ae hpot,
    integral_congr_ae hlin, hg]
  simp

/-! ### Coercivity -/

/-- **Coercivity of Taubes's functional.** For a complex polynomial `P` of degree at least one
there is a constant `C` such that every compactly supported `C¹` function `w` satisfies

`∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) ≤ 2 I(w) + C`,

where `I` is `TauCeti.Vortex.reducedFunctional P` and `h = ‖P‖² / (1 + ‖P‖²)`. -/
theorem exists_le_two_mul_reducedFunctional_add (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
          (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 ≤
        2 * reducedFunctional P w + C := by
  obtain ⟨C, _, _, hcoer⟩ := exists_coercivity hm
  refine ⟨C, fun w hw hws ↦ ?_⟩
  obtain ⟨u, hv, hg, -, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasCompactSupport
    (mu := (volume : Measure ℂ)) (p := 2) hw hws
  obtain ⟨hpot, hlin⟩ := potential_linear_congr (P := P) hv
  have h := (hcoer u ((integrable_mul_exp_sub_one_sub P hw.continuous hws).congr hpot.symm)).1
  rwa [norm_gradient_sq_eq hg, integral_congr_ae hpot, integral_congr_ae hlin,
    ← reducedFunctional_def] at h

/-- Taubes's functional is bounded below on compactly supported `C¹` functions. -/
theorem exists_le_reducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → C ≤ reducedFunctional P w := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_reducedFunctional_add hm
  refine ⟨-C / 2, fun w hw hws ↦ ?_⟩
  have hA : 0 ≤ ∫ z, ‖fderiv ℝ w z‖ ^ 2 := integral_nonneg fun z ↦ by positivity
  have hE : 0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    integral_nonneg fun z ↦ potential_nonneg P z _
  linarith [hC w hw hws]

/-- **Bounded sublevel sets.** For a complex polynomial `P` of degree at least one and every
level `t`, the compactly supported `C¹` functions `w` with `I(w) ≤ t` have uniformly bounded
Dirichlet energy `∫ ‖Dw‖²` and `L²` norm `∫ w²`; here `I` is
`TauCeti.Vortex.reducedFunctional P`. -/
theorem exists_integral_le_of_reducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → reducedFunctional P w ≤ t →
      ∫ z, ‖fderiv ℝ w z‖ ^ 2 ≤ C ∧ ∫ z, w z ^ 2 ≤ C := by
  obtain ⟨D, hD⟩ := exists_norm_sq_le_of_le hm t
  refine ⟨D, fun w hw hws ht ↦ ?_⟩
  obtain ⟨u, hv, hg, -, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasCompactSupport
    (mu := (volume : Measure ℂ)) (p := 2) hw hws
  obtain ⟨hpot, hlin⟩ := potential_linear_congr (P := P) hv
  have h := hD u ((integrable_mul_exp_sub_one_sub P hw.continuous hws).congr hpot.symm)
  rw [norm_gradient_sq_eq hg, norm_value_sq_eq hv, integral_congr_ae hpot,
    integral_congr_ae hlin, ← reducedFunctional_def] at h
  exact h ht

/-- **Taubes's functional is bounded below on `H¹(ℂ)`**, for a complex polynomial `P` of degree
at least one. -/
theorem exists_le_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2, (C : EReal) ≤ sobolevReducedFunctional P u := by
  obtain ⟨C, _, _, hcoer⟩ := exists_coercivity hm
  refine ⟨-C / 2, fun u ↦ ?_⟩
  by_cases htop : sobolevReducedFunctional P u = ⊤
  · rw [htop]
    exact le_top
  have hpot := sobolevReducedFunctional_ne_top_iff.1 htop
  rw [sobolevReducedFunctional_eq_coe hpot, EReal.coe_le_coe_iff]
  have hA : 0 ≤ ‖W1p.gradient u‖ ^ 2 := by positivity
  have hE : 0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
    integral_nonneg fun z ↦ potential_nonneg P z _
  linarith [(hcoer u hpot).1]

/-- **Bounded sublevel sets on `H¹(ℂ)`.** For a complex polynomial `P` of degree at least one
and every level `t`, the corrections `u ∈ H¹(ℂ)` with `I(u) ≤ t` lie in a fixed ball; here `I` is
`TauCeti.Vortex.sobolevReducedFunctional P`. -/
theorem exists_norm_le_of_sobolevReducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ R : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2, sobolevReducedFunctional P u ≤ t → ‖u‖ ≤ R := by
  obtain ⟨D, hD⟩ := exists_norm_sq_le_of_le hm t
  refine ⟨1 + 2 * D, fun u ht ↦ ?_⟩
  have hpot := sobolevReducedFunctional_ne_top_iff.1 (ne_top_of_le_ne_top (EReal.coe_ne_top t) ht)
  rw [sobolevReducedFunctional_eq_coe hpot, EReal.coe_le_coe_iff] at ht
  obtain ⟨hg, hv⟩ := hD u hpot ht
  have hu := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  nlinarith [sq_nonneg (‖u‖ - 1), norm_nonneg u]

/-! ### Existence of a minimizer -/

/-- The linear term of Taubes's functional is a continuous linear functional on `H¹(ℂ)`: the `L²`
pairing of the value with the square integrable coefficient. -/
private theorem exists_continuousLinearMap_eq_integral (hm : 0 < P.natDegree) :
    ∃ ℓ : W1p (volume : Measure ℂ) ⊤ 2 →L[ℝ] ℝ, ∀ u, ℓ u =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := by
  have hc := memLp_coefficient hm
  rw [← volume_restrict_top] at hc
  refine ⟨(innerSL ℝ (hc.toLp _)).comp W1p.valueL, fun u ↦ ?_⟩
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply,
    L2.inner_def, volume_restrict_top]
  have h := hc.coeFn_toLp
  simp only [volume_restrict_top] at h
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  simp [hz, mul_comm]

/-- **Weak lower semicontinuity.** For a complex polynomial `P` of degree at least one, Taubes's
functional is lower semicontinuous on `H¹(ℂ)` with its weak topology. -/
theorem lowerSemicontinuous_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    LowerSemicontinuous fun u : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) ↦
      sobolevReducedFunctional P ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm u) := by
  obtain ⟨ℓ, hℓ⟩ := exists_continuousLinearMap_eq_integral (P := P) hm
  -- The quadratic and linear terms form a convex continuous function, hence weakly lower
  -- semicontinuous.
  have hconv : ConvexOn ℝ univ fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦
      ‖W1p.gradient u‖ ^ 2 / 2 + ℓ u := by
    have hsq := ((convexOn_univ_norm.pow (fun x _ ↦ norm_nonneg x) 2).comp_linearMap
      (W1p.gradientL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).toLinearMap).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [preimage_univ] at hsq
    convert hsq.add (ℓ.toLinearMap.convexOn convex_univ) using 1
    funext u
    simp only [Pi.pow_apply, Function.comp_apply, ContinuousLinearMap.coe_coe,
      W1p.gradientL_apply, smul_eq_mul, Pi.add_apply]
    ring
  have hcont : Continuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦
      ‖W1p.gradient u‖ ^ 2 / 2 + ℓ u := by
    have hg : Continuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦ W1p.gradient u :=
      (W1p.gradientL (mu := (volume : Measure ℂ))).continuous.congr W1p.gradientL_apply
    fun_prop
  have h₁ := continuous_coe_real_ereal.comp_lowerSemicontinuous
    (hconv.quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := ℝ)
      hcont.lowerSemicontinuous) EReal.coe_strictMono.monotone
  -- The potential term is weakly lower semicontinuous, through the weakly continuous value map.
  have h₂ := (continuous_coe_ennreal_ereal.comp
      (ENNReal.continuous_div_const 16 (by norm_num))).comp_lowerSemicontinuous
    ((lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P
      ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))).comp
      (WeakSpace.map (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous)
    fun a b hab ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 (ENNReal.div_le_div_right hab 16)
  convert h₁.add' h₂ fun u ↦ EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
    (Or.inl (EReal.coe_ne_bot _)) using 1
  funext u
  obtain ⟨v, rfl⟩ := (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).surjective u
  have hmap : (toWeakSpace ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)))).symm
      (WeakSpace.map W1p.valueL (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) v)) =
        W1p.value v := by
    -- `toWeakSpace` and `WeakSpace.map` are the identity and `W1p.valueL` on the underlying
    -- spaces, and no lemma states their composite.
    rw [← W1p.valueL_apply]
    rfl
  simp only [Function.comp_apply, hℓ, volume_restrict_top, sobolevReducedFunctional_def,
    LinearEquiv.symm_apply_apply, hmap]

/-- **Existence of a minimizer of Taubes's functional.** For a complex polynomial `P` of degree
at least one, Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P` attains its minimum
on `H¹(ℂ)`. Since `I(0) = 0` (`TauCeti.Vortex.sobolevReducedFunctional_zero`), the minimum value
is at most `0`; it is finite by `TauCeti.Vortex.exists_le_sobolevReducedFunctional`. -/
theorem exists_isMinOn_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2, IsMinOn (sobolevReducedFunctional P) univ u := by
  set e := toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)
  obtain ⟨R, hR⟩ := exists_norm_le_of_sobolevReducedFunctional_le hm 0
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (by simp))
  -- Closed balls of the Hilbert space `H¹(ℂ)` are weakly compact.
  have hK : IsCompact (e '' closedBall 0 R) :=
    isCompact_toWeakSpace_closedBall surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 R
  obtain ⟨a, ⟨u, -, rfl⟩, hmin⟩ := ((lowerSemicontinuous_sobolevReducedFunctional hm
    ).lowerSemicontinuousOn (e '' closedBall 0 R)).exists_isMinOn
      ⟨e 0, mem_image_of_mem e (mem_closedBall_self hR0)⟩ hK
  rw [isMinOn_iff] at hmin
  have hmin' (v : W1p (volume : Measure ℂ) ⊤ 2) (hv : ‖v‖ ≤ R) :
      sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
    simpa only [e, LinearEquiv.symm_apply_apply] using
      hmin (e v) (mem_image_of_mem e (mem_closedBall_zero_iff.2 hv))
  refine ⟨u, isMinOn_iff.2 fun v _ ↦ ?_⟩
  by_cases hv : ‖v‖ ≤ R
  · exact hmin' v hv
  -- Outside the ball the functional is positive, while its minimum on the ball is at most `0`.
  have h0 := hmin' 0 (by simpa using hR0)
  rw [sobolevReducedFunctional_zero] at h0
  exact h0.trans (not_le.1 fun h ↦ hv (hR v (by simpa using h))).le

end TauCeti.Vortex
