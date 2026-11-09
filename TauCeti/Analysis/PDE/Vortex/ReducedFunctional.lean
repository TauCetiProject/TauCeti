/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.AtInfinity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
public import TauCeti.Analysis.Sobolev.Poincare.Planar
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.MeasureTheory.Function.Lp.SqrtOneAddSq
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Topology.Semicontinuity.Basic

/-!
# Taubes's functional for the prescribed-zero vortex problem: coercivity and a minimizer

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

The difficulty is coercivity. The middle term grows exponentially for positive `w` but only
linearly for negative `w`, and `h` vanishes at the zeros of `P`, so it does not control `∫ w²`
directly. Outside a disc, where `h ≥ 1 / 2`, it bounds `∫ (√(1 + w²) - 1)`, and the planar
estimate `TauCeti.exists_integral_sq_le_of_finrank_eq_two` then bounds `∫ w²` by a constant times
the power `3 / 2` of one plus the energy `∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w)`. Since
the linear term is at most the square root of `∫ w²` times a constant, it is dominated by the
energy. This gives, for every compactly supported `C¹` function `w`:

* `TauCeti.Vortex.exists_le_two_mul_reducedFunctional_add`: the energy is at most `2 I(w) + C`;
* `TauCeti.Vortex.exists_le_reducedFunctional`: `I` is bounded below;
* `TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`: on each sublevel set of `I`,
  `∫ ‖Dw‖²` and `∫ w²` are bounded, with a constant independent of `w`.

The direct method runs on `W^{1,2}(ℂ)`. There `I` is `TauCeti.Vortex.sobolevReducedFunctional`,
built from the value and the weak gradient, and it agrees with `reducedFunctional` on test
functions (`TauCeti.Vortex.sobolevReducedFunctional_ofTestFunctionₗ`). Its potential is a Bochner
integral, so the statements concern the functions whose potential `h (exp (2w) - 1 - 2w)` is
integrable. The planar estimate extends to `W^{1,2}(ℂ)` by density
(`TauCeti.W1p.exists_integral_value_sq_le_of_finrank_eq_two`), and with it the coercivity:

* `TauCeti.Vortex.exists_le_two_mul_sobolevReducedFunctional_add`: the energy is at most
  `2 I(u) + C`;
* `TauCeti.Vortex.exists_le_sobolevReducedFunctional`: `I` is bounded below;
* `TauCeti.Vortex.exists_norm_le_of_sobolevReducedFunctional_le`: each sublevel set of `I` is
  bounded in the Sobolev norm.

The sublevel sets are also convex, because the energy is convex and the last term linear, and
closed, because the potential is lower semicontinuous
(`TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub`). In the Hilbert space
`W^{1,2}(ℂ)` they are therefore weakly compact, and `I` attains its infimum
(`TauCeti.Vortex.exists_isMinOn_sobolevReducedFunctional`). The Euler–Lagrange equation and the
regularity of the minimizer, which would make it a solution of the reduced equation, are not
treated here.

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

/-! ### Coercivity -/

variable {P : Polynomial ℂ}

/-- For a compactly supported continuous `w`, the potential term `h (exp (2w) - 1 - 2w)` is
integrable. -/
private theorem integrable_potential {w : ℂ → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) : Integrable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  have hP := P.continuous
  have hc : Continuous fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    ((hP.norm.pow 2).div (continuous_const.add (hP.norm.pow 2))
      fun z ↦ (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne').mul
      (by fun_prop)
  exact hc.integrable_of_hasCompactSupport (hws.mono fun z hz h0 ↦ hz (by simp [h0]))

/-- The potential integral `∫ h (exp (2w) - 1 - 2w)` is nonnegative. -/
private theorem integral_potential_nonneg (w : ℂ → ℝ) :
    0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
  integral_nonneg fun z ↦
    mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)

/-- The energy `∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w)` is nonnegative. -/
private theorem energy_nonneg (w : ℂ → ℝ) :
    0 ≤ (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
      (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 := by
  have hA : 0 ≤ ∫ z, ‖fderiv ℝ w z‖ ^ 2 := integral_nonneg fun z ↦ by positivity
  have hE := integral_potential_nonneg (P := P) w
  positivity

/-- Outside a disc where `‖P‖ ≥ 1`, so that `h ≥ 1 / 2`, the modular `√(1 + w²) - 1` is at most
twice the potential term `h (exp (2w) - 1 - 2w)`. -/
private theorem setIntegral_compl_closedBall_le {R : ℝ}
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖P.eval z‖) {w : ℂ → ℝ}
    (hpint : Integrable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z))
    (hmod : Integrable fun z ↦ √(1 + w z ^ 2) - 1) :
    ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1) ≤
      2 * ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  have hpot (z : ℂ) :
      0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)
  rw [← integral_const_mul]
  calc ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1)
      ≤ ∫ z in (closedBall (0 : ℂ) R)ᶜ, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) := by
        refine setIntegral_mono_on hmod.integrableOn (hpint.const_mul 2).integrableOn
          measurableSet_closedBall.compl fun z hz ↦ ?_
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
          (Eventually.of_forall fun z ↦ mul_nonneg zero_le_two (hpot z))

/-- The algebra behind the bound on `∫ w²`. With `k = 2 + C₀ √A`, the planar estimate
`W ≤ 2 k (2 E) + k² S`, in which the modular has already been bounded by twice the potential `E`,
gives `W² ≤ γ (1 + M)³` for the energy `M = A / 2 + E / 16`. -/
private theorem sq_le_of_le_two_mul_mul_add {A E W S C₀ : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hW : 0 ≤ W) (hC₀ : 0 ≤ C₀)
    (h : W ≤ 2 * (2 + C₀ * √A) * (2 * E) + (2 + C₀ * √A) ^ 2 * S) :
    W ^ 2 ≤ (8192 * (8 + 4 * C₀ ^ 2) + 2 * (8 + 4 * C₀ ^ 2) ^ 2 * S ^ 2) *
      (1 + (A / 2 + E / 16)) ^ 3 := by
  set M := A / 2 + E / 16
  set k := 2 + C₀ * √A
  have hk : 0 ≤ k := by positivity
  have hW1 : W ≤ 64 * k * M + k ^ 2 * S := by
    have : E ≤ 16 * M := by simp only [M]; linarith
    nlinarith
  -- `k² ≤ 8 + 2 C₀² A ≤ (8 + 4 C₀²) (1 + M)`.
  have hk2 : k ^ 2 ≤ (8 + 4 * C₀ ^ 2) * (1 + M) := by
    have hsA : √A ^ 2 = A := Real.sq_sqrt hA
    have : k ^ 2 ≤ 8 + 2 * C₀ ^ 2 * A := by
      simp only [k]
      nlinarith [sq_nonneg (2 - C₀ * √A)]
    have : A ≤ 2 * M := by simp only [M]; linarith
    nlinarith [sq_nonneg C₀]
  exact sq_le_mul_one_add_pow_three hW (by positivity) (by positivity) hW1 hk2

/-- The algebra of coercivity: if the linear term `L` satisfies `L² ≤ K W` and
`W² ≤ γ (1 + M)³`, then `M ≤ 2 (M + L) + 1 + 16 K² γ`. -/
private theorem le_two_mul_add_add_of_sq_le {M L W K γ : ℝ} (hM : 0 ≤ M) (hγ : 0 ≤ γ)
    (hL : L ^ 2 ≤ K * W) (hW : W ^ 2 ≤ γ * (1 + M) ^ 3) :
    M ≤ 2 * (M + L) + (1 + 16 * (K ^ 2 * γ)) := by
  have hx4 : |L| ^ 4 ≤ K ^ 2 * γ * (1 + M) ^ 3 := by
    calc |L| ^ 4 = (L ^ 2) ^ 2 := by rw [← sq_abs L]; ring
      _ ≤ (K * W) ^ 2 := pow_le_pow_left₀ (sq_nonneg L) hL 2
      _ = K ^ 2 * W ^ 2 := by ring
      _ ≤ K ^ 2 * (γ * (1 + M) ^ 3) := by gcongr
      _ = K ^ 2 * γ * (1 + M) ^ 3 := by ring
  have := le_div_two_add_of_pow_four_le (by positivity) hM hx4
  linarith [neg_abs_le L]

/-- The coefficient `g - (1 + ‖P‖²)⁻¹ / 8` of the linear term of Taubes's functional is square
integrable. -/
private theorem memLp_linearCoeff (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) 2 := by
  have h1 := (P.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).const_mul 2
  have h2 := (Polynomial.memLp_inv_one_add_norm_eval_sq hm).const_mul (1 / 8 : ℝ)
  convert h1.sub h2 using 1
  funext z
  simp only [Pi.sub_apply]
  ring

/-- The energy `∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w)` controls `∫ w²`:
its square is at most a constant times the cube of one plus the energy. -/
private theorem exists_sq_integral_sq_le (hm : 0 < P.natDegree) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ z, w z ^ 2) ^ 2 ≤ γ * (1 + ((∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) / 16)) ^ 3 := by
  obtain ⟨C₀, hC₀, hpl⟩ :=
    exists_integral_sq_le_of_finrank_eq_two (volume : Measure ℂ) Complex.finrank_real_complex
  obtain ⟨R, hR⟩ := P.exists_forall_notMem_closedBall_le_norm_eval hm 1
  refine ⟨8192 * (8 + 4 * C₀ ^ 2) + 2 * (8 + 4 * C₀ ^ 2) ^ 2 *
    volume.real (closedBall (0 : ℂ) R) ^ 2, by positivity, fun w hw hws ↦ ?_⟩
  have hmod : Integrable fun z ↦ √(1 + w z ^ 2) - 1 :=
    (by fun_prop : Continuous fun z ↦ √(1 + w z ^ 2) - 1).integrable_of_hasCompactSupport
      (hws.mono fun z hz h0 ↦ hz (by simp [h0]))
  refine sq_le_of_le_two_mul_mul_add (A := ∫ z, ‖fderiv ℝ w z‖ ^ 2)
    (integral_nonneg fun z ↦ by positivity) (integral_potential_nonneg w)
    (integral_nonneg fun z ↦ sq_nonneg _) hC₀
    ((hpl w hw hws (closedBall (0 : ℂ) R) measurableSet_closedBall
      measure_closedBall_lt_top.ne).trans ?_)
  gcongr
  exact setIntegral_compl_closedBall_le hR (integrable_potential hw.continuous hws) hmod

/-- **Coercivity of Taubes's functional.** For a complex polynomial `P` of degree at least one
there is a constant `C` such that every compactly supported `C¹` function `w` satisfies

`∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) ≤ 2 I(w) + C`,

where `I` is `TauCeti.Vortex.reducedFunctional P` and `h = ‖P‖² / (1 + ‖P‖²)`. -/
theorem exists_le_two_mul_reducedFunctional_add (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
          (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) / 16 ≤
        2 * reducedFunctional P w + C := by
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_integral_sq_le hm
  have hc := memLp_linearCoeff hm
  refine ⟨1 + 16 * ((∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) ^ 2) ^ 2 * γ), fun w hw hws ↦ ?_⟩
  have h := le_two_mul_add_add_of_sq_le (energy_nonneg w) hγ
    (sq_integral_mul_le_integral_sq_mul_integral_sq hc
      (hw.continuous.memLp_of_hasCompactSupport hws)) (hsq w hw hws)
  rw [reducedFunctional_def]
  linarith

/-- Taubes's functional is bounded below on compactly supported `C¹` functions. -/
theorem exists_le_reducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → C ≤ reducedFunctional P w := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_reducedFunctional_add hm
  refine ⟨-C / 2, fun w hw hws ↦ ?_⟩
  linarith [hC w hw hws, energy_nonneg (P := P) w]

/-- **Bounded sublevel sets.** For a complex polynomial `P` of degree at least one and every
level `t`, the compactly supported `C¹` functions `w` with `I(w) ≤ t` have uniformly bounded
Dirichlet energy `∫ ‖Dw‖²` and `L²` norm `∫ w²`; here `I` is
`TauCeti.Vortex.reducedFunctional P`. -/
theorem exists_integral_le_of_reducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → reducedFunctional P w ≤ t →
      ∫ z, ‖fderiv ℝ w z‖ ^ 2 ≤ C ∧ ∫ z, w z ^ 2 ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_le_two_mul_reducedFunctional_add hm
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_integral_sq_le hm
  set B := 2 * t + C₁
  refine ⟨max (2 * B) (1 + γ * (1 + B) ^ 3), fun w hw hws ht ↦ ?_⟩
  set A := ∫ z, ‖fderiv ℝ w z‖ ^ 2
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)
  set W := ∫ z, w z ^ 2
  have hA : 0 ≤ A := integral_nonneg fun z ↦ by positivity
  have hE : 0 ≤ E := integral_potential_nonneg w
  have hMB : A / 2 + E / 16 ≤ B := by
    have := hC₁ w hw hws
    simp only [B]
    linarith
  refine ⟨le_max_of_le_left (by linarith), le_max_of_le_right ?_⟩
  have hW2 : W ^ 2 ≤ γ * (1 + B) ^ 3 := by
    refine (hsq w hw hws).trans (mul_le_mul_of_nonneg_left ?_ hγ)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  nlinarith [sq_nonneg (W - 1)]

/-! ### Taubes's functional on `W^{1,2}(ℂ)` -/

section Sobolev

open TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace

/-- **Taubes's functional on `W^{1,2}(ℂ)`.** For `u ∈ W^{1,2}(ℂ)` with value `w` and weak gradient
`∇w`,

`I(u) = ‖∇w‖₂² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) w`,

with `h` and `g` as in `TauCeti.Vortex.reducedFunctional`, which it extends from test functions
(`TauCeti.Vortex.sobolevReducedFunctional_ofTestFunctionₗ`). The potential is a Bochner
integral, so the value is meaningful only when `h (exp (2w) - 1 - 2w)` is integrable, and the
statements below assume this. -/
def sobolevReducedFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : ℝ :=
  ‖W1p.gradient u‖ ^ 2 / 2 +
    (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
    ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z

/-- The defining formula of Taubes's functional on `W^{1,2}(ℂ)`. -/
theorem sobolevReducedFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      ‖W1p.gradient u‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := (rfl)

/-- The value of `u ∈ W^{1,2}(ℂ)` is square integrable on `ℂ`. -/
private theorem memLp_value (u : W1p (volume : Measure ℂ) ⊤ 2) : MemLp (W1p.value u) 2 :=
  (Lp.memLp (W1p.value u)).mono_measure Measure.restrict_univ.ge

private theorem integral_value_sq (u : W1p (volume : Measure ℂ) ⊤ 2) :
    ∫ z, W1p.value u z ^ 2 = ‖W1p.value u‖ ^ 2 := by
  rw [← W1p.integral_value_sq_eq_norm_value_sq]
  simp only [Opens.coe_top, Measure.restrict_univ]

/-- On a test function `φ`, Taubes's functional on `W^{1,2}(ℂ)` is `reducedFunctional P φ`. -/
theorem sobolevReducedFunctional_ofTestFunctionₗ (P : Polynomial ℂ) (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    sobolevReducedFunctional P (W1p.ofTestFunctionₗ volume ⊤ 2 φ) = reducedFunctional P φ := by
  have hval : (W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) : ℂ → ℝ) =ᵐ[volume] φ :=
    (W1p.value_ofTestFunctionₗ_ae φ).filter_mono (ae_mono Measure.restrict_univ.ge)
  have h1 : ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z) - 1 -
          2 * W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z) =
      ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * φ z) - 1 - 2 * φ z) :=
    integral_congr_ae (by filter_upwards [hval] with z hz; rw [hz])
  have h2 : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * φ z :=
    integral_congr_ae (by filter_upwards [hval] with z hz; rw [hz])
  rw [sobolevReducedFunctional_def, reducedFunctional_def, W1p.norm_gradient_ofTestFunctionₗ_sq,
    h1, h2]

/-- The energy `‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u)` controls `∫ u²` on `W^{1,2}(ℂ)`:
its square is at most a constant times the cube of one plus the energy. -/
private theorem exists_sq_integral_value_sq_le (hm : 0 < P.natDegree) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      (∫ z, W1p.value u z ^ 2) ^ 2 ≤ γ * (1 + (‖W1p.gradient u‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16)) ^ 3 := by
  obtain ⟨C₀, hC₀, hpl⟩ := W1p.exists_integral_value_sq_le_of_finrank_eq_two
    (μ := (volume : Measure ℂ)) Complex.finrank_real_complex
  obtain ⟨R, hR⟩ := P.exists_forall_notMem_closedBall_le_norm_eval hm 1
  refine ⟨8192 * (8 + 4 * C₀ ^ 2) + 2 * (8 + 4 * C₀ ^ 2) ^ 2 *
    volume.real (closedBall (0 : ℂ) R) ^ 2, by positivity, fun u hu ↦ ?_⟩
  refine sq_le_of_le_two_mul_mul_add (A := ‖W1p.gradient u‖ ^ 2) (by positivity)
    (integral_potential_nonneg _) (integral_nonneg fun z ↦ sq_nonneg _) hC₀ ?_
  rw [Real.sqrt_sq (norm_nonneg _)]
  refine (hpl u (closedBall (0 : ℂ) R) measurableSet_closedBall
    measure_closedBall_lt_top.ne).trans ?_
  gcongr
  exact setIntegral_compl_closedBall_le hR hu (memLp_value u).integrable_sqrt_one_add_sq_sub_one

/-- **Coercivity of Taubes's functional on `W^{1,2}(ℂ)`.** For a complex polynomial `P` of degree
at least one there is a constant `C` such that every `u ∈ W^{1,2}(ℂ)` with integrable potential
`h (exp (2u) - 1 - 2u)` satisfies

`‖∇u‖₂² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) ≤ 2 I(u) + C`,

where `I` is `TauCeti.Vortex.sobolevReducedFunctional P`. -/
theorem exists_le_two_mul_sobolevReducedFunctional_add (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      ‖W1p.gradient u‖ ^ 2 / 2 +
          (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
            (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 ≤
        2 * sobolevReducedFunctional P u + C := by
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_integral_value_sq_le hm
  have hc := memLp_linearCoeff hm
  refine ⟨1 + 16 * ((∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) ^ 2) ^ 2 * γ), fun u hu ↦ ?_⟩
  have hE := integral_potential_nonneg (P := P) (W1p.value u)
  have h := le_two_mul_add_add_of_sq_le (by positivity) hγ
    (sq_integral_mul_le_integral_sq_mul_integral_sq hc (memLp_value u)) (hsq u hu)
  rw [sobolevReducedFunctional_def]
  linarith

/-- Taubes's functional is bounded below on the functions of `W^{1,2}(ℂ)` with integrable
potential. -/
theorem exists_le_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    ∃ C : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      C ≤ sobolevReducedFunctional P u := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_sobolevReducedFunctional_add hm
  refine ⟨-C / 2, fun u hu ↦ ?_⟩
  have hE := integral_potential_nonneg (P := P) (W1p.value u)
  linarith [hC u hu, sq_nonneg ‖W1p.gradient u‖]

/-- **Bounded sublevel sets in `W^{1,2}(ℂ)`.** For a complex polynomial `P` of degree at least one
and every level `t`, the functions `u ∈ W^{1,2}(ℂ)` with integrable potential and `I(u) ≤ t` are
uniformly bounded in the Sobolev norm; here `I` is `TauCeti.Vortex.sobolevReducedFunctional P`. -/
theorem exists_norm_le_of_sobolevReducedFunctional_le (hm : 0 < P.natDegree) (t : ℝ) :
    ∃ R : ℝ, ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) →
      sobolevReducedFunctional P u ≤ t → ‖u‖ ≤ R := by
  obtain ⟨C, hC⟩ := exists_le_two_mul_sobolevReducedFunctional_add hm
  obtain ⟨γ, hγ, hsq⟩ := exists_sq_integral_value_sq_le hm
  set B := 2 * t + C
  refine ⟨√(2 * B + (1 + γ * (1 + B) ^ 3)), fun u hu ht ↦ ?_⟩
  have hE := integral_potential_nonneg (P := P) (W1p.value u)
  have hA := sq_nonneg ‖W1p.gradient u‖
  have hMB := hC u hu
  have hW2 : (∫ z, W1p.value u z ^ 2) ^ 2 ≤ γ * (1 + B) ^ 3 :=
    (hsq u hu).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by simp only [B]; linarith) 3) hγ)
  have hW : ∫ z, W1p.value u z ^ 2 ≤ 1 + γ * (1 + B) ^ 3 := by
    nlinarith [sq_nonneg (∫ z, W1p.value u z ^ 2 - 1)]
  rw [← Real.sqrt_sq (norm_nonneg u), W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← integral_value_sq]
  exact Real.sqrt_le_sqrt (by simp only [B] at *; linarith)

/-! ### Existence of a minimizer -/

/-- The potential `∫ h (exp (2u) - 1 - 2u)`, as an extended integral, is lower semicontinuous on
`W^{1,2}(ℂ)`. -/
private theorem lowerSemicontinuous_lintegral_potential (P : Polynomial ℂ) :
    LowerSemicontinuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦
      ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) := by
  have h := (lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P
    ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))).comp
      ((toWeakSpaceCLM ℝ _).continuous.comp
        (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).continuous)
  simp only [Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace, LinearEquiv.symm_apply_apply,
    W1p.valueL_apply] at h
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

/-- The potential `h (exp (2u) - 1 - 2u)` of `u ∈ W^{1,2}(ℂ)` is almost everywhere strongly
measurable. -/
private theorem aestronglyMeasurable_potential (P : Polynomial ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    AEStronglyMeasurable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
  have hv := (memLp_value u).aestronglyMeasurable.aemeasurable
  have hh : Measurable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    have := P.continuous.measurable
    fun_prop
  exact (hh.aemeasurable.mul (((hv.const_mul 2).exp.sub_const 1).sub
    (hv.const_mul 2))).aestronglyMeasurable

/-- The linear term of Taubes's functional is an `L²` pairing with the value. -/
private theorem integral_mul_value_eq_inner {c : ℂ → ℝ} (hc : MemLp c 2)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    ∫ z, c z * W1p.value u z = ⟪(hc.restrict _).toLp c, W1p.value u⟫_ℝ := by
  rw [L2.inner_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [(hc.restrict ((⊤ : Opens ℂ) : Set ℂ)).coeFn_toLp.filter_mono
    (ae_mono Measure.restrict_univ.ge)] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

/-- The sublevel sets of Taubes's functional on `W^{1,2}(ℂ)`, among the functions with integrable
potential, are convex: the Dirichlet energy and the potential are convex and the last term is
linear. -/
private theorem convex_sublevel (hm : 0 < P.natDegree) (t : ℝ) :
    Convex ℝ {u : W1p (volume : Measure ℂ) ⊤ 2 |
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ∧
      sobolevReducedFunctional P u ≤ t} := by
  have hc := memLp_linearCoeff hm
  intro u hu v hv a b ha hb hab
  have hval : (W1p.value (a • u + b • v) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ a * W1p.value u z + b * W1p.value v z := by
    filter_upwards
      [(W1p.value_add_ae (a • u) (b • v)).filter_mono (ae_mono Measure.restrict_univ.ge),
      (W1p.value_smul_ae a u).filter_mono (ae_mono Measure.restrict_univ.ge),
      (W1p.value_smul_ae b v).filter_mono (ae_mono Measure.restrict_univ.ge)] with z hz1 hz2 hz3
    rw [hz1, Pi.add_apply, hz2, hz3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  -- The potential is convex pointwise.
  have hpt : ∀ᵐ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value (a • u + b • v) z) - 1 - 2 * W1p.value (a • u + b • v) z) ≤
      a * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) +
      b * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) := by
    filter_upwards [hval] with z hz
    rw [hz]
    have hΦ := Real.convexOn_exp_two_mul_sub_one_sub_two_mul.2 (mem_univ (W1p.value u z))
      (mem_univ (W1p.value v z)) ha hb hab
    simp only [smul_eq_mul] at hΦ
    have hh : 0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hΦ hh]
  have hsum := (hu.1.const_mul a).add (hv.1.const_mul b)
  have hint : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value (a • u + b • v) z) - 1 - 2 * W1p.value (a • u + b • v) z) := by
    refine hsum.mono' (aestronglyMeasurable_potential P _) ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _))]
    exact hz
  refine ⟨hint, ?_⟩
  have hE := integral_mono_ae hint hsum hpt
  rw [integral_add' (hu.1.const_mul a) (hv.1.const_mul b), integral_const_mul,
    integral_const_mul] at hE
  have hG : ‖W1p.gradient (a • u + b • v)‖ ^ 2 ≤
      a * ‖W1p.gradient u‖ ^ 2 + b * ‖W1p.gradient v‖ ^ 2 := by
    have hn : ‖W1p.gradient (a • u + b • v)‖ ≤ a * ‖W1p.gradient u‖ + b * ‖W1p.gradient v‖ := by
      have hlin : W1p.gradient (a • u + b • v) = a • W1p.gradient u + b • W1p.gradient v := by
        simp only [← W1p.gradientL_apply, map_add, map_smul]
      rw [hlin]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h0 : 0 ≤ ‖W1p.gradient (a • u + b • v)‖ := norm_nonneg _
    nlinarith [mul_nonneg ha hb, sq_nonneg (‖W1p.gradient u‖ - ‖W1p.gradient v‖),
      norm_nonneg (W1p.gradient u), norm_nonneg (W1p.gradient v)]
  have hL : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value (a • u + b • v) z =
      a * (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
      b * ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z := by
    have hcu : Integrable fun z ↦ a * ((2 * ‖P.derivative.eval z‖ ^ 2 /
        (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) :=
      (hc.integrable_mul (memLp_value u)).const_mul a
    have hcv : Integrable fun z ↦ b * ((2 * ‖P.derivative.eval z‖ ^ 2 /
        (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z) :=
      (hc.integrable_mul (memLp_value v)).const_mul b
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hcu hcv]
    refine integral_congr_ae ?_
    filter_upwards [hval] with z hz
    simp only [hz]
    ring
  have hu2 := mul_le_mul_of_nonneg_left hu.2 ha
  have hv2 := mul_le_mul_of_nonneg_left hv.2 hb
  rw [sobolevReducedFunctional_def] at hu2 hv2 ⊢
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- The sublevel sets of Taubes's functional on `W^{1,2}(ℂ)`, among the functions with integrable
potential, are closed: the potential is lower semicontinuous and the other terms continuous. -/
private theorem isClosed_sublevel (hm : 0 < P.natDegree) (t : ℝ) :
    IsClosed {u : W1p (volume : Measure ℂ) ⊤ 2 |
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ∧
      sobolevReducedFunctional P u ≤ t} := by
  have hc := memLp_linearCoeff hm
  set B : W1p (volume : Measure ℂ) ⊤ 2 → ℝ := fun u ↦ ‖W1p.gradient u‖ ^ 2 / 2 +
    ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z with hB_def
  have hB : Continuous B := by
    have hG : Continuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦ ‖W1p.gradient u‖ := by
      simpa only [W1p.gradientL_apply] using
        (W1p.gradientL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).continuous.norm
    have hL : Continuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := by
      have hV : Continuous fun u : W1p (volume : Measure ℂ) ⊤ 2 ↦ W1p.value u :=
        (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2)).continuous.congr
          W1p.valueL_apply
      simp only [integral_mul_value_eq_inner hc]
      exact continuous_const.inner hV
    exact ((hG.pow 2).div_const 2).add hL
  have heq : {u : W1p (volume : Measure ℂ) ⊤ 2 |
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ∧
      sobolevReducedFunctional P u ≤ t} =
      {u | ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ≤
        ENNReal.ofReal (16 * (t - B u))} ∩ {u | B u ≤ t} := by
    ext u
    simp only [mem_ofPred_eq, mem_inter_iff]
    have hnn : 0 ≤ᵐ[volume] fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
      ae_of_all _ fun z ↦ mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)
    have hE := integral_potential_nonneg (P := P) (W1p.value u)
    rw [sobolevReducedFunctional_def]
    constructor
    · rintro ⟨hi, ht⟩
      refine ⟨?_, by simp only [hB_def]; linarith⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
      exact ENNReal.ofReal_le_ofReal (by simp only [hB_def]; linarith)
    · rintro ⟨hV, hBt⟩
      have hi : Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) :=
        ⟨aestronglyMeasurable_potential P u,
          (hasFiniteIntegral_iff_ofReal hnn).2 (hV.trans_lt ENNReal.ofReal_lt_top)⟩
      refine ⟨hi, ?_⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
        ENNReal.ofReal_le_ofReal_iff (by linarith)] at hV
      simp only [hB_def] at hBt hV
      linarith
  rw [heq]
  exact ((lowerSemicontinuous_lintegral_potential P).isClosed_setOf_le
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub hB)))).inter
    (isClosed_le hB continuous_const)

/-- **Existence of a minimizer of Taubes's functional.** For a complex polynomial `P` of degree at
least one, Taubes's functional `I = TauCeti.Vortex.sobolevReducedFunctional P` attains its
infimum over the functions `u ∈ W^{1,2}(ℂ)` whose potential `h (exp (2u) - 1 - 2u)` is
integrable. -/
theorem exists_isMinOn_sobolevReducedFunctional (hm : 0 < P.natDegree) :
    ∃ u ∈ {v : W1p (volume : Measure ℂ) ⊤ 2 |
        Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z))},
      IsMinOn (sobolevReducedFunctional P) {v | Integrable (fun z ↦
        ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z))} u := by
  -- Name the admissible set `D` and the sublevel sets `S t`, keeping them opaque.
  obtain ⟨D, hD⟩ : ∃ D : Set (W1p (volume : Measure ℂ) ⊤ 2), D = {v | Integrable (fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z))} := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ → Set (W1p (volume : Measure ℂ) ⊤ 2), ∀ t, S t = {u | Integrable
      (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) ∧
      sobolevReducedFunctional P u ≤ t} := ⟨_, fun _ ↦ rfl⟩
  rw [← hD]
  have hSD (t : ℝ) (u) (hu : u ∈ S t) : u ∈ D ∧ sobolevReducedFunctional P u ≤ t := by
    rw [hS] at hu
    rw [hD]
    exact hu
  have hDS (t : ℝ) (u) (hu : u ∈ D) (ht : sobolevReducedFunctional P u ≤ t) : u ∈ S t := by
    rw [hD] at hu
    rw [hS]
    exact ⟨hu, ht⟩
  have hconv (t : ℝ) : Convex ℝ (S t) := hS t ▸ convex_sublevel hm t
  have hclosed (t : ℝ) : IsClosed (S t) := hS t ▸ isClosed_sublevel hm t
  -- The zero function is admissible.
  have h0 : (0 : W1p (volume : Measure ℂ) ⊤ 2) ∈ D := by
    have hz : (W1p.value (0 : W1p (volume : Measure ℂ) ⊤ 2) : ℂ → ℝ) =ᵐ[volume] 0 := by
      have := (Lp.coeFn_zero ℝ 2 ((volume : Measure ℂ).restrict
        ((⊤ : Opens ℂ) : Set ℂ))).filter_mono (ae_mono Measure.restrict_univ.ge)
      simpa only [← W1p.valueL_apply, map_zero] using this
    rw [hD]
    refine (integrable_zero ℂ ℝ volume).congr ?_
    filter_upwards [hz] with z hz
    simp [hz]
  obtain ⟨C₀, hC₀⟩ := exists_le_sobolevReducedFunctional hm
  have hne : (sobolevReducedFunctional P '' D).Nonempty := ⟨_, 0, h0, rfl⟩
  have hbdd : BddBelow (sobolevReducedFunctional P '' D) :=
    ⟨C₀, by rintro _ ⟨v, hv, rfl⟩; rw [hD] at hv; exact hC₀ v hv⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = sInf (sobolevReducedFunctional P '' D) := ⟨_, rfl⟩
  -- The images in the weak topology of the sublevel sets at the levels `m + 1 / (n + 1)`.
  let K : ℕ → Set (WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)) :=
    fun n ↦ toWeakSpace ℝ _ '' S (m + 1 / (n + 1))
  have hmono (n : ℕ) : K (n + 1) ⊆ K n := by
    refine image_mono fun u hu ↦ ?_
    obtain ⟨huD, hut⟩ := hSD _ u hu
    refine hDS _ u huD (hut.trans ?_)
    have : 1 / ((↑(n + 1) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    linarith
  have hKne (n : ℕ) : (K n).Nonempty := by
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
      (lt_add_of_pos_right (sInf (sobolevReducedFunctional P '' D))
        (by positivity : (0 : ℝ) < 1 / (n + 1)))
    exact ⟨_, v, hDS _ v hv (hm_def ▸ hlt.le), rfl⟩
  have hK0 : IsCompact (K 0) := by
    obtain ⟨R, hR⟩ := exists_norm_le_of_sobolevReducedFunctional_le hm (m + 1 / ((0 : ℕ) + 1))
    have hsub : S (m + 1 / ((0 : ℕ) + 1)) ⊆ closedBall 0 R := fun u hu ↦ by
      obtain ⟨huD, hut⟩ := hSD _ u hu
      rw [hD] at huD
      exact mem_closedBall_zero_iff.2 (hR u huD hut)
    exact isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded
      (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ)) (hclosed _) (hconv _)
      (isBounded_closedBall.subset hsub)
  have hKcl (n : ℕ) : IsClosed (K n) := by
    have h := Convex.toWeakSpace_closure ℝ (hconv (m + 1 / (n + 1)))
    rw [(hclosed _).closure_eq] at h
    simp only [K]
    rw [h]
    exact isClosed_closure
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hKne hK0 hKcl
  have hmem (n : ℕ) : (toWeakSpace ℝ _).symm x ∈ S (m + 1 / (n + 1)) := by
    obtain ⟨v, hv, hvx⟩ := mem_iInter.1 hx n
    rw [← hvx, LinearEquiv.symm_apply_apply]
    exact hv
  refine ⟨(toWeakSpace ℝ _).symm x, (hSD _ _ (hmem 0)).1, isMinOn_iff.2 fun v hv ↦ ?_⟩
  have hle : sobolevReducedFunctional P ((toWeakSpace ℝ _).symm x) ≤ m := by
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [(hSD _ _ (hmem n)).2]
  exact hle.trans (hm_def ▸ csInf_le hbdd ⟨v, hv, rfl⟩)

end Sobolev

end TauCeti.Vortex
