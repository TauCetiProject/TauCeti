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
import TauCeti.Analysis.Sobolev.Poincare.Planar
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Coercivity of Taubes's functional for the prescribed-zero vortex problem

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

These are the coercivity estimates of the direct method on `H¹(ℂ)`. The extension of `I` and of
these estimates to `H¹(ℂ)`, the existence of a minimizer, and its regularity are not treated here.

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

/-- The potential `exp (2t) - 1 - 2t` is nonnegative. -/
private theorem exp_two_mul_sub_one_sub_two_mul_nonneg (t : ℝ) :
    0 ≤ Real.exp (2 * t) - 1 - 2 * t := by
  linarith [Real.add_one_le_exp (2 * t)]

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
  integral_nonneg fun z ↦ mul_nonneg (by positivity) (exp_two_mul_sub_one_sub_two_mul_nonneg _)

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
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, 1 ≤ ‖P.eval z‖) {w : ℂ → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) :
    ∫ z in (closedBall (0 : ℂ) R)ᶜ, (√(1 + w z ^ 2) - 1) ≤
      2 * ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) := by
  have hpint := integrable_potential (P := P) hw hws
  have hmod : Integrable fun z ↦ √(1 + w z ^ 2) - 1 :=
    (by fun_prop : Continuous fun z ↦ √(1 + w z ^ 2) - 1).integrable_of_hasCompactSupport
      (hws.mono fun z hz h0 ↦ hz (by simp [h0]))
  have hpot (z : ℂ) :
      0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    mul_nonneg (by positivity) (exp_two_mul_sub_one_sub_two_mul_nonneg _)
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
        have := exp_two_mul_sub_one_sub_two_mul_nonneg (w z)
        nlinarith
    _ ≤ ∫ z, 2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) :=
        setIntegral_le_integral (hpint.const_mul 2)
          (Eventually.of_forall fun z ↦ mul_nonneg zero_le_two (hpot z))

/-- The energy `∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w)` controls `∫ w²`:
its square is at most a constant times the cube of one plus the energy. -/
private theorem exists_sq_integral_sq_le (hm : 0 < P.natDegree) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ z, w z ^ 2) ^ 2 ≤ γ * (1 + ((∫ z, ‖fderiv ℝ w z‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * w z) - 1 - 2 * w z)) / 16)) ^ 3 := by
  obtain ⟨C₀, hC₀, hpl⟩ :=
    exists_integral_sq_le_of_finrank_eq_two (volume : Measure ℂ) Complex.finrank_real_complex
  -- A nonconstant polynomial has modulus at least one outside a closed disc.
  obtain ⟨R, -, hR⟩ := (hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp
    (by
      rw [cobounded_eq_cocompact]
      exact (P.tendsto_norm_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp hm)
        tendsto_norm_cocompact_atTop).eventually_ge_atTop 1 :
      ∀ᶠ z in Bornology.cobounded ℂ, 1 ≤ ‖P.eval z‖)
  set S := volume.real (closedBall (0 : ℂ) R)
  set β := 8 + 4 * C₀ ^ 2
  refine ⟨8192 * β + 2 * β ^ 2 * S ^ 2, by positivity, fun w hw hws ↦ ?_⟩
  set A := ∫ z, ‖fderiv ℝ w z‖ ^ 2
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)
  set M := A / 2 + E / 16
  set k := 2 + C₀ * √A
  have hA : 0 ≤ A := integral_nonneg fun z ↦ by positivity
  have hE : 0 ≤ E := integral_potential_nonneg w
  have hk : 0 ≤ k := by positivity
  -- The planar estimate with `s` the disc: `∫ w² ≤ 2 k (2 E) + k² S ≤ 64 k M + k² S`.
  have hW1 : ∫ z, w z ^ 2 ≤ 64 * k * M + k ^ 2 * S := by
    have h := hpl w hw hws (closedBall (0 : ℂ) R) measurableSet_closedBall
      measure_closedBall_lt_top.ne
    have h2 := mul_le_mul_of_nonneg_left
      (setIntegral_compl_closedBall_le hR hw.continuous hws) (by positivity : 0 ≤ 2 * k)
    have h3 : 2 * k * (2 * E) ≤ 64 * k * M := by
      have : E ≤ 16 * M := by simp only [M]; linarith
      nlinarith
    linarith
  -- `k² ≤ 8 + 2 C₀² A ≤ β (1 + M)`.
  have hk2 : k ^ 2 ≤ β * (1 + M) := by
    have hsA : √A ^ 2 = A := Real.sq_sqrt hA
    have : k ^ 2 ≤ 8 + 2 * C₀ ^ 2 * A := by
      simp only [k]
      nlinarith [sq_nonneg (2 - C₀ * √A)]
    have : A ≤ 2 * M := by simp only [M]; linarith
    simp only [β]
    nlinarith [sq_nonneg C₀]
  exact sq_le_mul_one_add_pow_three (integral_nonneg fun z ↦ sq_nonneg _) (by positivity)
    (by positivity) hW1 hk2

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
  set c : ℂ → ℝ := fun z ↦
    2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8
  have hc : MemLp c 2 := by
    have h1 := (P.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).const_mul 2
    have h2 := (Polynomial.memLp_inv_one_add_norm_eval_sq hm).const_mul (1 / 8 : ℝ)
    convert h1.sub h2 using 1
    funext z
    simp only [c, Pi.sub_apply]
    ring
  set K := ∫ z, c z ^ 2
  set D := K ^ 2 * γ
  refine ⟨1 + 16 * D, fun w hw hws ↦ ?_⟩
  set A := ∫ z, ‖fderiv ℝ w z‖ ^ 2
  set E := ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)
  set M := A / 2 + E / 16
  have hM : 0 ≤ M := energy_nonneg w
  have hwL : MemLp w 2 := hw.continuous.memLp_of_hasCompactSupport hws
  -- The linear term: `|∫ c w| ≤ x` with `x² ≤ K ∫ w²`, hence `x⁴ ≤ D (1 + M)³`.
  set x := ∫ z, |c z| * |w z|
  have hlin : -x ≤ ∫ z, c z * w z := by
    have h1 : |∫ z, c z * w z| ≤ x :=
      calc |∫ z, c z * w z| ≤ ∫ z, |c z * w z| := abs_integral_le_integral_abs
        _ = x := by simp_rw [abs_mul, x]
    linarith [neg_abs_le (∫ z, c z * w z)]
  have hx2 : x ^ 2 ≤ K * ∫ z, w z ^ 2 := by
    have := sq_integral_mul_le_integral_sq_mul_integral_sq (f := fun z ↦ |c z|)
      (g := fun z ↦ |w z|) (by simpa [Real.norm_eq_abs] using hc.norm)
      (by simpa [Real.norm_eq_abs] using hwL.norm)
    simpa only [sq_abs] using this
  have hx4 : x ^ 4 ≤ D * (1 + M) ^ 3 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ ≤ (K * ∫ z, w z ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg x) hx2 2
      _ = K ^ 2 * (∫ z, w z ^ 2) ^ 2 := by ring
      _ ≤ K ^ 2 * (γ * (1 + M) ^ 3) := by gcongr; exact hsq w hw hws
      _ = D * (1 + M) ^ 3 := by simp only [D]; ring
  have hxM := le_div_two_add_of_pow_four_le (by positivity) hM hx4
  have hI : reducedFunctional P w = M + ∫ z, c z * w z := by
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

end TauCeti.Vortex
