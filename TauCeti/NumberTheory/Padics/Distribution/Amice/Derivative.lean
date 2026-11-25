/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.MulCoord

/-!
# The Amice transform of the transpose derivative

The transpose derivative `(d μ)(f) = μ(f')` of a locally analytic distribution
(`TauCeti.LocallyAnalyticDistribution.derivative`) acts on Amice transforms, over a complete
field `K` of characteristic zero, as multiplication by `log (1 + T)`
(`amiceTransform_derivative`):

`A_{d μ} = log (1 + T) · A_μ`.

Two standalone facts enter: the derivative kills the constants, which are the Mahler terms of
degree `0` (`LocallyAnalytic.derivative_mahlerTerm_zero`), and the transpose derivative and
multiplication by the coordinate satisfy the commutator relation `x (d μ) = μ + d (x μ)`
(`LocallyAnalyticDistribution.mulCoord_derivative`).

As `log (1 + T)` is not a zero divisor, the transpose derivative is injective. Its interaction with
convolution is in `TauCeti.NumberTheory.Padics.Distribution.Amice.Derivative.Convolution`.

## Main results

* `TauCeti.LocallyAnalytic.derivative_mahlerTerm_zero`: the derivative of a constant is zero.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_derivative`: `A_{d μ} = log (1 + T) · A_μ`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_iterate_derivative`:
  `A_{dᵏ μ} = log (1 + T)ᵏ · A_μ`.
* `TauCeti.LocallyAnalyticDistribution.derivative_injective`: the transpose derivative is
  injective.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (𝕜 : Type*) [Field 𝕜] [NeZero (p : 𝕜)] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
  [SMulCommClass ℤ_[p] 𝕜 E]

/-- **The derivative of a constant is zero**: `mahlerTerm p 𝕜 e 0` is the constant function `e`. -/
@[simp]
theorem derivative_mahlerTerm_zero (e : E) : derivative 𝕜 (mahlerTerm p 𝕜 e 0) = 0 := by
  rw [mahlerTerm_def]
  refine derivative_ofStage_eq_zero 𝕜 fun a n ↦ ?_
  rw [amiceTerm_apply, coeff_amicePolynomial_eq_zero _ (Nat.succ_pos n), zero_smul]

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- **The Amice transform of the transpose derivative.** With the convention `(d μ)(f) = μ(f')`,
the Amice transform of `d μ` is `log (1 + T)` times the Amice transform of `μ`. -/
@[simp]
theorem amiceTransform_derivative (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (derivative μ) = PowerSeries.log K * amiceTransform μ := by
  -- No formula for the derivatives of the binomial polynomials is needed. Multiplication by `x`
  -- acts on Amice transforms as the derivation `∂ = (1 + T) d/dT`, and `∂ log (1 + T) = 1`, so
  -- by `x (d ν) = ν + d (x ν)` the difference `A_{d ν} - log (1 + T) A_ν` intertwines
  -- multiplication by `x` with `∂`. Its constant coefficient vanishes because the derivative kills
  -- the constant `1`, and `∂ (∑ₙ aₙ Tⁿ) = ∑ₙ ((n + 1) aₙ₊₁ + n aₙ) Tⁿ` then kills all its
  -- coefficients by induction.
  set L := PowerSeries.log K
  set D := PowerSeries.mahlerDerivation K
  -- `∂ log (1 + T) = (1 + T) d/dT log (1 + T) = 1`.
  have hL : D L = 1 := by
    rw [PowerSeries.mahlerDerivation_apply, mul_comm, PowerSeries.derivative_log_mul_one_add_X]
  -- The difference `A_{d ν} - L A_ν` intertwines multiplication by `x` with `∂`.
  have hstep (ν : LocallyAnalyticDistribution p K) :
      D (amiceTransform (derivative ν)) - D (L * amiceTransform ν) =
        amiceTransform (derivative (mulCoord ν)) - L * amiceTransform (mulCoord ν) := by
    rw [← amiceTransform_mulCoord, mulCoord_derivative, map_add, Derivation.leibniz, hL,
      amiceTransform_mulCoord, smul_eq_mul, smul_eq_mul, mul_one]
    ring
  ext n
  induction n generalizing μ with
  | zero =>
    -- The constant coefficients vanish: the derivative kills the constant `1`.
    simp [L, PowerSeries.coeff_mul]
  | succ n ih =>
    have hn := congrArg (PowerSeries.coeff n) (hstep μ)
    simp only [map_sub, D, PowerSeries.coeff_mahlerDerivation, ih μ, ih (mulCoord μ),
      sub_self] at hn
    refine mul_left_cancel₀ (Nat.cast_add_one_ne_zero n : ((n : K) + 1) ≠ 0) ?_
    linear_combination hn

/-- Iterating, the transpose derivative `dᵏ` acts on the Amice transform as multiplication by
`log (1 + T) ^ k`. -/
theorem amiceTransform_iterate_derivative (μ : LocallyAnalyticDistribution p K) (k : ℕ) :
    amiceTransform (derivative^[k] μ) = PowerSeries.log K ^ k * amiceTransform μ := by
  rw [Function.Semiconj.iterate_right (f := amiceTransform) (gb := (PowerSeries.log K * ·))
    amiceTransform_derivative k μ, mul_left_iterate_apply]

/-- The transpose derivative is injective: `log (1 + T)` is not a zero divisor of `K⟦T⟧`. -/
theorem derivative_injective :
    Function.Injective (derivative (p := p) (K := K)) := by
  have hL : PowerSeries.log K ≠ 0 := fun hL ↦ by
    simpa [hL] using PowerSeries.derivative_log_mul_one_add_X (A := K)
  intro μ ν hμν
  refine amiceTransform_injective (mul_left_cancel₀ hL ?_)
  rw [← amiceTransform_derivative, ← amiceTransform_derivative, hμν]

end LocallyAnalyticDistribution

end TauCeti
