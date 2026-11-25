/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic.Derivative

/-!
# The transpose derivative of locally analytic distributions

The derivative `TauCeti.LocallyAnalytic.derivative` of locally analytic functions is computed on
each analytic stage `LA_h(K)` by the continuous operator `TauCeti.AnalyticStage.derivative`, so its
transpose is the derivative of a distribution, `TauCeti.LocallyAnalyticDistribution.derivative`,
with the sign convention `(d μ)(f) = μ(f')`. It multiplies the stage seminorm of level `h` by at
most `‖p‖⁻ʰ`.

The Leibniz rule `x (d μ) = μ + d (x μ)` is in `TauCeti.NumberTheory.Padics.Distribution.MulCoord`,
and the Amice transform of the transpose derivative, `A_{d μ} = log (1 + T) · A_μ`, is in
`TauCeti.NumberTheory.Padics.Distribution.Amice.Derivative`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.derivative`: the transpose derivative `(d μ)(f) = μ(f')`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_derivative_le`: the derivative multiplies the
  stage seminorm of level `h` by at most `‖p‖⁻ʰ`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [NeZero (p : K)]

/-- The transpose derivative of a locally analytic distribution: `(d μ)(f) = μ(f')`. -/
noncomputable def derivative :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalyticDistribution p K :=
  dualMap (LocallyAnalytic.derivative K) (fun _ ↦ AnalyticStage.derivative K)
    (derivative_ofStage K)

/-- The distribution `d μ` takes the value `μ(f')` on `f`. -/
@[simp]
theorem coe_derivative_apply (μ : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    (derivative μ : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.derivative K f) :=
  coe_dualMap_apply μ f

/-- The restriction of `d μ` to a stage is the restriction of `μ` composed with the derivative on
that stage. -/
@[simp]
theorem stage_derivative (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stage h (derivative μ) = stage h μ ∘L AnalyticStage.derivative K :=
  stage_dualMap h μ

/-- The derivative multiplies the stage seminorm of level `h` by at most `‖p‖⁻ʰ`. -/
theorem stageSeminorm_derivative_le (h : ℕ) (μ : LocallyAnalyticDistribution p K) :
    stageSeminorm h (derivative μ) ≤ ‖((p : K) ^ h)⁻¹‖ * stageSeminorm h μ :=
  (stageSeminorm_dualMap_le h μ).trans
    (mul_le_mul_of_nonneg_right opNorm_derivative_le (apply_nonneg _ _))

end LocallyAnalyticDistribution

end TauCeti
