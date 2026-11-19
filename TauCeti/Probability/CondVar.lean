/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CondVar

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# The conditional law of total variance

For σ-algebras `m₁ ≤ m₂ ≤ m₀` and a square-integrable real random variable `X` on a finite
measure space,

`Var[X | m₁] = E[Var[X | m₂] | m₁] + Var[E[X | m₂] | m₁]` almost everywhere.

Both sides reduce to second moments by `condVar_ae_eq_condExp_sq_sub_sq_condExp`, after which
the identity is the tower property `condExp_condExp_of_le`. The unconditional case `m₁ = ⊥` is
Mathlib's `integral_condVar_add_variance_condExp`.

## Main statements

* `ProbabilityTheory.condVar_ae_eq_condExp_condVar_add_condVar_condExp`: the conditional law of
  total variance for nested σ-algebras.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m₁ m₂ m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} {X : Ω → ℝ}

/-- **Conditional law of total variance**: for nested σ-algebras `m₁ ≤ m₂ ≤ m₀` and a
square-integrable `X`, the conditional variance given `m₁` is the conditional expectation given
`m₁` of the conditional variance given `m₂`, plus the conditional variance given `m₁` of the
conditional expectation given `m₂`. -/
theorem condVar_ae_eq_condExp_condVar_add_condVar_condExp [IsFiniteMeasure μ]
    (h₁₂ : m₁ ≤ m₂) (h₂₀ : m₂ ≤ m₀) (hX : MemLp X 2 μ) :
    Var[X; μ | m₁] =ᵐ[μ] μ[Var[X; μ | m₂] | m₁] + Var[μ[X | m₂]; μ | m₁] := by
  have h₁₀ := h₁₂.trans h₂₀
  have hY : MemLp μ[X | m₂] 2 μ := hX.condExp one_le_two
  have hYsq : Integrable (μ[X | m₂] ^ 2) μ := hY.integrable_sq
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp h₁₀ hX,
    condVar_ae_eq_condExp_sq_sub_sq_condExp h₁₀ hY,
    condExp_congr_ae (m := m₁) (condVar_ae_eq_condExp_sq_sub_sq_condExp h₂₀ hX),
    condExp_sub (m := m₁) (integrable_condExp (f := X ^ 2)) hYsq,
    condExp_condExp_of_le (f := X ^ 2) h₁₂ h₂₀, condExp_condExp_of_le (f := X) h₁₂ h₂₀]
    with ω h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  ring

end ProbabilityTheory
