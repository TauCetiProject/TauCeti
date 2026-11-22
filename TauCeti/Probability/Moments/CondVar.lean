/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CondVar

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# The conditional law of total variance

For σ-algebras `m₁ ≤ m₂ ≤ m₀` and a square-integrable real random variable `X`, the conditional
variance of `X` given the coarser information `m₁` splits into the expected residual variance
given the finer information `m₂` and the variance of the finer conditional mean:

`Var[X | m₁] = E[Var[X | m₂] | m₁] + Var[E[X | m₂] | m₁]` almost everywhere.

Square integrability of `X` is assumed throughout, but no finiteness of the measure. Two junk
cases of Mathlib's conditional expectation then occur, and the identity holds in both. If the
trim of the measure to the coarser σ-algebra is not σ-finite, every conditional expectation
given it is `0`, so all three terms vanish. If `X` is square integrable but not integrable (on an
infinite measure), the conditional mean `E[X | m]` is `0`, while the conditional second moment
`E[X² | m]` of the integrable `X²` need not vanish. On a probability space,
the specialization `m₁ = ⊥` corresponds to Mathlib's scalar law of total variance
`integral_condVar_add_variance_condExp`.

## Main statements

* `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp'`: `Var[X | m] = E[X² | m] - E[X | m]²`
  almost everywhere, for a square-integrable `X` and an arbitrary measure.
* `ProbabilityTheory.condVar_ae_eq_condExp_condVar_add_condVar_condExp`: the conditional law of
  total variance for nested σ-algebras and a square-integrable `X`.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley, 2019,
  equations (10.9)–(10.10), p. 233 (the specialization to observed and complete data).
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m m₁ m₂ m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} {X : Ω → ℝ}

/-- The conditional variance of a square-integrable `X` is the conditional second moment minus the
square of the conditional mean, `μ`-almost everywhere, for an arbitrary measure `μ`. This is
Mathlib's `condVar_ae_eq_condExp_sq_sub_sq_condExp` without its finiteness assumption on `μ`. -/
theorem condVar_ae_eq_condExp_sq_sub_sq_condExp' (hm : m ≤ m₀) (hX : MemLp X 2 μ) :
    Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 := by
  by_cases hσ : SigmaFinite (μ.trim hm); swap
  · simp [condVar_of_not_sigmaFinite hσ, condExp_of_not_sigmaFinite hm hσ]
  by_cases hXi : Integrable X μ; swap
  · simp [condVar, condExp_of_not_integrable hXi]
  -- On each finite-measure spanning set of `μ.trim hm`, apply Mathlib's finite-measure identity.
  have hsq : Integrable ((X - μ[X | m]) ^ 2) μ := (hX.sub (hX.condExp one_le_two)).integrable_sq
  refine (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null ?_ ?_ <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  set s := spanningSets (μ.trim hm) n
  have hs : MeasurableSet[m] s := measurableSet_spanningSets _ n
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have hmean := condExp_restrict_ae_eq_restrict hm hs hXi
  have hvar : Var[X; μ.restrict s | m] =ᵐ[μ.restrict s] Var[X; μ | m] := by
    simp only [condVar]
    exact (condExp_congr_ae (hmean.mono fun ω hω ↦ by simp [hω])).trans
      (condExp_restrict_ae_eq_restrict hm hs hsq)
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm (hX.restrict s), hmean, hvar,
    condExp_restrict_ae_eq_restrict (f := X ^ 2) hm hs hX.integrable_sq] with ω h₁ h₂ h₃ h₄
  simp_all

/-- **Conditional law of total variance**: for nested σ-algebras `m₁ ≤ m₂ ≤ m₀` and a
square-integrable `X`, `μ`-almost everywhere, the conditional variance given `m₁` is the
conditional expectation given `m₁` of the conditional variance given `m₂`, plus the conditional
variance given `m₁` of the conditional expectation given `m₂`. The measure `μ` is arbitrary.

With `m₂` the complete-data and `m₁` the observed-data σ-algebra of a missing-data model, this is
the variance decomposition of Little and Rubin, *Statistical Analysis with Missing Data*, 3rd ed.,
equations (10.9)–(10.10), p. 233. -/
theorem condVar_ae_eq_condExp_condVar_add_condVar_condExp
    (h₁₂ : m₁ ≤ m₂) (h₂₀ : m₂ ≤ m₀) (hX : MemLp X 2 μ) :
    Var[X; μ | m₁] =ᵐ[μ] μ[Var[X; μ | m₂] | m₁] + Var[μ[X | m₂]; μ | m₁] := by
  have h₁₀ := h₁₂.trans h₂₀
  by_cases hσ : SigmaFinite (μ.trim h₁₀); swap
  · simp [condVar_of_not_sigmaFinite hσ, condExp_of_not_sigmaFinite h₁₀ hσ]
  have : SigmaFinite (μ.trim h₂₀) := sigmaFiniteTrim_mono h₂₀ h₁₂
  have hY : MemLp μ[X | m₂] 2 μ := hX.condExp one_le_two
  have hYsq : Integrable (μ[X | m₂] ^ 2) μ := hY.integrable_sq
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp' h₁₀ hX,
    condVar_ae_eq_condExp_sq_sub_sq_condExp' h₁₀ hY,
    condExp_congr_ae (m := m₁) (condVar_ae_eq_condExp_sq_sub_sq_condExp' h₂₀ hX),
    condExp_sub (m := m₁) (integrable_condExp (f := X ^ 2)) hYsq,
    condExp_condExp_of_le (f := X ^ 2) h₁₂ h₂₀, condExp_condExp_of_le (f := X) h₁₂ h₂₀]
    with ω h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  ring

end ProbabilityTheory
