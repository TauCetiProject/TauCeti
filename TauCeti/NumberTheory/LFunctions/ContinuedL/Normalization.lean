/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Normalization

/-!
# Normalization translation of the continued L-function

Under a `NormalizationTranslation` of integer weight `w`, the analytic completed function is
`Λ_an(s) = N^(-w/4) Λ_ar(s + w/2)` while the gamma shifts are translated by `+w/2` and the polar
divisor is translated by `-w/2`. Multiplying by `N^(-s/2)` combines the normalizing factor
`N^(-w/4)` with `N^(-s/2)` into `N^(-(s + w/2)/2)`, and local meromorphic normal forms commute with
translation (`TauCeti.toMeromorphicNFAt_comp_add_const`). Consequently, the continued uncompleted
L-function translates directly by `s ↦ s + w/2` everywhere on `ℂ`, without continuation or
functional-equation hypotheses on either card.

## Main results

* `NormalizationTranslation.analytic_invGammaFactor`: `invGammaFactor` shifts by `w/2`.
* `NormalizationTranslation.analytic_continuedL`, `analytic_continuedL_comp`: `continuedL` shifts by
  `w/2` at every point of `ℂ`, including cancelled and uncancelled poles.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
-/

public section

open Complex

namespace TauCeti.LFunctions.NormalizationTranslation

variable (T : NormalizationTranslation)

/-- The entire reciprocal gamma factor of the analytic card is the arithmetic one shifted by
`w/2`. -/
@[simp]
theorem analytic_invGammaFactor (s : ℂ) :
    T.analytic.invGammaFactor s = T.arithmetic.invGammaFactor (s + (T.weight : ℂ) / 2) := by
  simp [AnalyticLFunctionData.invGammaFactor_def]

/-- **Normalization translation of `continuedL`.** The continued uncompleted L-function of the
analytic card equals that of the arithmetic card shifted by `w/2` at every point of `ℂ`, poles
included, matching the Dirichlet-series shift `NormalizationTranslation.LSeries_analytic_coeff`. -/
@[simp]
theorem analytic_continuedL (s : ℂ) :
    T.analytic.continuedL s = T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  set c : ℂ := (T.weight : ℂ) / 2
  set g : ℂ → ℂ := fun z ↦
    ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) * T.arithmetic.completed z *
      T.arithmetic.invGammaFactor z
  have hraw : (fun z ↦ ((T.analytic.conductor : ℕ) : ℂ) ^ (-z / 2) * T.analytic.completed z *
      T.analytic.invGammaFactor z) = g ∘ (· + c) := by
    ext z
    have hpow : ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
        ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4) =
        ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(z + c) / 2) := by
      rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr T.arithmetic.conductor.ne_zero)]
      congr 1
      simp only [c]
      ring
    simp only [Function.comp_apply, g, T.conductor_eq, T.completed_eq, T.analytic_invGammaFactor]
    calc
      ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
          (((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4) *
            T.arithmetic.completed (z + c)) *
          T.arithmetic.invGammaFactor (z + c) =
        (((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
          ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4)) *
          T.arithmetic.completed (z + c) * T.arithmetic.invGammaFactor (z + c) := by ring
      _ = ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(z + c) / 2) *
          T.arithmetic.completed (z + c) * T.arithmetic.invGammaFactor (z + c) := by rw [hpow]
  have hord : meromorphicOrderAt T.analytic.invGammaFactor s =
      meromorphicOrderAt T.arithmetic.invGammaFactor (s + c) := by
    rw [funext T.analytic_invGammaFactor,
      meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  simp only [AnalyticLFunctionData.continuedL_def, T.polarOrder_eq, hord]
  split_ifs
  · rw [hraw]
    exact congrFun (TauCeti.toMeromorphicNFAt_comp_add_const g s c) s
  · exact congrFun hraw s

/-- Function-level form of `NormalizationTranslation.analytic_continuedL`. -/
theorem analytic_continuedL_comp :
    T.analytic.continuedL = T.arithmetic.continuedL ∘ (· + (T.weight : ℂ) / 2) :=
  funext T.analytic_continuedL

end TauCeti.LFunctions.NormalizationTranslation
