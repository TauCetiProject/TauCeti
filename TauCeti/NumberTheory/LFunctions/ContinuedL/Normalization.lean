/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Normalization
import TauCeti.Analysis.Meromorphic.NormalForm

/-!
# Normalization translation of continued L-functions

In a `NormalizationTranslation` of weight `w`, the analytic completed function is
`N^(-w / 4) * Λ_ar(s + w / 2)` and the analytic gamma parameters are the arithmetic ones shifted by
`+w / 2`. Multiplying by `N^(-s / 2)` combines the two powers of the conductor into
`N^(-(s + w / 2) / 2)`, so the unextended product `N^(-s / 2) * Λ(s) * γ(s)⁻¹` of the analytic
record is literally the arithmetic one shifted by `s ↦ s + w / 2`. Since local conversion to
meromorphic normal form commutes with translation (`TauCeti.toMeromorphicNFAt_comp_add_const`),
`T.analytic.continuedL s = T.arithmetic.continuedL (s + w / 2)` holds pointwise on all of `ℂ`
without any continuation hypothesis.

## Main results

* `NormalizationTranslation.analytic_invGammaFactor`: `T.analytic.invGammaFactor` is
  `T.arithmetic.invGammaFactor` shifted by `w / 2`.
* `NormalizationTranslation.analytic_continuedL_apply`,
  `NormalizationTranslation.analytic_continuedL`: `T.analytic.continuedL` is
  `T.arithmetic.continuedL` shifted by `w / 2`.
* `NormalizationTranslation.meromorphicOrderAt_analytic_continuedL`,
  `NormalizationTranslation.analyticAt_analytic_continuedL_iff`: meromorphic order and analyticity
  translate by `w / 2`.
* `NormalizationTranslation.arithmetic_continuedL_eq_LSeries`: in the arithmetic normalization,
  `T.arithmetic.continuedL s = LSeries T.arithmetic.coeff s` on `1 + w / 2 < s.re`.
-/

public section

open Complex

namespace TauCeti.LFunctions.NormalizationTranslation

variable (T : NormalizationTranslation)

/-- The analytic reciprocal gamma factor is the arithmetic one shifted by `w / 2`. -/
@[simp]
theorem analytic_invGammaFactor (s : ℂ) :
    T.analytic.invGammaFactor s = T.arithmetic.invGammaFactor (s + (T.weight : ℂ) / 2) := by
  simp [AnalyticLFunctionData.invGammaFactor_def]

/-- **Normalization shift of `continuedL`.** Passing from an arithmetic normalization of weight `w`
to its analytic normalization shifts `continuedL` by `+w / 2` at every point of `ℂ`, both on and
off the support of `polarOrder`. -/
@[simp]
theorem analytic_continuedL_apply (s : ℂ) :
    T.analytic.continuedL s = T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  have hN : ((T.arithmetic.conductor : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr T.arithmetic.conductor.ne_zero
  have hraw_apply (z : ℂ) :
      ((T.analytic.conductor : ℕ) : ℂ) ^ (-z / 2) *
          T.analytic.completed z * T.analytic.invGammaFactor z =
        ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(z + (T.weight : ℂ) / 2) / 2) *
          T.arithmetic.completed (z + (T.weight : ℂ) / 2) *
            T.arithmetic.invGammaFactor (z + (T.weight : ℂ) / 2) := by
    have hpow : ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
        ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4) =
        ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(z + (T.weight : ℂ) / 2) / 2) := by
      rw [← cpow_add _ _ hN]
      congr 1
      ring
    rw [T.conductor_eq, T.completed_eq, T.analytic_invGammaFactor]
    calc
      ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
          (((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4) *
            T.arithmetic.completed (z + (T.weight : ℂ) / 2)) *
          T.arithmetic.invGammaFactor (z + (T.weight : ℂ) / 2) =
        (((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
          ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4)) *
            T.arithmetic.completed (z + (T.weight : ℂ) / 2) *
          T.arithmetic.invGammaFactor (z + (T.weight : ℂ) / 2) := by ring
      _ = ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(z + (T.weight : ℂ) / 2) / 2) *
            T.arithmetic.completed (z + (T.weight : ℂ) / 2) *
          T.arithmetic.invGammaFactor (z + (T.weight : ℂ) / 2) := by rw [hpow]
  have hraw : (fun z : ℂ ↦ ((T.analytic.conductor : ℕ) : ℂ) ^ (-z / 2) *
      T.analytic.completed z * T.analytic.invGammaFactor z) =
      (fun z : ℂ ↦ ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-z / 2) *
        T.arithmetic.completed z * T.arithmetic.invGammaFactor z) ∘
        (· + (T.weight : ℂ) / 2) :=
    funext hraw_apply
  have hinv_fn : T.analytic.invGammaFactor =
      T.arithmetic.invGammaFactor ∘ (· + (T.weight : ℂ) / 2) :=
    funext T.analytic_invGammaFactor
  have hord : meromorphicOrderAt T.analytic.invGammaFactor s =
      meromorphicOrderAt T.arithmetic.invGammaFactor (s + (T.weight : ℂ) / 2) := by
    rw [hinv_fn, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  rw [AnalyticLFunctionData.continuedL_def, AnalyticLFunctionData.continuedL_def,
    T.polarOrder_eq s, hord]
  split_ifs with hcond
  · rw [hraw, TauCeti.toMeromorphicNFAt_comp_add_const_apply]
  · exact hraw_apply s

/-- Function-level form of `analytic_continuedL_apply`. -/
theorem analytic_continuedL :
    T.analytic.continuedL = T.arithmetic.continuedL ∘ (· + (T.weight : ℂ) / 2) :=
  funext T.analytic_continuedL_apply

/-- Translation preserves the meromorphic order of `continuedL` at the shifted point. -/
@[simp]
theorem meromorphicOrderAt_analytic_continuedL (s : ℂ) :
    meromorphicOrderAt T.analytic.continuedL s =
      meromorphicOrderAt T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  rw [T.analytic_continuedL, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- Translation preserves analyticity of `continuedL` at the shifted point. -/
@[simp]
theorem analyticAt_analytic_continuedL_iff (s : ℂ) :
    AnalyticAt ℂ T.analytic.continuedL s ↔
      AnalyticAt ℂ T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  rw [T.analytic_continuedL]
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_of_eq (by fun_prop) rfl⟩
  have h' := h.comp_of_eq (f := fun z ↦ z - (T.weight : ℂ) / 2) (by fun_prop)
    (add_sub_cancel_right s ((T.weight : ℂ) / 2))
  exact h'.congr (Filter.Eventually.of_forall fun z ↦ by simp)

/-- On the arithmetic half-plane `1 + w / 2 < s.re`, `T.arithmetic.continuedL` agrees with the
arithmetic Dirichlet series `LSeries T.arithmetic.coeff`. -/
theorem arithmetic_continuedL_eq_LSeries
    (hda : T.analytic.HasDirichletAgreement) (hmc : T.analytic.HasMeromorphicContinuation)
    {s : ℂ} (hs : 1 + (T.weight : ℝ) / 2 < s.re) :
    T.arithmetic.continuedL s = LSeries T.arithmetic.coeff s := by
  set d : ℂ := (T.weight : ℂ) / 2
  have hlt : 1 < (s - d).re := by
    have hd : d.re = (T.weight : ℝ) / 2 := by simp [d]
    rw [sub_re, hd]
    linarith
  have heq := hda.continuedL_eq_LSeries hmc hlt
  rw [T.analytic_continuedL_apply, T.LSeries_analytic_coeff, sub_add_cancel] at heq
  exact heq

end TauCeti.LFunctions.NormalizationTranslation
