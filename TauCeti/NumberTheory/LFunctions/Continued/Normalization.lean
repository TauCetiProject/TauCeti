/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Normalization
import TauCeti.Analysis.Meromorphic.NormalForm

/-!
# Normalization translation of the continued function

In a `NormalizationTranslation` of weight `w`, the analytic completed function is
`N^(-w/4) Λ_ar(s + w/2)` and the analytic gamma shifts are the arithmetic ones plus `w/2`.
Multiplying by `N^(-s/2)` combines the two conductor powers into `N^(-(s + w/2)/2)`, so the raw
uncompleted product of the analytic record is that of the arithmetic record translated by
`w/2`. Conversion to meromorphic normal form commutes with translation, so

`T.analytic.continuedL s = T.arithmetic.continuedL (s + w/2)`

at every point of `ℂ`, poles included, without any continuation hypothesis.

The statements follow Christian Merten's earlier construction in Tau Ceti PR #41996,
transported to the canonical `AnalyticLFunctionData.continuedL`.
-/

public section

open Complex

namespace TauCeti.LFunctions.NormalizationTranslation

variable (T : NormalizationTranslation)

/-- The analytic reciprocal gamma factor is the arithmetic one translated by `w/2`. -/
@[simp]
theorem analytic_invGammaFactor (s : ℂ) :
    T.analytic.invGammaFactor s = T.arithmetic.invGammaFactor (s + (T.weight : ℂ) / 2) := by
  simp [AnalyticLFunctionData.invGammaFactor_def]

/-- The raw uncompleted product of the analytic record is the arithmetic one translated by
`w/2`. -/
theorem analytic_uncompletedProduct :
    T.analytic.uncompletedProduct =
      T.arithmetic.uncompletedProduct ∘ (· + (T.weight : ℂ) / 2) := by
  funext z
  have hexp : -(z + (T.weight : ℂ) / 2) / 2 = -z / 2 + -(T.weight : ℂ) / 4 := by ring
  simp only [Function.comp_apply, AnalyticLFunctionData.uncompletedProduct_def, T.conductor_eq,
    T.completed_eq, T.analytic_invGammaFactor, hexp,
    cpow_add _ _ (Nat.cast_ne_zero.mpr T.arithmetic.conductor.ne_zero)]
  ring

/-- **Normalization translation of the continued function.** Passing from the arithmetic to the
analytic normalization of weight `w` translates the continued function by `w/2`, at every point
of `ℂ`. -/
theorem analytic_continuedL :
    T.analytic.continuedL = T.arithmetic.continuedL ∘ (· + (T.weight : ℂ) / 2) := by
  have hset : {s | 0 ≤ meromorphicOrderAt T.analytic.uncompletedProduct s} =
      (· + (T.weight : ℂ) / 2) ⁻¹'
        {s | 0 ≤ meromorphicOrderAt T.arithmetic.uncompletedProduct s} := by
    ext s
    simp [T.analytic_uncompletedProduct, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  rw [AnalyticLFunctionData.continuedL_def, AnalyticLFunctionData.continuedL_def, hset,
    T.analytic_uncompletedProduct, TauCeti.toMeromorphicNFOn_comp_add_const]

/-- Pointwise form of `NormalizationTranslation.analytic_continuedL`. -/
@[simp]
theorem analytic_continuedL_apply (s : ℂ) :
    T.analytic.continuedL s = T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) :=
  congrFun T.analytic_continuedL s

/-- Translation preserves the meromorphic order of the continued function. -/
@[simp]
theorem meromorphicOrderAt_analytic_continuedL (s : ℂ) :
    meromorphicOrderAt T.analytic.continuedL s =
      meromorphicOrderAt T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  rw [T.analytic_continuedL, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- Translation preserves analyticity of the continued function. -/
@[simp]
theorem analyticAt_analytic_continuedL_iff (s : ℂ) :
    AnalyticAt ℂ T.analytic.continuedL s ↔
      AnalyticAt ℂ T.arithmetic.continuedL (s + (T.weight : ℂ) / 2) := by
  rw [T.analytic_continuedL]
  exact analyticAt_comp_iff_of_deriv_ne_zero (by fun_prop) (by simp)

/-- In the arithmetic normalization, the continued function agrees with the arithmetic
Dirichlet series on `Re s > 1 + w/2`. -/
theorem arithmetic_continuedL_eq_LSeries (hda : T.analytic.HasDirichletAgreement)
    (hm : Meromorphic T.analytic.completed) {s : ℂ} (hs : 1 + (T.weight : ℝ) / 2 < s.re) :
    T.arithmetic.continuedL s = LSeries T.arithmetic.coeff s := by
  have hlt : 1 < (s - (T.weight : ℂ) / 2).re := by
    have hd : ((T.weight : ℂ) / 2).re = (T.weight : ℝ) / 2 := by simp
    rw [sub_re, hd]
    linarith
  have heq := hda.continuedL_eq_LSeries hm hlt
  rwa [T.analytic_continuedL_apply, T.LSeries_analytic_coeff, sub_add_cancel] at heq

end TauCeti.LFunctions.NormalizationTranslation
