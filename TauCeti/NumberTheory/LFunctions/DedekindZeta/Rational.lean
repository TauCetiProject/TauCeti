/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta

/-!
# Comparison over `ℚ` with the Riemann zeta function

Over `K = ℚ`, this file identifies the completed Dedekind zeta function
`TauCeti.LFunctions.completedDedekindZeta ℚ` with the meromorphic normal form of Mathlib's
`completedRiemannZeta` (and hence pointwise away from the poles `0` and `1`), and compares
`TauCeti.LFunctions.dedekindZetaData ℚ` with `TauCeti.LFunctions.riemannZetaData` off index zero.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_rat_eq_toMeromorphicNFOn`: `completedDedekindZeta ℚ`
  equals `toMeromorphicNFOn completedRiemannZeta Set.univ`.
* `TauCeti.LFunctions.completedDedekindZeta_rat_eq`: pointwise agreement away from `0` and `1`.
* `TauCeti.LFunctions.dedekindZetaData_rat_eqOffZero`: `AnalyticLFunctionData.EqOffZero` comparison
  between `dedekindZetaData ℚ` and the normal-form version of `riemannZetaData`.
-/

public section
noncomputable section

open Complex NumberField NumberField.InfinitePlace Set

namespace TauCeti.LFunctions

/-- Over `ℚ`, `completedDedekindZeta ℚ` is the meromorphic normal form of
`completedRiemannZeta`. -/
theorem completedDedekindZeta_rat_eq_toMeromorphicNFOn :
    completedDedekindZeta ℚ = toMeromorphicNFOn completedRiemannZeta univ := by
  refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (meromorphicNFOn_completedDedekindZeta ℚ)
    (meromorphicNFOn_toMeromorphicNFOn _ _) fun s (hs : 1 < s.re) ↦ ?_
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hGℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
      (analyticAt_completedRiemannZeta h0 h1)]
  rw [completedDedekindZeta_eq_mul_dedekindZeta ℚ hs, dedekindZeta_rat_eq_riemannZeta hs,
    riemannZeta_def_of_ne_zero h0]
  simp only [discr_rat, nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    abs_one, Int.cast_one, Complex.one_cpow, pow_one, pow_zero, one_mul, mul_one]
  exact mul_div_cancel₀ _ hGℝ

/-- Over `ℚ`, `completedDedekindZeta ℚ` agrees with Mathlib's `completedRiemannZeta` away from
its poles `0` and `1`. -/
theorem completedDedekindZeta_rat_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s := by
  rw [completedDedekindZeta_rat_eq_toMeromorphicNFOn]
  exact toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
    (analyticAt_completedRiemannZeta h0 h1)

/-- Over `ℚ`, `dedekindZetaData ℚ` agrees off index zero with the normal-form version of
`riemannZetaData`. The two differ at index zero because `dedekindZetaCoeff ℚ 0 = 1` whereas
`ArithmeticFunction.zeta 0 = 0`. -/
theorem dedekindZetaData_rat_eqOffZero :
    (dedekindZetaData ℚ).EqOffZero
      { riemannZetaData with completed := toMeromorphicNFOn completedRiemannZeta univ } where
  coeff_eq n hn := by simp [hn]
  conductor_eq := by
    apply PNat.eq
    simp
  gammaR_eq := by
    simp [nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)]
  gammaC_eq := by simp
  rootNumber_eq := by simp
  completed_eq := by simp [completedDedekindZeta_rat_eq_toMeromorphicNFOn]
  polarOrder_eq := by simp

end TauCeti.LFunctions
