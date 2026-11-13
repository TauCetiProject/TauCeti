/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta

/-!
# The continued uncompleted function of the zeta record

Removing the archimedean factor from the Riemann zeta record gives Mathlib's
`riemannZeta` at every point. In particular the removable extension has value
`-1 / 2` at zero, rather than the zero of the raw product. At one the pole is
not removable and the chosen total representative is retained.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions

private theorem uncompletedProduct_riemannZetaData (s : ℂ) :
    riemannZetaData.uncompletedProduct s = completedRiemannZeta s / Gammaℝ s := by
  simp only [AnalyticLFunctionData.uncompletedProduct_def, riemannZetaData_conductor,
    PNat.one_coe, Nat.cast_one, one_cpow, one_mul, riemannZetaData_completed,
    AnalyticLFunctionData.invGammaFactor_def, riemannZetaData_gammaFactor, div_eq_mul_inv]

private theorem continuedL_eventuallyEq_riemannZeta (s : ℂ) :
    riemannZetaData.continuedL =ᶠ[𝓝[≠] s] riemannZeta := by
  have h0 : ∀ᶠ z : ℂ in 𝓝[≠] s, z ≠ 0 := by
    by_cases hs : s = 0
    · subst s
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds hs)
  filter_upwards [riemannZetaData_hasMeromorphicContinuation.continuedL_eventuallyEq s, h0]
    with z hz hz0
  rw [hz, uncompletedProduct_riemannZetaData, riemannZeta_def_of_ne_zero hz0]

/-- Removing the conductor and gamma factors from the zeta record recovers the
native Riemann zeta function, including the removable value at zero. -/
@[simp]
theorem riemannZetaData_continuedL : riemannZetaData.continuedL = riemannZeta := by
  funext s
  have heq := continuedL_eventuallyEq_riemannZeta s
  by_cases hs : s = 1
  · subst s
    rw [riemannZetaData_hasMeromorphicContinuation.continuedL_eq_of_gammaFactor_ne_zero
      (by rw [riemannZetaData_gammaFactor, Gammaℝ_one]; exact one_ne_zero)]
    rw [uncompletedProduct_riemannZetaData, riemannZeta_def_of_ne_zero one_ne_zero]
  · exact riemannZetaData_hasMeromorphicContinuation.continuedL_eq_of_eventuallyEq
      (analyticOn_riemannZeta s hs) heq

-- The cancelled pole at zero is filled with the genuine value of zeta, not zero.
example : riemannZetaData.continuedL 0 = -1 / 2 := by
  simp [riemannZeta_zero]

end TauCeti.LFunctions
