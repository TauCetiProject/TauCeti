/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.AnalyticConductor.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Normalization
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta

/-!
# Normalization and the Riemann zeta analytic conductor

Shifting an arithmetic normalization of weight `w` to the analytic normalization translates
its conductor by `s ↦ s + w/2`. In particular, the analytic central point corresponds to the
arithmetic point `(w+1)/2`. For the Riemann zeta record the analytic conductor is `‖s‖ + 3`.
-/

public section

open Complex

namespace TauCeti.LFunctions

/-- Translation to the analytic normalization shifts the conductor's evaluation point by
`+w/2`, just as it shifts each gamma parameter. -/
@[simp]
theorem NormalizationTranslation.analytic_analyticConductorAt (T : NormalizationTranslation)
    (s : ℂ) :
    T.analytic.analyticConductorAt s =
      T.arithmetic.toAnalyticLFunctionData.analyticConductorAt (s + (T.weight : ℂ) / 2) := by
  simp [AnalyticLFunctionData.analyticConductorAt_def, Multiset.map_map,
    ← add_assoc, add_right_comm s]

/-- The analytic central point corresponds to the arithmetic central point `(w+1)/2`. -/
@[simp]
theorem NormalizationTranslation.analytic_centralAnalyticConductor (T : NormalizationTranslation) :
    T.analytic.centralAnalyticConductor =
      T.arithmetic.toAnalyticLFunctionData.analyticConductorAt (((T.weight : ℂ) + 1) / 2) := by
  rw [AnalyticLFunctionData.centralAnalyticConductor_def, T.analytic_analyticConductorAt]
  congr 1
  ring

/-- The analytic conductor of the Riemann zeta function. -/
@[simp]
theorem riemannZetaData_analyticConductorAt (s : ℂ) :
    riemannZetaData.analyticConductorAt s = ‖s‖ + 3 := by
  simp [AnalyticLFunctionData.analyticConductorAt_def]

/-- In the offset-three convention the central conductor of zeta is `7/2`. -/
@[simp]
theorem riemannZetaData_centralAnalyticConductor :
    riemannZetaData.centralAnalyticConductor = 7 / 2 := by
  norm_num [AnalyticLFunctionData.centralAnalyticConductor_def]

-- A complex gamma factor must contribute two distinct shifts, including in degree two.
example (d : AnalyticLFunctionData) (k : ℂ) (hR : d.gammaR = 0)
    (hC : d.gammaC = {(k - 1) / 2}) (s : ℂ) :
    d.analyticConductorAt s = (d.conductor : ℝ) *
      (‖s + (k - 1) / 2‖ + 3) * (‖s + (k + 1) / 2‖ + 3) := by
  have hshift : s + (k - 1) / 2 + 1 = s + (k + 1) / 2 := by ring
  simp [AnalyticLFunctionData.analyticConductorAt_def, hR, hC, hshift, mul_assoc]

end TauCeti.LFunctions
