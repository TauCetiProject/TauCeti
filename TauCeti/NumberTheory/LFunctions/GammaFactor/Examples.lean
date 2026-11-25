/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order

/-!
# Gamma poles, reciprocal zeros and their multiplicities

The examples specialize the gamma-list API without assumptions on a completed L-function.
Repeated parameters and coincident real and complex factors each contribute their multiplicity.
-/

public section

open Complex

namespace TauCeti.LFunctions.AnalyticLFunctionData

open Classical in
/-- Two identical real factors and one complex factor have a triple pole at zero. -/
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 0}) (hC : d.gammaC = {0}) :
    meromorphicOrderAt d.gammaFactor 0 = -3 := by
  simpa [hR, hC, ← Multiset.cons_zero] using
    d.meromorphicOrderAt_gammaFactor_eq_neg_count 0

open Classical in
/-- The analytic reciprocal has a triple zero at the same coincident poles. -/
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 0}) (hC : d.gammaC = {0}) :
    analyticOrderAt d.invGammaFactor 0 = 3 := by
  simpa [hR, hC, ← Multiset.cons_zero] using
    d.analyticOrderAt_invGammaFactor_eq_count 0

open Classical in
/-- Native divisors distinguish the gamma pole from the reciprocal zero, with multiplicity. -/
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 0}) (hC : d.gammaC = {0}) :
    MeromorphicOn.divisor d.gammaFactor Set.univ 0 = -3 ∧
      MeromorphicOn.divisor d.invGammaFactor Set.univ 0 = 3 := by
  simp [d.divisor_gammaFactor_apply (Set.mem_univ 0),
    d.divisor_invGammaFactor_apply (Set.mem_univ 0), hR, hC, ← Multiset.cons_zero]

open Classical in
/-- Distinct shifts can share a pole: shifts zero and two both contribute at minus two. -/
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 2}) (hC : d.gammaC = 0) :
    meromorphicOrderAt d.gammaFactor (-2) = -2 ∧
      analyticOrderAt d.invGammaFactor (-2) = 2 := by
  simp [d.meromorphicOrderAt_gammaFactor_eq_neg_count,
    d.analyticOrderAt_invGammaFactor_eq_count, hR, hC, ← Multiset.cons_zero]

/-- Empty gamma lists give constant one and no divisor, including at zero. -/
example (d : AnalyticLFunctionData) (hR : d.gammaR = 0) (hC : d.gammaC = 0) (s : ℂ) :
    d.gammaFactor s = 1 ∧ d.invGammaFactor s = 1 ∧
      MeromorphicOn.divisor d.gammaFactor Set.univ s = 0 ∧
      MeromorphicOn.divisor d.invGammaFactor Set.univ s = 0 := by
  simp [gammaFactor_def, invGammaFactor_def,
    d.divisor_gammaFactor_apply (Set.mem_univ s),
    d.divisor_invGammaFactor_apply (Set.mem_univ s), hR, hC]

end TauCeti.LFunctions.AnalyticLFunctionData
