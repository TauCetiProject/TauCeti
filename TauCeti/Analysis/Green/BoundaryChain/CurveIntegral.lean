/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Basic
public import TauCeti.Analysis.Green.Basic

/-!
# Gauge-chain and Bochner curve integrals

When the circulation integrand is genuinely Bochner integrable on every supported arc,
the sum of the two gauge coordinate integrals agrees with the integer-weighted sum of
Mathlib's existing `curveIntegral`. Gauge integrability of the individual coordinates is
retained, so no conditional gauge value is replaced by a junk-valued Bochner integral.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.BoundaryChain

/-- Genuine arcwise Bochner integrability identifies gauge circulation with the sum of
Mathlib curve integrals, even when only the combined circulation is Bochner integrable. -/
theorem integral_add_eq_curveIntegral {P Q : ℂ → ℝ} {c : BoundaryChain}
    (hP : Integrable Complex.reCLM P c) (hQ : Integrable Complex.imCLM Q c)
    (hc : ∀ γ ∈ c.support,
      IntervalIntegrable (circulationFun P Q γ.2.2.extend) volume 0 1) :
    integral Complex.reCLM P c + integral Complex.imCLM Q c =
      Finsupp.linearCombination ℤ (fun γ : Arc ↦ curveIntegral (oneForm P Q) γ.2.2) c := by
  rw [integral_apply, integral_apply, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, ← Finset.sum_add_distrib, ← smul_add]
  apply Finset.sum_congr rfl
  intro γ hγ
  congr 1
  rw [curveIntegral_oneForm_eq]
  have h := (hP.hasIntegral hγ).add (hQ.hasIntegral hγ)
  have hi : BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ circulationFun P Q γ.2.2.extend (t 0))
      BoxIntegral.BoxAdditiveMap.volume
      (arcIntegral Complex.reCLM P γ + arcIntegral Complex.imCLM Q γ) := by
    simpa only [circulationFun, Complex.reCLM_apply, Complex.imCLM_apply, Pi.add_def] using h
  exact hi.unique ((hc γ hγ).hasBoxIntegral zero_lt_one BoxIntegral.IntegrationParams.Henstock rfl)

end TauCeti.Green.BoundaryChain
