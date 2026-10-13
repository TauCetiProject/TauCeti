/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Basic
public import TauCeti.Analysis.Green.Basic
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Gauge-chain and Bochner curve integrals

When the circulation integrand is genuinely Bochner integrable on every supported arc,
the sum of the two gauge coordinate integrals agrees with the integer-weighted sum of
Mathlib's existing `curveIntegral`. Gauge integrability of the individual coordinates is
retained, so no conditional gauge value is replaced by a junk-valued Bochner integral.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Green.BoundaryChain

/-- Continuous coefficients are genuinely Bochner integrable along a straight segment. -/
theorem intervalIntegrable_circulationFun_segment {p q : ℂ} {P Q : ℂ → ℝ}
    (hP : ContinuousOn P (segment ℝ p q)) (hQ : ContinuousOn Q (segment ℝ p q)) :
    IntervalIntegrable (circulationFun P Q (Path.segment p q).extend) volume 0 1 := by
  have hc : CurveIntegrable (oneForm P Q) (Path.segment p q) := by
    rw [curveIntegrable_segment]
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hm : Set.MapsTo (AffineMap.lineMap p q) (Set.Icc (0 : ℝ) 1) (segment ℝ p q) :=
      fun _ ht ↦ (convex_segment p q).lineMap_mem (left_mem_segment ℝ p q)
        (right_mem_segment ℝ p q) ht
    have hp := hP.comp (by fun_prop) hm
    have hq := hQ.comp (by fun_prop) hm
    simpa only [oneForm_apply, Pi.add_def, Pi.mul_def, Function.comp_apply] using
      (hp.mul continuousOn_const).add (hq.mul continuousOn_const)
  rw [curveIntegrable_iff_intervalIntegrable_deriv] at hc
  simpa only [← circulationFun_eq_oneForm] using hc

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
  have hi : BoxIntegral.HasIntegral (BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ circulationFun P Q γ.2.2.extend (t 0))
      BoxIntegral.BoxAdditiveMap.volume
      (arcIntegral Complex.reCLM P γ + arcIntegral Complex.imCLM Q γ) := by
    simpa only [circulationFun_def, Complex.reCLM_apply, Complex.imCLM_apply, Pi.add_def] using h
  exact hi.eq_intervalIntegral (hc γ hγ) rfl

end TauCeti.Green.BoundaryChain
