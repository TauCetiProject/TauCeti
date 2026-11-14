/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.TaylorSeries
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Taylor expansion under a power substitution

For a function analytic at zero, substitution of `z ^ d` in the function expands the
exponents of its Taylor series by `d`. This identifies analytic and formal power
substitutions, including at ramification points where the derivative of the substitution
vanishes. The proof uses the divided-difference decomposition of an analytic function.

## Main results

* `TauCeti.taylorSeries_comp_pow`: Taylor expansion commutes with a positive power substitution.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §1 (local power series).
-/

public noncomputable section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜}

/-- Substitution of `z ^ d` in an analytic function expands every Taylor exponent by `d`.
The positivity hypothesis excludes constant substitution. -/
theorem taylorSeries_comp_pow (hf : AnalyticAt 𝕜 f 0) (d : ℕ) (hd : d ≠ 0) :
    taylorSeries (fun z ↦ f (z ^ d)) 0 = PowerSeries.expand d hd (taylorSeries f 0) := by
  have recurrence (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g 0) :
      taylorSeries (fun z ↦ g (z ^ d)) 0 = PowerSeries.C (g 0) +
        PowerSeries.X ^ d * taylorSeries (fun z ↦ dslope g 0 (z ^ d)) 0 := by
    have h : (fun z ↦ g (z ^ d)) =
        (fun _ ↦ g 0) + (fun z ↦ z - 0) ^ d * (fun z ↦ dslope g 0 (z ^ d)) := by
      funext z
      have hz := sub_smul_dslope g 0 (z ^ d)
      simp only [sub_zero, smul_eq_mul] at hz
      simpa using (eq_add_of_sub_eq' hz.symm)
    have hc : AnalyticAt 𝕜 (fun z : 𝕜 ↦ z - 0) 0 := by fun_prop
    have hp : AnalyticAt 𝕜 (fun z : 𝕜 ↦ z ^ d) 0 := by fun_prop
    have ht : AnalyticAt 𝕜 (fun z ↦ dslope g 0 (z ^ d)) 0 :=
      (hg.dslope 0).comp_of_eq hp (zero_pow hd)
    rw [h, taylorSeries_add analyticAt_const ((hc.pow d).mul ht), taylorSeries_const,
      taylorSeries_mul (hc.pow d) ht, taylorSeries_pow hc, taylorSeries_sub_const]
  ext n
  induction n using Nat.strong_induction_on generalizing f with
  | ind n ih =>
    rw [recurrence f hf, taylorSeries_eq_C_add_X_mul hf, map_add (PowerSeries.expand d hd),
      map_mul (PowerSeries.expand d hd),
      PowerSeries.expand_C, PowerSeries.expand_X]
    simp only [map_add, PowerSeries.coeff_X_pow_mul']
    by_cases hn : d ≤ n
    · simp only [hn, ↓reduceIte]
      rw [ih (n - d) (by omega) (hf.dslope 0)]
    · simp [hn]

end TauCeti
