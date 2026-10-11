/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Changing the reference measure of a relative entropy

For measures `γ ≪ π ≪ R`, the Radon–Nikodym chain rule `dγ/dR = dγ/dπ · dπ/dR` turns into an
additive rule for log-likelihood ratios, `llr γ R = llr γ π + llr π R` almost everywhere with
respect to `γ`. Integrating it against `γ` relates the relative entropies of `γ` against the two
references `R` and `π`, up to the term `∫ llr π R dγ`. When this term equals its value
`∫ llr π R dπ` at `γ = π`, the relation is **Csiszár's Pythagorean identity**
`klDiv γ R = klDiv γ π + klDiv π R`.

The typical use is to identify an I-projection: if `π` belongs to a family of measures and
`log (dπ/dR)` integrates to the same value against every member `γ ≪ π` of the family, then the
identity shows at once that `π` minimises `klDiv · R` over the family. In entropic optimal
transport the family is the set of couplings of two fixed marginals and `log (dπ/dR)` is a sum
`φ(x) + ψ(y)` of two potentials, whose integral depends on a coupling only through its
marginals.

## Main statements

* `TauCeti.llr_withDensity_exp`: the log-likelihood ratio of `R.withDensity (exp ∘ f)` against
  `R` is `f`.
* `TauCeti.llr_add_llr`: the chain rule `llr γ π + llr π R = llr γ R`, `γ`-almost everywhere.
* `TauCeti.klDiv_eq_klDiv_add_klDiv`: the Pythagorean identity.

## References

* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probab. 3 (1975), 146–158.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {γ π R : Measure α}

/-- The log-likelihood ratio of the measure with density `exp ∘ f` with respect to `R` is `f`,
almost everywhere. -/
theorem llr_withDensity_exp [SigmaFinite R] {f : α → ℝ} (hf : AEMeasurable f R) :
    llr (R.withDensity fun x ↦ ENNReal.ofReal (Real.exp (f x))) R =ᵐ[R] f := by
  filter_upwards [Measure.rnDeriv_withDensity₀ R (f := fun x ↦ ENNReal.ofReal (Real.exp (f x)))
    (by fun_prop)] with x hx
  simp [llr_def, hx, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **Chain rule for log-likelihood ratios.** If `γ ≪ π ≪ R`, then
`llr γ π + llr π R = llr γ R`, `γ`-almost everywhere. -/
theorem llr_add_llr [SigmaFinite γ] [SigmaFinite π] [SigmaFinite R] (hγπ : γ ≪ π)
    (hπR : π ≪ R) : llr γ π + llr π R =ᵐ[γ] llr γ R := by
  have hγR := hγπ.trans hπR
  filter_upwards [hγR.ae_le (Measure.rnDeriv_mul_rnDeriv hγπ), Measure.rnDeriv_pos hγπ,
    hγπ.ae_le (Measure.rnDeriv_lt_top γ π), hγπ.ae_le (Measure.rnDeriv_pos hπR),
    hγR.ae_le (Measure.rnDeriv_lt_top π R)] with x hx h₁ h₂ h₃ h₄
  rw [Pi.mul_apply] at hx
  simp only [Pi.add_apply, llr_def, ← hx, ENNReal.toReal_mul]
  exact (Real.log_mul (ENNReal.toReal_pos h₁.ne' h₂.ne).ne'
    (ENNReal.toReal_pos h₃.ne' h₄.ne).ne').symm

/-- **Csiszár's Pythagorean identity.** Let `γ ≪ π ≪ R` be finite measures such that `llr π R` is
integrable against both `γ` and `π`, with the same integral. Then
`klDiv γ R = klDiv γ π + klDiv π R`. -/
theorem klDiv_eq_klDiv_add_klDiv [IsFiniteMeasure γ] [IsFiniteMeasure π] [IsFiniteMeasure R]
    (hγπ : γ ≪ π) (hπR : π ≪ R) (hγ : Integrable (llr π R) γ) (hπ : Integrable (llr π R) π)
    (h : ∫ x, llr π R x ∂γ = ∫ x, llr π R x ∂π) :
    klDiv γ R = klDiv γ π + klDiv π R := by
  have hγR := hγπ.trans hπR
  have hchain := llr_add_llr hγπ hπR
  by_cases hint : Integrable (llr γ π) γ
  swap
  · have hint' : ¬ Integrable (llr γ R) γ := fun h' ↦
      hint <| (integrable_add_iff_integrable_left' hγ).1 <| (integrable_congr hchain).2 h'
    simp [klDiv_of_not_integrable hint, klDiv_of_not_integrable hint']
  have hint' : Integrable (llr γ R) γ := (integrable_congr hchain).1 (hint.add hγ)
  rw [klDiv_of_ac_of_integrable hγR hint', klDiv_of_ac_of_integrable hγπ hint,
    klDiv_of_ac_of_integrable hπR hπ, ← ENNReal.ofReal_add
      (integral_llr_add_sub_measure_univ_nonneg hγπ hint)
      (integral_llr_add_sub_measure_univ_nonneg hπR hπ),
    ← integral_congr_ae hchain, Pi.add_def, integral_add hint hγ, h]
  ring_nf

end TauCeti
