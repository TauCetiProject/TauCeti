/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gamma

/-!
# Density API for the Gamma distribution

This file connects the Gamma law to `HasPDF`, `pdf`, and the Radon--Nikodym derivative, allowing
consumers to pass between distributional and density formulations.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability

/-- The `ℝ≥0∞`-valued Gamma density is measurable. -/
theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) := by
  unfold gammaPDF
  exact (measurable_gammaPDFReal a r).ennreal_ofReal

/-- The Gamma density at a natural shape is the corresponding Erlang density formula. -/
theorem gammaPDFReal_nat_eq {k : ℕ} (hk : 1 ≤ k) {r x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal k r x = r ^ k / (k - 1).factorial * x ^ (k - 1) * Real.exp (-(r * x)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hpow : x ^ ((↑(j + 1) : ℝ) - 1) = x ^ j := by
    rw [Nat.cast_succ, add_sub_cancel_right, Real.rpow_natCast]
  rw [gammaPDFReal, ite_eq_left hx, Real.rpow_natCast, hpow,
    Nat.cast_succ, Real.Gamma_nat_eq_factorial, Nat.add_sub_cancel]

/-- Dividing the Erlang density of shape `k` and rate `r` by `r ^ k` leaves
`x ^ (k - 1) * exp (-(r * x)) / (k - 1)!`. -/
theorem gammaPDFReal_nat_div_pow {k : ℕ} (hk : 1 ≤ k) {r x : ℝ} (hr : r ≠ 0) (hx : 0 ≤ x) :
    gammaPDFReal k r x / r ^ k = x ^ (k - 1) * Real.exp (-(r * x)) / (k - 1).factorial := by
  rw [gammaPDFReal_nat_eq hk hx]
  have := Nat.factorial_pos (k - 1)
  field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a Gamma law has a density. -/
theorem hasPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- The density of a Gamma law is `gammaPDF`. -/
theorem pdf_eq_gammaPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    pdf X P =ᵐ[volume] gammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- The Radon--Nikodym derivative of a Gamma law is `gammaPDF`. -/
theorem rnDeriv_gammaMeasure (a r : ℝ) :
    (gammaMeasure a r).rnDeriv volume =ᵐ[volume] gammaPDF a r := by
  unfold gammaMeasure
  exact Measure.rnDeriv_withDensity volume (measurable_gammaPDF a r)

end TauCeti.Probability
