/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Levy.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of the Lévy distribution

This file identifies the exact positivity sets of the real- and extended-nonnegative-valued Lévy
densities and the topological support of the Lévy measure. At positive scale the density is
positive exactly above the location, so the measure support also contains the location as the
boundary point. At nonpositive scale all three supports are empty, consistently with the
totalized zero-law convention.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer (2020),
  chapter 1.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The real-valued Lévy density is nonzero exactly above the location when the scale is
positive. -/
@[simp]
theorem support_levyPDFReal (m c : ℝ) :
    Function.support (levyPDFReal m c) = if 0 < c then Ioi m else ∅ := by
  by_cases hc : 0 < c
  · simp only [hc, ite_true]
    ext x
    rw [Function.mem_support]
    simp only [mem_Ioi]
    constructor
    · intro hx
      by_contra hxm
      exact hx (levyPDFReal_of_le (le_of_not_gt hxm) c)
    · intro hxm
      rw [levyPDFReal_of_lt hxm]
      positivity
  · simp only [hc, ite_false]
    ext x
    rw [Function.mem_support]
    simp [levyPDFReal_of_nonpos (not_lt.mp hc) m x]

/-- The extended-nonnegative-valued Lévy density is nonzero exactly above the location when the
scale is positive. -/
@[simp]
theorem support_levyPDF (m c : ℝ) :
    Function.support (levyPDF m c) = if 0 < c then Ioi m else ∅ := by
  ext x
  have hpos : 0 < levyPDFReal m c x ↔ levyPDFReal m c x ≠ 0 :=
    ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne (levyPDFReal_nonneg m c x) h.symm⟩
  rw [Function.mem_support, levyPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff, hpos,
    ← Function.mem_support, support_levyPDFReal]

/-- The topological support of a Lévy law is the closed upper half-line from its location at
positive scale and is empty for the totalized zero law at nonpositive scale. -/
@[simp]
theorem support_levyMeasure (m c : ℝ) :
    (levyMeasure m c).support = if 0 < c then Ici m else ∅ := by
  by_cases hc : 0 < c
  · simp only [hc, ite_true]
    have hsupp : Function.support (levyPDF m c) = Ioi m := by
      simp only [support_levyPDF, hc, ite_true]
    rw [levyMeasure_eq_withDensity,
      Measure.support_withDensity_eq_closure (measurable_levyPDF m c) isOpen_Ioi
        hsupp, closure_Ioi]
  · simp only [hc, ite_false]
    rw [levyMeasure_of_nonpos (not_lt.mp hc), Measure.support_zero]

end TauCeti.Probability
