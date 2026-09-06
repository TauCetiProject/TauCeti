/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Moment-generating functions of sums of coordinates under a product measure

A statistic of the form `x ↦ ∑ j, f j (x j)` under a finite product measure `Measure.pi μ` has
exponential `∏ j, exp (t * f j (x j))`, so Fubini's theorem turns its moment-generating function
into the product of the coordinate ones. Since each factor is positive exactly on its
exponential-integrability domain, the domain of the sum is the intersection of the domains of
the coordinates.

These are the facts that turn a quadratic statistic of a Gaussian vector, written in
eigen-coordinates, into a product of one-dimensional moment-generating functions.

## Main results

* `ProbabilityTheory.mgf_sum_pi` — the moment-generating function of a sum of coordinate
  statistics factors over the coordinates, for every argument;
* `ProbabilityTheory.integrableExpSet_sum_pi` — its exponential-integrability domain is the
  intersection of the coordinate domains.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  {μ : ∀ i, Measure (E i)}

/-- Under a product measure the exponential of a sum of coordinate statistics factors over the
coordinates, so Fubini's theorem turns its integral into a product of one-dimensional
moment-generating functions. No integrability hypothesis is needed: off the common domain both
sides are zero. -/
theorem mgf_sum_pi [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ) (t : ℝ) :
    mgf (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) t = ∏ j, mgf (f j) (μ j) t := by
  simp only [mgf, Finset.mul_sum, Real.exp_sum]
  exact integral_fintype_prod_eq_prod fun j (u : E j) ↦ Real.exp (t * f j u)

/-- Under a product of probability measures, a sum of coordinate statistics has finite
exponential moments of order `t` exactly when every coordinate does. -/
theorem integrableExpSet_sum_pi [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, E i → ℝ) :
    integrableExpSet (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) =
      ⋂ j, integrableExpSet (f j) (μ j) := by
  ext t
  rw [Set.mem_iInter]
  have hpi : t ∈ integrableExpSet (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) ↔
      0 < ∏ j, mgf (f j) (μ j) t := by
    rw [← mgf_sum_pi]
    exact mgf_pos_iff.symm
  have hj (j : ι) : t ∈ integrableExpSet (f j) (μ j) ↔ 0 < mgf (f j) (μ j) t := mgf_pos_iff.symm
  simp only [hpi, hj]
  refine ⟨fun h j ↦ mgf_nonneg.lt_of_ne' fun hj ↦ ?_, fun h ↦ Finset.prod_pos fun j _ ↦ h j⟩
  exact absurd (Finset.prod_eq_zero (Finset.mem_univ j) hj) h.ne'

end ProbabilityTheory
