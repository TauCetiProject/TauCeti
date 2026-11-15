/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Order.BigOperators.Sum.Filter
public import TauCeti.Probability.Distributions.Beta.Quantile
public import TauCeti.Probability.Distributions.Dirichlet.Marginal
public import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of Dirichlet coordinates

A coordinate of a Dirichlet vector with at least two coordinates has a Beta law. Its lower
quantile is therefore the inverse regularized incomplete Beta function, with shapes given by
that coordinate's concentration and the sum of the other concentrations. The one-coordinate
law is instead constant at one; it must not be treated as a Beta law with zero second shape.

This file gives these scalar quantiles and their one-sided endpoint limits. For at least two
coordinates the endpoints are zero and one; for one coordinate both endpoints are one.

The formulas use `map_eval_dirichletMeasure`, `quantile_betaMeasure`, and the existing
one-coordinate Dirac identity.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {a : ι → ℝ}

/-- An interior quantile of a Dirichlet coordinate is the inverse regularized incomplete Beta
function with that coordinate's concentration and the total of the other concentrations. -/
@[simp]
theorem quantile_map_eval_dirichletMeasure [DecidableEq ι] [Nontrivial ι]
    (ha : ∀ i, 0 < a i) (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((dirichletMeasure a).map (fun x ↦ x i)).quantile u =
      inverseRegularizedIncompleteBeta (a i) (∑ j with j ≠ i, a j) u := by
  rw [map_eval_dirichletMeasure ha i,
    quantile_betaMeasure (ha i) (Finset.sum_filter_ne_pos ha i) hu]

/-- A Dirichlet law with one coordinate has constant interior coordinate quantile one. -/
@[simp]
theorem quantile_map_eval_dirichletMeasure_of_card_eq_one (ha : ∀ i, 0 < a i)
    (hcard : Fintype.card ι = 1) (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((dirichletMeasure a).map (fun x ↦ x i)).quantile u = 1 := by
  rw [dirichletMeasure_eq_dirac_of_card_eq_one ha hcard,
    Measure.map_dirac' (by fun_prop), Measure.quantile_dirac _ hu.1 hu.2.le]
  simp

/-- At level zero the coordinate quantile tends to zero, except for a one-coordinate
Dirichlet law, whose quantile is constantly one. -/
theorem tendsto_quantile_map_eval_dirichletMeasure_nhdsGT_zero (ha : ∀ i, 0 < a i)
    (i : ι) :
    Tendsto ((dirichletMeasure a).map (fun x ↦ x i)).quantile (𝓝[>] 0)
      (𝓝 (if Fintype.card ι = 1 then 1 else 0)) := by
  classical
  rcases subsingleton_or_nontrivial ι with _ | _
  · let : Unique ι := uniqueOfSubsingleton i
    have hcard : Fintype.card ι = 1 := Fintype.card_unique
    simp only [hcard, ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with u hu
    exact (quantile_map_eval_dirichletMeasure_of_card_eq_one ha hcard i hu).symm
  · rw [ite_eq_right (ne_of_gt Fintype.one_lt_card), map_eval_dirichletMeasure ha i]
    exact tendsto_quantile_betaMeasure_nhdsGT_zero (ha i) (Finset.sum_filter_ne_pos ha i)

/-- At level one every valid Dirichlet coordinate quantile tends to one, including the
constant coordinate of a one-coordinate law. -/
theorem tendsto_quantile_map_eval_dirichletMeasure_nhdsLT_one (ha : ∀ i, 0 < a i)
    (i : ι) :
    Tendsto ((dirichletMeasure a).map (fun x ↦ x i)).quantile (𝓝[<] 1) (𝓝 1) := by
  classical
  rcases subsingleton_or_nontrivial ι with _ | _
  · let : Unique ι := uniqueOfSubsingleton i
    have hcard : Fintype.card ι = 1 := Fintype.card_unique
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with u hu
    exact (quantile_map_eval_dirichletMeasure_of_card_eq_one ha hcard i hu).symm
  · rw [map_eval_dirichletMeasure ha i]
    exact tendsto_quantile_betaMeasure_nhdsLT_one (ha i) (Finset.sum_filter_ne_pos ha i)

end TauCeti.Probability
