/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quadratic

/-!
# Brenier's theorem for the quadratic Wasserstein distance

This module bridges Brenier's theorem for the half-squared-norm cost in
`TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic` to the quadratic Wasserstein distance
`TauCeti.wassersteinEDist 2` and cost `edist ^ 2` from
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic`.

## Main statements

* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_isCCRegular` — on a finite-dimensional real
  inner product space, every optimal plan for `edist ^ 2` out of a finite `c - c`-regular source
  into a law at finite `W₂` distance is the graph plan of a measurable transport map.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Brenier's theorem for the cost `edist ^ 2`.** On a finite-dimensional real inner product
space, an optimal plan for the cost `edist ^ 2` out of a finite measure `μ` that is `c - c`-regular,
to a law at finite `W₂` distance from `μ`, is the graph plan of a measurable map. -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_isCCRegular {μ ν : Measure E}
    [IsFiniteMeasure μ] (hμ : IsCCRegular μ) {π : Measure (E × E)}
    (h : IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) π μ ν)
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    ∃ T : E → E, Measurable T ∧ π = graphPlan T μ :=
  let ⟨_, _, _, _, _, hgraph⟩ := (isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two h)
    |>.exists_eq_graphPlan_gradient hμ
      (transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top hfin)
  ⟨_, measurable_gradient _, hgraph⟩

end TauCeti
