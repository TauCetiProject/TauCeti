/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Pratelli
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# The Wasserstein distance as a Monge infimum

On a Polish metric space, the `p`-th power of the Wasserstein distance from an atomless law is a
Monge infimum over transport maps, for every finite nonzero exponent `p`
(`TauCeti.wassersteinEDist_rpow_eq_mongeCost`). The cost `edist x y ^ p` is continuous, so this is
a corollary of Pratelli's theorem `TauCeti.mongeCost_eq_transportCost_of_continuous`. No moment
condition is needed: if a law has no finite `p`-moment, both sides may be `∞`.

## References

* A. Pratelli, *On the equality between Monge's infimum and Kantorovich's minimum in optimal mass
  transportation*, Ann. I. H. Poincaré Probab. Statist. 43 (2007), 1--13.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [PolishSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- **The Wasserstein distance is a Monge infimum.** For an atomless source law on a Polish metric
space, the `p`-th power of the Wasserstein distance to any measure is the infimum of
`∫⁻ x, edist x (T x) ^ p ∂μ` over the transport maps `T`, for every finite nonzero exponent
`p`. -/
theorem wassersteinEDist_rpow_eq_mongeCost {p : ℝ≥0∞} {ν : Measure X} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) :
    wassersteinEDist p μ ν ^ p.toReal =
      mongeCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  rw [wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp]
  exact (mongeCost_eq_transportCost_of_continuous
    (ENNReal.continuous_rpow_const.comp continuous_edist)).symm

end TauCeti
