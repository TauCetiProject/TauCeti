/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GraphPlanDensity

/-!
# The Wasserstein distance as a Monge infimum

On a Polish metric space, the `p`-th power of the Wasserstein distance from an atomless law with
finite `p`-moment is a Monge infimum over transport maps, for every finite nonzero exponent `p`
(`TauCeti.wassersteinEDist_rpow_eq_mongeCost`). The cost `edist x y ^ p` has the integrable split
upper envelope `K * (edist x₀ x ^ p + edist x₀ y ^ p)` when both laws have finite `p`-moment, so
this is a corollary of `TauCeti.mongeCost_eq_transportCost_of_le_split`. No moment is needed on
the target: if it has none, both sides are `∞`.

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

/-- **The Wasserstein distance is a Monge infimum.** For an atomless source law with finite
`p`-moment on a Polish metric space, the `p`-th power of the Wasserstein distance to any
probability law is the infimum of `∫⁻ x, edist x (T x) ^ p ∂μ` over the transport maps `T`, for
every finite nonzero exponent `p`. -/
theorem wassersteinEDist_rpow_eq_mongeCost {p : ℝ≥0∞} {ν : Measure X} [IsProbabilityMeasure ν]
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hμ : HasFiniteMoment p μ) :
    wassersteinEDist p μ ν ^ p.toReal =
      mongeCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν := by
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  rw [wassersteinEDist_rpow_eq_transportCost hd hp0 hp]
  by_cases hν : HasFiniteMoment p ν
  swap
  · have hW : wassersteinEDist p μ ν = ∞ := by
      by_contra h
      exact hν ((hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd hμ).2 h)
    have htop : transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν = ∞ := by
      rw [← wassersteinEDist_rpow_eq_transportCost hd hp0 hp, hW,
        ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp0 hp)]
    rw [htop, eq_comm, ← top_le_iff, ← htop]
    exact transportCost_le_mongeCost _ _ _
  obtain ⟨x₀, -⟩ := hasFiniteMoment_def.1 hμ
  set K := ENNReal.LpAddConst (ENNReal.ofReal p.toReal)⁻¹
  have hK : K ≠ ∞ := (ENNReal.LpAddConst_lt_top _).ne
  have hint {ρ : Measure X} [IsProbabilityMeasure ρ] (hρ : HasFiniteMoment p ρ) :
      ∫⁻ x, K * edist x₀ x ^ p.toReal ∂ρ ≠ ∞ := by
    rw [lintegral_const_mul' _ _ hK]
    exact ENNReal.mul_ne_top hK
      ((hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp x₀ ρ).1 hρ)
  have hm : Measurable fun x : X ↦ K * edist x₀ x ^ p.toReal :=
    (measurable_edist_right.pow_const _).const_mul _
  have hc : Continuous fun z : X × X ↦ edist z.1 z.2 ^ p.toReal :=
    ENNReal.continuous_rpow_const.comp continuous_edist
  refine (mongeCost_eq_transportCost_of_le_split (c := fun z : X × X ↦ edist z.1 z.2 ^ p.toReal)
    hc hm.aemeasurable hm.aemeasurable (hint hμ) (hint hν) fun z ↦ ?_).symm
  calc edist z.1 z.2 ^ p.toReal ≤ (edist x₀ z.1 + edist x₀ z.2) ^ p.toReal := by
        gcongr
        exact edist_triangle_left _ _ _
    _ ≤ K * (edist x₀ z.1 ^ p.toReal + edist x₀ z.2 ^ p.toReal) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ ENNReal.toReal_nonneg
    _ = K * edist x₀ z.1 ^ p.toReal + K * edist x₀ z.2 ^ p.toReal := mul_add _ _ _

end TauCeti
