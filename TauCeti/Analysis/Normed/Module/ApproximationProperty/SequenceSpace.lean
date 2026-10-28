/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Basis
public import TauCeti.Analysis.Normed.Module.Bases.Approximation
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basis

/-!
# Metric approximation of sequence spaces

The spaces `ℓ^p(ι, 𝕜)` for `1 ≤ p < ∞` and `C₀(ι, 𝕜)` for discrete `ι` have the metric
approximation property. Their canonical unconditional bases have contractive finite
projections, so pointwise coordinate expansion gives uniform approximation on compact sets.
The statements allow arbitrary index types and do not require completeness of the field.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open scoped lp ZeroAtInfty ENNReal

namespace TauCeti

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Every scalar `lp` space with `1 ≤ p < ∞` has the metric approximation property. -/
theorem hasMetricApproximationProperty_lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    HasMetricApproximationProperty 𝕜 ℓ^p(ι, 𝕜) := by
  classical
  exact (lp.unconditionalBasis hp).hasMetricApproximationProperty
    (lp.norm_unconditionalBasis_proj_le hp)

/-- The space of scalar families vanishing at infinity on a discrete index type has the
metric approximation property. -/
theorem hasMetricApproximationProperty_zeroAtInfty [TopologicalSpace ι] [DiscreteTopology ι] :
    HasMetricApproximationProperty 𝕜 C₀(ι, 𝕜) := by
  classical
  exact ZeroAtInftyContinuousMap.unconditionalBasis.hasMetricApproximationProperty
    ZeroAtInftyContinuousMap.norm_unconditionalBasis_proj_le

end TauCeti
