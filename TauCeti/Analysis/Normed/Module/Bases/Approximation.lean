/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Schauder bases give the bounded approximation property

The initial projections of a Schauder basis approximate the identity uniformly on norm-compact
sets. Their operator norms are bounded by the basis constant, so a Banach space with a Schauder
basis has the bounded approximation property with precisely that bound.

The same argument applies to unconditional bases, using the net of all finite coordinate
projections. For ordinary Schauder bases only initial segments are used; unconditional
convergence is not assumed. A basis whose relevant projections are contractions gives the
metric approximation property.

The finite projections, their ranges and their bounds come from Mathlib's
`GeneralSchauderBasis` API.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
-/

public section

open scoped NNReal Topology

variable {𝕜 E β : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

namespace GeneralSchauderBasis

/-- Each finite coordinate projection of a generalized Schauder basis has finite rank. -/
theorem hasFiniteRange_proj {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 E L)
    (A : Finset β) : (b.proj A).toLinearMap.HasFiniteRange := by
  rw [LinearMap.hasFiniteRange_iff_range, b.range_proj_eq_span]
  exact Submodule.fg_span (A.finite_toSet.image b)

end GeneralSchauderBasis

namespace SchauderBasis

/-- A uniformly bounded family of initial basis projections witnesses the bounded
approximation property, even without completeness. -/
theorem hasBoundedApproximationPropertyWith_of_bound (b : SchauderBasis 𝕜 E) {C : ℝ≥0}
    (hC : ∀ n, ‖b.proj n‖ ≤ C) : TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C :=
  .of_tendsto b.proj (fun n => b.hasFiniteRange_proj (Finset.range n)) hC b.tendsto_proj

/-- A Schauder basis of a Banach space gives the bounded approximation property with its
basis constant. -/
theorem hasBoundedApproximationPropertyWith (b : SchauderBasis 𝕜 E) [CompleteSpace E] :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 E b.nnnormProjBound :=
  b.hasBoundedApproximationPropertyWith_of_bound b.norm_proj_le_nnnormProjBound

/-- A Banach space with a Schauder basis has the bounded approximation property. -/
theorem hasBoundedApproximationProperty (b : SchauderBasis 𝕜 E) [CompleteSpace E] :
    TauCeti.HasBoundedApproximationProperty 𝕜 E :=
  b.hasBoundedApproximationPropertyWith.hasBoundedApproximationProperty

/-- A Schauder basis with contractive initial projections gives the metric approximation
property. -/
theorem hasMetricApproximationProperty (b : SchauderBasis 𝕜 E)
    (hb : ∀ n, ‖b.proj n‖ ≤ 1) : TauCeti.HasMetricApproximationProperty 𝕜 E := by
  apply TauCeti.hasMetricApproximationProperty_iff.mpr
  exact b.hasBoundedApproximationPropertyWith_of_bound (C := 1) hb

end SchauderBasis

namespace UnconditionalSchauderBasis

/-- Uniformly bounded finite coordinate projections of an unconditional basis witness the
bounded approximation property, without a countability assumption on the index type. -/
theorem hasBoundedApproximationPropertyWith_of_bound (b : UnconditionalSchauderBasis β 𝕜 E)
    {C : ℝ≥0} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C) :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C := by
  classical
  exact .of_tendsto b.proj b.hasFiniteRange_proj hC b.tendsto_proj

/-- An unconditional basis of a Banach space gives the bounded approximation property with
its unconditional basis constant. -/
theorem hasBoundedApproximationPropertyWith (b : UnconditionalSchauderBasis β 𝕜 E)
    [CompleteSpace E] : TauCeti.HasBoundedApproximationPropertyWith 𝕜 E b.nnnormProjBound :=
  b.hasBoundedApproximationPropertyWith_of_bound b.norm_proj_le_nnnormProjBound

/-- A Banach space with an unconditional Schauder basis has the bounded approximation
property. -/
theorem hasBoundedApproximationProperty (b : UnconditionalSchauderBasis β 𝕜 E)
    [CompleteSpace E] : TauCeti.HasBoundedApproximationProperty 𝕜 E :=
  b.hasBoundedApproximationPropertyWith.hasBoundedApproximationProperty

/-- An unconditional basis with contractive finite coordinate projections gives the metric
approximation property. -/
theorem hasMetricApproximationProperty (b : UnconditionalSchauderBasis β 𝕜 E)
    (hb : ∀ A : Finset β, ‖b.proj A‖ ≤ 1) : TauCeti.HasMetricApproximationProperty 𝕜 E := by
  apply TauCeti.hasMetricApproximationProperty_iff.mpr
  exact b.hasBoundedApproximationPropertyWith_of_bound (C := 1) hb

end UnconditionalSchauderBasis
