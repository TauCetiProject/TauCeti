/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrals of continuous functions on a compact space

On a compact space `X`, every continuous function is integrable against a finite measure
(`ContinuousMap.integrable`), and integration against a finite measure is Lipschitz, hence
continuous, in the integrand for the sup norm on `C(X, E)`. This is what lets an identity between
integrals pass from a dense subset of `C(X, E)` to all of it.
-/

public section

open MeasureTheory Set

/-- On a compact space, a continuous function is integrable against every finite measure. -/
theorem ContinuousMap.integrable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E] (f : C(X, E))
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a compact space, integration against a finite measure is a continuous function of the
integrand for the topology of uniform convergence on `C(X, E)`. -/
theorem continuous_integral_continuousMap {μ : Measure X} [IsFiniteMeasure μ] :
    Continuous fun f : C(X, E) ↦ ∫ x, f x ∂μ := by
  refine (LipschitzWith.of_dist_le_mul (K := (μ.real univ).toNNReal) fun f g ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ measureReal_nonneg, mul_comm,
    ← integral_sub (f.integrable μ) (g.integrable μ)]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)

end TauCeti
