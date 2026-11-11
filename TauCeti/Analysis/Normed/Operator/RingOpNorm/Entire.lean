/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Entire evaluation along a continuous linear retract

If `r ∘ i = id`, extending an endomorphism `u` along the retract gives `i ∘ u ∘ r`.
Evaluating an entire function with zero constant coefficient commutes with this extension.
The constant coefficient condition is essential: the extension of the identity is `i ∘ r`,
not necessarily the identity of the larger module.

This is the analytic counterpart of `ContinuousLinearMap.aeval_comp_comp_of_retract`.
It uses the ring-scalar operator norm and applies without a norm-one or ultrametric assumption.
-/

public section

open Filter Topology
open scoped TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [CompleteSpace N]

/-- Extending an endomorphism along a continuous linear retract commutes with evaluating an
entire series with zero constant coefficient. The extension need not be unital. -/
theorem evalAt_comp_comp_of_retract {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {B : R⟦X⟧}
    (hB : B.IsEntire) (hB₀ : PowerSeries.coeff 0 B = 0) :
    B.evalAt (i.comp (u.comp r)) = i.comp ((B.evalAt u).comp r) := by
  have hleft := (hB.tendsto_aeval_trunc (i.comp (u.comp r))).comp
    (tendsto_add_atTop_nat 1)
  have hright := ((lipschitzWith_comp_comp i r).continuous.tendsto (B.evalAt u)).comp
    ((hB.tendsto_aeval_trunc u).comp (tendsto_add_atTop_nat 1))
  apply tendsto_nhds_unique hleft
  exact hright.congr fun n ↦ (aeval_comp_comp_of_retract hri u
    (by simp [PowerSeries.coeff_trunc, hB₀])).symm

end ContinuousLinearMap
