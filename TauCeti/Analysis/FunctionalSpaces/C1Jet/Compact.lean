/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.C1Jet.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Compact value map for C¹ jets

On a compact convex set, a bounded family of C¹ jets has uniformly Lipschitz value components.
For a proper target space, Arzelà–Ascoli therefore makes the value map into continuous
maps a compact operator. In particular this applies to real and complex scalar-valued jets.
This supplies the compact inclusion used in two-norm spectral estimates for transfer operators.

No finite-dimensionality or nonempty-interior assumption on the domain is needed: the segment
identity already gives the Lipschitz estimate, even when derivatives are not uniquely determined
by values.

## References

* A. Gamburd, M. Magee and R. Ronan, *An asymptotic formula for integer points on
  Markoff–Hurwitz varieties*, Ann. of Math. 190 (2019), footnote 21, p.794.
-/

public section

noncomputable section

open Set Metric

namespace TauCeti.C1Jet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} [CompactSpace K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

/-- Bounded families of jets on a convex set have equicontinuous value components. -/
theorem equicontinuous_value (hK : Convex ℝ K) {S : Set (C1Jet 𝕜 K V)}
    (hS : Bornology.IsBounded S) : Equicontinuous (fun j : S ↦ ⇑j.val.value) := by
  obtain ⟨R, hR, hbound⟩ := hS.exists_pos_norm_le
  exact (LipschitzWith.uniformEquicontinuous _ ⟨R, hR.le⟩ fun j ↦
    (j.val.lipschitzWith_value hK).weaken
      (j.val.norm_deriv_le.trans (hbound j.val j.property))).equicontinuous

/-- On a compact convex set, the value map of jets with values in a proper normed space
is compact. This includes both real and complex scalar-valued jets. -/
theorem isCompactOperator_valueCLM [ProperSpace V] (hK : Convex ℝ K) :
    IsCompactOperator (valueCLM 𝕜 K V) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (valueCLM 𝕜 K V).toLinearMap zero_lt_one).2
  have hc := ArzelaAscoli.isCompact_closure_range_of_equicontinuous
    (equicontinuous_value hK (isBounded_closedBall (x := (0 : C1Jet 𝕜 K V)) (r := 1)))
    (fun x ↦ ⟨closedBall (0 : V) 1, isCompact_closedBall _ _, fun j ↦ by
      simpa only [mem_closedBall, dist_zero_right] using
        (j.val.norm_value_apply_le x).trans (mem_closedBall_zero_iff.1 j.property)⟩)
  simpa only [image_eq_range, ContinuousLinearMap.coe_coe, valueCLM_apply] using hc

end TauCeti.C1Jet
