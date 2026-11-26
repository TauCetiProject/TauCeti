/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Norming
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of the norm of an operator field

On a separable domain, measurability of the norm of each orbit implies measurability
of the operator norm. The almost everywhere version allows a different exceptional
null set for each vector. In particular, apply these results to strongly measurable
or almost everywhere strongly measurable orbits using their measurable norms.
Neither statement requires strong measurability of the field in the operator-norm topology.

The common sequence of unit-ball tests is supplied by
`ContinuousLinearMap.exists_seq_norming`; Mathlib's `Measurable.isLUB` and
`AEMeasurable.isLUB` then recover measurability of the norm.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, Proposition 1.1.28.
-/

public section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeparableSpace E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a separable domain, measurable norms of all orbits give a measurable operator norm.
In particular, strongly measurable orbits suffice. -/
theorem measurable_opNorm_of_forall_norm_apply {A : S → E →L[𝕜] F}
    (hA : ∀ x, Measurable (fun s ↦ ‖A s x‖)) : Measurable (fun s ↦ ‖A s‖) := by
  obtain ⟨v, -, hv⟩ := ContinuousLinearMap.exists_seq_norming (𝕜 := 𝕜) (E := E) (F := F)
  exact Measurable.isLUB (fun n ↦ hA (v n)) (fun s ↦ hv (A s))

/-- On a separable domain, a.e. measurable norms of all orbits give an a.e. measurable
operator norm. The exceptional set may depend on the vector being tested. -/
theorem aemeasurable_opNorm_of_forall_norm_apply {A : S → E →L[𝕜] F}
    (hA : ∀ x, AEMeasurable (fun s ↦ ‖A s x‖) μ) :
    AEMeasurable (fun s ↦ ‖A s‖) μ := by
  obtain ⟨v, -, hv⟩ := ContinuousLinearMap.exists_seq_norming (𝕜 := 𝕜) (E := E) (F := F)
  exact AEMeasurable.isLUB (fun n ↦ hA (v n)) (.of_forall fun s ↦ hv (A s))

end TauCeti
