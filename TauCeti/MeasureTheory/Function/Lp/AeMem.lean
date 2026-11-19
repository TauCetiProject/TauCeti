/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# `Lᵖ` classes with values in a closed set

For a closed subset `C` of the target, the `Lᵖ` classes taking values in `C` almost everywhere
form a closed subset of `Lᵖ` (`MeasureTheory.Lp.isClosed_setOf_ae_mem`): a sequence converging in
`Lᵖ` has a subsequence converging almost everywhere, and `C` contains the pointwise limits. For a
closed subspace `C` this is the closed subspace of `Lᵖ` classes with values in `C`, such as the
boundary values allowed by a boundary condition.
-/

public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The `Lᵖ` classes with values almost everywhere in a closed set `C` form a closed set. -/
theorem isClosed_setOf_ae_mem {C : Set E} (hC : IsClosed C) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  refine IsSeqClosed.isClosed fun f g hf hfg ↦ ?_
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 fun i ↦ hf (ns i)] with x hx hmem
  exact hC.mem_of_tendsto hx (Eventually.of_forall hmem)

end MeasureTheory.Lp
