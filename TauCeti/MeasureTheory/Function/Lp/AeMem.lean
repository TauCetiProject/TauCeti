/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# `Lᵖ` classes with values in a closed set

For a closed subset `C` of the target, the `Lᵖ` classes taking values in `C` almost everywhere
form a closed subset of `Lᵖ` (`MeasureTheory.Lp.isClosed_setOf_ae_mem`): a sequence converging in
`Lᵖ` has a subsequence converging almost everywhere, and `C` contains the pointwise limits. For a
closed subspace `C` this is the closed subspace of `Lᵖ` classes with values in `C`, such as the
boundary values allowed by a boundary condition.

Similarly, for a convex set `C`, the `Lᵖ` classes taking values in `C` almost everywhere form a
convex set (`MeasureTheory.Lp.convex_setOf_ae_mem`), such as the conditional action probabilities
of randomized decision rules.
-/

public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞}

/-- The `Lᵖ` classes with values almost everywhere in a closed set `C` form a closed set. -/
theorem isClosed_setOf_ae_mem [Fact (1 ≤ p)] {C : Set E} (hC : IsClosed C) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  refine IsSeqClosed.isClosed fun f g hf hfg ↦ ?_
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 fun i ↦ hf (ns i)] with x hx hmem
  exact hC.mem_of_tendsto hx (Eventually.of_forall hmem)

/-- The `Lᵖ` classes with values almost everywhere in a convex set `C` form a convex set. -/
theorem convex_setOf_ae_mem [NormedSpace ℝ E] {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
    Lp.coeFn_smul b g] with x hfx hgx hadd hsmul₁ hsmul₂
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂, Pi.smul_apply, Pi.smul_apply]
  exact hC hfx hgx ha hb hab

end MeasureTheory.Lp
