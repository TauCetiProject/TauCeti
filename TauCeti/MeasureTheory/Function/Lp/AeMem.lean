/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Pointwise constraints in `Lᵖ`

Almost-everywhere membership in a closed set is a closed constraint in `Lᵖ`. Convex pointwise
constraints give convex sets of `Lᵖ` classes. These facts apply in particular to probability
vectors used as the conditional action probabilities of randomized rules.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {p : ℝ≥0∞} {s : Set E}

/-- The `Lᵖ` classes taking values almost everywhere in a closed set form a closed set. -/
theorem isClosed_setOf_ae_mem [Fact (1 ≤ p)] (hs : IsClosed s) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ s} := by
  apply IsSeqClosed.isClosed
  intro f g hf hg
  obtain ⟨n, _, hn⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  filter_upwards [hn, ae_all_iff.2 (fun k ↦ hf (n k))] with x hx hsx
  exact hs.mem_of_tendsto hx (Eventually.of_forall hsx)

/-- The `Lᵖ` classes taking values almost everywhere in a convex set form a convex set. -/
theorem convex_setOf_ae_mem [NormedSpace ℝ E] (hs : Convex ℝ s) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ s} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
    Lp.coeFn_smul b g] with x hfx hgx hadd hsmul₁ hsmul₂
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂, Pi.smul_apply, Pi.smul_apply]
  exact hs hfx hgx ha hb hab

end MeasureTheory.Lp
