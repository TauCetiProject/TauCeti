/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The `Lᵖ` seminorm on an open set from its compact subsets

In a locally compact, second countable space, an open set `U` is the increasing union of a compact
exhaustion. For a finite exponent `p` the `Lᵖ` seminorm over `U` is therefore controlled by its
values over the compact subsets of `U`: a bound that holds on every compact `K ⊆ U` holds on `U`
(`MeasureTheory.eLpNorm_restrict_le_of_forall_isCompact`). Local estimates, which naturally come
with a compact set, give global ones in this way.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α ε : Type*} [TopologicalSpace α] [MeasurableSpace α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [TopologicalSpace ε] [ContinuousENorm ε] {μ : Measure α}

/-- **The `Lᵖ` seminorm on an open set is controlled by its compact subsets.** For a finite
exponent `p`, if the `Lᵖ` seminorm of `f` over every compact subset of an open set `U` is at
most `C`, then so is its `Lᵖ` seminorm over `U`. -/
theorem eLpNorm_restrict_le_of_forall_isCompact {U : Set α} (hU : IsOpen U) {f : α → ε}
    {p : ℝ≥0∞} (hp : p ≠ ∞) (hf : AEStronglyMeasurable f (μ.restrict U))
    {C : ℝ≥0∞} (h : ∀ K ⊆ U, IsCompact K → eLpNorm f p (μ.restrict K) ≤ C) :
    eLpNorm f p (μ.restrict U) ≤ C := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm, hf]
  have := hU.locallyCompactSpace
  -- A compact exhaustion of `U`, as a directed family of compact subsets of `α`.
  let K := CompactExhaustion.choice U
  have hunion : ⋃ n, ((↑) '' K n : Set α) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ, Subtype.range_coe]
  have hdir : Directed (· ⊆ ·) fun n => ((↑) '' K n : Set α) :=
    Monotone.directed_le fun m n hmn => image_mono (K.subset hmn)
  have hsub : ∀ n, ((↑) '' K n : Set α) ⊆ U := fun n => image_subset_iff.2 fun x _ => x.property
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf, one_div, ENNReal.rpow_inv_le_iff hpos,
    ← hunion, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun n => ?_
  have hn := h _ (hsub n) ((K.isCompact n).image continuous_subtypeVal)
  rwa [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hf.mono_measure
    (Measure.restrict_mono (hsub n) le_rfl)), one_div, ENNReal.rpow_inv_le_iff hpos] at hn

end MeasureTheory
