/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff

/-!
# Sets whose frontier has finite codimension-one Hausdorff measure

In a real normed space `E` of positive finite dimension `n`, a set whose topological frontier has
finite `(n - 1)`-dimensional Hausdorff measure inside an open set `Ω` agrees almost everywhere in
`Ω`, for every additive Haar measure, with its interior
(`TauCeti.ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top`): a set of finite `μH[n - 1]`
measure has `μH[n]` measure zero, and `μH[n]` is an additive Haar measure. In particular such a set
is null-measurable in `Ω`, by Mathlib's `nullMeasurableSet_of_null_frontier` for the restricted
measure. The same holds when the frontier only has locally finite `μH[n - 1]` measure in `Ω`
(`TauCeti.ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top`), since a
locally null set is null.
-/

public section

namespace TauCeti

open MeasureTheory Measure TopologicalSpace Set Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E}

/-- A set whose frontier has finite `μH[n - 1]` measure in an open set `Ω` agrees almost
everywhere in `Ω` with its interior, in positive dimension `n`. -/
theorem ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top (hn : finrank ℝ E ≠ 0)
    (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ Ω) ≠ ∞) :
    s =ᵐ[μ.restrict Ω] interior s := by
  have hH : μH[((finrank ℝ E : ℕ) : ℝ)] (frontier s ∩ Ω) = 0 :=
    (hausdorffMeasure_zero_or_top (Nat.cast_lt.2 (Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos))
      _).resolve_right h
  have hnull : μ (frontier s ∩ Ω) = 0 := absolutelyContinuous_isAddHaarMeasure μ _ hH
  refine (interior_ae_eq_of_null_frontier ?_).symm
  rwa [Measure.restrict_apply' Ω.isOpen.measurableSet]

/-- A set whose frontier has locally finite `μH[n - 1]` measure in an open set `Ω`, that is finite
`μH[n - 1]` measure in every compact subset of `Ω`, agrees almost everywhere in `Ω` with its
interior, in positive dimension `n`. -/
theorem ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top
    (hn : finrank ℝ E ≠ 0)
    (h : ∀ K, IsCompact K → K ⊆ Ω → μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ K) ≠ ∞) :
    s =ᵐ[μ.restrict Ω] interior s := by
  refine (interior_ae_eq_of_null_frontier ?_).symm
  rw [Measure.restrict_apply' Ω.isOpen.measurableSet]
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨K, hK, hxK, hKΩ⟩ := exists_compact_subset Ω.isOpen hx.2
  refine ⟨frontier s ∩ K, mem_nhdsWithin.2 ⟨interior K, isOpen_interior, hxK,
    fun y hy => ⟨hy.2.1, interior_subset hy.1⟩⟩, ?_⟩
  exact absolutelyContinuous_isAddHaarMeasure μ _
    ((hausdorffMeasure_zero_or_top (Nat.cast_lt.2 (Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos))
      _).resolve_right (h K hK hKΩ))

end TauCeti
