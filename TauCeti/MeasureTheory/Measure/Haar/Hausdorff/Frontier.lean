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
measure has `μH[n]` measure zero, and `μH[n]` is an additive Haar measure, so the frontier is null
in `Ω`, and in any set where it has finite `μH[n - 1]` measure
(`TauCeti.addHaar_frontier_inter_eq_zero_of_hausdorffMeasure_frontier_inter_ne_top`). In
particular such a set is null-measurable in `Ω`, by Mathlib's `nullMeasurableSet_of_null_frontier`
for the restricted measure. The same holds when the frontier only has locally finite `μH[n - 1]`
measure in `Ω`
(`TauCeti.ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top`), since a
locally null set is null.

In the whole space, and in every finite dimension `n` (in dimension zero every frontier is empty),
a set whose frontier has finite `μH[n - 1]` measure has a null frontier
(`TauCeti.addHaar_frontier_eq_zero_of_hausdorffMeasure_frontier_ne_top`) and is null-measurable
(`TauCeti.nullMeasurableSet_of_hausdorffMeasure_frontier_ne_top`) for every additive Haar measure.
-/

public section

namespace TauCeti

open MeasureTheory Measure TopologicalSpace Set Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E}

/-- A set whose frontier has finite `μH[n - 1]` measure in a set `t` has a frontier that is null
in `t` for every additive Haar measure, in positive dimension `n`. -/
theorem addHaar_frontier_inter_eq_zero_of_hausdorffMeasure_frontier_inter_ne_top
    (hn : finrank ℝ E ≠ 0) {t : Set E} (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ t) ≠ ∞) :
    μ (frontier s ∩ t) = 0 :=
  absolutelyContinuous_isAddHaarMeasure μ _ <|
    (hausdorffMeasure_zero_or_top (Nat.cast_lt.2 (Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos))
      _).resolve_right h

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
  exact addHaar_frontier_inter_eq_zero_of_hausdorffMeasure_frontier_inter_ne_top μ hn (h K hK hKΩ)

/-- A set whose frontier has finite `μH[n - 1]` measure in an open set `Ω` agrees almost
everywhere in `Ω` with its interior, in positive dimension `n`. -/
theorem ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top (hn : finrank ℝ E ≠ 0)
    (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ Ω) ≠ ∞) :
    s =ᵐ[μ.restrict Ω] interior s :=
  ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top μ hn fun _ _ hKΩ =>
    ne_top_of_le_ne_top h (measure_mono (inter_subset_inter_right _ hKΩ))

/-- **A frontier of finite codimension-one measure is null.** In a real normed space of finite
dimension `n`, a set whose frontier has finite `μH[n - 1]` measure has a frontier that is null for
every additive Haar measure. In dimension zero every frontier is empty. -/
theorem addHaar_frontier_eq_zero_of_hausdorffMeasure_frontier_ne_top
    (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s) ≠ ∞) : μ (frontier s) = 0 := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · have : Subsingleton E := finrank_zero_iff.1 hn
    rw [(isClopen_discrete s).frontier_eq, measure_empty]
  simpa using addHaar_frontier_inter_eq_zero_of_hausdorffMeasure_frontier_inter_ne_top μ hn
    (t := univ) (by simpa using h)

/-- **Sets with a frontier of finite codimension-one measure are null-measurable.** In a real
normed space of finite dimension `n`, a set whose frontier has finite `μH[n - 1]` measure is
null-measurable for every additive Haar measure. -/
theorem nullMeasurableSet_of_hausdorffMeasure_frontier_ne_top
    (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s) ≠ ∞) : NullMeasurableSet s μ :=
  nullMeasurableSet_of_null_frontier
    (addHaar_frontier_eq_zero_of_hausdorffMeasure_frontier_ne_top μ h)

end TauCeti
