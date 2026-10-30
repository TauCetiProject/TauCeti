/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Locally finite families

A locally finite family of sets stays locally finite when it is reindexed along the first
projection `ι × κ → ι` with `κ` finite (`LocallyFinite.comp_fst`). Together with
`LocallyFinite.subset`, this makes a family indexed by `ι × κ` whose `(i, k)`-th member lies in
the `i`-th member of a locally finite family locally finite. Dually, the pointwise union of
finitely many locally finite families is locally finite (`LocallyFinite.iUnion`).

In a pseudometric space, a locally finite family of closed sets has the following useful local
description: around each point there is a ball such that every member of the family meeting the
ball contains the centre.
-/

public section

open Set

namespace LocallyFinite

variable {ι κ X : Type*} [TopologicalSpace X] {f : ι → Set X}

/-- A locally finite family stays locally finite when reindexed along the first projection
`ι × κ → ι`, for `κ` finite. -/
theorem comp_fst [Finite κ] (hf : LocallyFinite f) : LocallyFinite fun p : ι × κ ↦ f p.1 :=
  fun x ↦
    let ⟨U, hU, hfin⟩ := hf x
    ⟨U, hU, (hfin.prod (finite_univ (α := κ))).subset fun _ hp ↦ ⟨hp, mem_univ _⟩⟩

/-- The pointwise union of finitely many locally finite families is locally finite. -/
protected theorem iUnion [Finite κ] {f : κ → ι → Set X} (hf : ∀ k, LocallyFinite (f k)) :
    LocallyFinite fun i ↦ ⋃ k, f k i := by
  simp_rw [locallyFinite_iff_smallSets] at hf ⊢
  intro x
  filter_upwards [Filter.eventually_all.2 fun k ↦ hf k x] with t ht
  simpa only [iUnion_inter, nonempty_iUnion, ofPred_exists] using finite_iUnion ht

end LocallyFinite

namespace TauCeti

open Metric Set

/-- Around each point there is a ball such that every member of a locally finite family of closed
sets that meets the ball contains the centre. -/
theorem exists_pos_forall_mem_of_mem_ball {X ι : Type*} [PseudoMetricSpace X]
    {s : ι → Set X} (hs : ∀ i, IsClosed (s i)) (hlf : LocallyFinite s) (x : X) :
    ∃ r > 0, ∀ i, ∀ y ∈ ball x r, y ∈ s i → x ∈ s i := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlf.eventually_subset hs x)
  exact ⟨r, hr, fun i y hy hys ↦ hball y hy hys⟩

end TauCeti
