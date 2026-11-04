/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.GapTrivialization
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Countable locally finite trivializing families of vector bundles

The gap charts of a subordinate partition of unity are linear whenever the original charts
are linear. Consequently every vector bundle over a paracompact normal base has a countable,
locally finite trivializing family. Paracompact Hausdorff bases are normal. The construction uses
the native partition of unity and native bundle trivializations, and imposes no finite-rank
assumption.

This is the chart-gluing part of Milnor and Stasheff, *Characteristic Classes*, Lemma 5.9.
Metric-normalized frames and extension of weighted coordinates at zero weights require
additional arguments.
-/

public section

noncomputable section

open Bundle Set

namespace PartitionOfUnity

variable {ι B F R : Type*} {E : B → Type*} {s : Set B}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
  [Semiring R] [AddCommMonoid F] [Module R F] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module R (E b)] (ρ : PartitionOfUnity ι B s)
  (e : ι → Trivialization F (π F E)) (he : ρ.IsSubordinate fun i ↦ (e i).baseSet)
  [∀ i, (e i).IsLinear R]

/-- Gap charts preserve the fiberwise linearity of the subordinate charts. -/
instance isLinear_gapTrivialization (n : ℕ) : (ρ.gapTrivialization e he n).IsLinear R where
  linear b hb := by
    rw [gapTrivialization_baseSet] at hb
    obtain ⟨S, hcard, hpos⟩ := ρ.exists_gap_pos_of_gapPartition_pos hb
    have hS := (ρ.gap_pos_iff.1 hpos).1
    have hfun : (fun v : E b ↦ (ρ.gapTrivialization e he n ⟨b, v⟩).2) =
        fun v : E b ↦ (e hS.choose ⟨b, v⟩).2 := by
      subst n
      exact funext fun v ↦ congrArg Prod.snd (ρ.gapTrivialization_apply e he hS hpos v)
    rw [hfun]
    exact (e hS.choose).linear R (he.mem_of_gap_pos hpos hS.choose_spec)

end PartitionOfUnity

namespace TauCeti

/-- A vector bundle over a paracompact normal base admits countably many fiberwise linear
trivializations whose open base sets cover the base and form a locally finite family. -/
theorem exists_countable_locallyFinite_trivialization
    (R : Type*) {B F : Type*} {E : B → Type*} [TopologicalSpace B]
    [ParacompactSpace B] [NormalSpace B] [NontriviallyNormedField R]
    [NormedAddCommGroup F] [NormedSpace R F] [∀ b, AddCommMonoid (E b)]
    [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle R F E] :
    ∃ e : ℕ → Trivialization F (π F E),
      (∀ n, (e n).IsLinear R) ∧ (⋃ n, (e n).baseSet) = univ ∧
        LocallyFinite (fun n ↦ (e n).baseSet) := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun b ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
  refine ⟨ρ.gapTrivialization (trivializationAt F E) hρ, fun _ ↦ inferInstance,
    Set.eq_univ_of_univ_subset ?_, ρ.locallyFinite_gapTrivialization_baseSet _ hρ⟩
  exact ρ.subset_iUnion_gapTrivialization_baseSet _ hρ

end TauCeti
