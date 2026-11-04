/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Action
public import Mathlib.Data.Set.PowersetCard
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Uniform subsets from random permutations

A uniform permutation of a finite population sends a fixed set to a uniformly chosen subset of
the same cardinality. Taking the inverse image gives the uniform law of the positions occupied by
fixed success labels in a random ordering. This connects permutation-based sampling without
replacement to uniform sampling of subsets, including empty and full success sets.

The argument uses Mathlib's `Set.powersetCard.isPretransitive`, which gives transitivity of the
permutation action on subsets of a fixed size.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, third edition,
  Wiley, 2005, chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Finset

variable {α : Type*} [Finite α]
    [MeasurableSpace (Equiv.Perm α)] [MeasurableSingletonClass (Equiv.Perm α)]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]

/-- The image of a fixed finite set under a uniform permutation is uniform among all subsets
of the same size. The empty set and the full population are included. -/
theorem map_uniformOn_perm (s : Finset α) :
    (uniformOn (Set.univ : Set (Equiv.Perm α))).map (fun σ ↦ s.map σ.toEmbedding) =
      uniformOn (Set.powersetCard α s.card) := by
  classical
  let : MulAction.IsPretransitive (Equiv.Perm α) (Set.powersetCard α s.card) :=
    Set.powersetCard.isPretransitive
  have hcoe : BijOn (Subtype.val : Set.powersetCard α s.card → Finset α) Set.univ
      (Set.powersetCard α s.card) :=
    ⟨fun t _ ↦ t.prop, Subtype.val_injective.injOn, fun t ht ↦ ⟨⟨t, ht⟩, Set.mem_univ _, rfl⟩⟩
  have h := congrArg (fun μ : Measure (Set.powersetCard α s.card) ↦ μ.map Subtype.val)
    (TauCeti.Probability.map_smul_uniformOn_univ (G := Equiv.Perm α)
      (⟨s, rfl⟩ : Set.powersetCard α s.card))
  rw [Measure.map_map measurable_subtype_coe (measurable_of_countable _), hcoe.map_uniformOn] at h
  convert h using 1
  congr 1
  funext σ
  simp only [Function.comp_apply, Set.powersetCard.coe_smul, smul_finset_def, map_eq_image]
  rfl

/-- The positions occupied by a fixed set of labels in a uniform random permutation form a
uniform subset of the same size. -/
theorem map_preimage_uniformOn_perm (s : Finset α) :
    (uniformOn (Set.univ : Set (Equiv.Perm α))).map
        (fun σ : Equiv.Perm α ↦ s.preimage σ σ.injective.injOn) =
      uniformOn (Set.powersetCard α s.card) := by
  classical
  have hinv := (Equiv.inv (Equiv.Perm α)).map_uniformOn_univ
  have h := congrArg (fun μ : Measure (Equiv.Perm α) ↦
    μ.map (fun σ ↦ s.map σ.toEmbedding)) hinv
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    s.map_uniformOn_perm] at h
  convert h using 1
  congr 1
  funext σ
  ext a
  simp [Equiv.Perm.inv_def]

end Finset

namespace ProbabilityTheory.HasLaw

variable {α Ω : Type*} [Finite α]
    [MeasurableSpace (Equiv.Perm α)] [MeasurableSingletonClass (Equiv.Perm α)]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    [MeasurableSpace Ω] {P : Measure Ω} {σ : Ω → Equiv.Perm α}

/-- A uniform random permutation puts any fixed success labels in a uniform set of positions. -/
theorem preimage_finset_uniformOn_perm (hσ : HasLaw σ (uniformOn univ) P) (s : Finset α) :
    HasLaw (fun ω ↦ s.preimage (σ ω) (σ ω).injective.injOn)
      (uniformOn (Set.powersetCard α s.card)) P := by
  rw [← s.map_preimage_uniformOn_perm]
  exact (hasLaw_map (measurable_of_countable
    (fun τ : Equiv.Perm α ↦ s.preimage τ τ.injective.injOn)).aemeasurable).comp hσ

end ProbabilityTheory.HasLaw
