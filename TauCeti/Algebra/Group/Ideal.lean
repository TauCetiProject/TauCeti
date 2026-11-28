/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Ideal
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Order.Filter.Finite

/-!
# Uniform cut-off index for cardinality bounds on additive semigroup ideals

Let `α` be a type with addition whose `AddSemigroupIdeal α` lattice satisfies the ascending chain
condition (`WellFoundedGT (AddSemigroupIdeal α)`), let `ι` be a preordered index type, let
`S : ι → Set α` be a family of finite subsets, and let `σ : ι → ℕ` be a family of upper bounds.
By Noetherian induction on ideals, every sufficiently large `d : ι` is a uniform cut-off: any
`M : AddSemigroupIdeal α` satisfying `(S i \ M.carrier).ncard ≤ σ i` for all `i ≤ d` already
satisfies it for all `i : ι`.

## Main results

* `TauCeti.eventually_forall_ncard_sdiff_le`: uniform cut-off index for any Noetherian
  `AddSemigroupIdeal` lattice and any family of finite subsets `S : ι → Set α`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/ThetaModuli/FlatClosure.lean` (`eventually_isCutDegree`), generalized from
`J →₀ ℕ` and `ℕ`-indexed families to arbitrary `[Add α]` with
`WellFoundedGT (AddSemigroupIdeal α)` and `[Preorder ι]`.
-/

public section

open Filter Set

namespace TauCeti

/-- On an additive type `α` whose `AddSemigroupIdeal α` lattice satisfies the ascending chain
condition, for any family of finite sets `S : ι → Set α` indexed by a preorder `ι` and bounds
`σ : ι → ℕ`, every sufficiently large `d : ι` is a uniform cut-off: any `M : AddSemigroupIdeal α`
omitting at most `σ i` elements of `S i` for all `i ≤ d` does so for all `i : ι`. -/
theorem eventually_forall_ncard_sdiff_le {α ι : Type*} [Add α] [Preorder ι]
    [WellFoundedGT (AddSemigroupIdeal α)] (S : ι → Set α) (hS : ∀ i, (S i).Finite) (σ : ι → ℕ) :
    ∀ᶠ d : ι in atTop, ∀ M : AddSemigroupIdeal α,
      (∀ i ≤ d, (S i \ M.carrier).ncard ≤ σ i) → ∀ i : ι, (S i \ M.carrier).ncard ≤ σ i := by
  let Few (M : AddSemigroupIdeal α) (i : ι) : Prop := (S i \ M.carrier).ncard ≤ σ i
  suffices h_above : ∀ N : AddSemigroupIdeal α, ∀ᶠ d : ι in atTop,
      ∀ M ≥ N, (∀ i ≤ d, Few M i) → ∀ i : ι, Few M i from
    (h_above ⊥).mono fun d h_bot M ↦ h_bot M bot_le
  intro N
  induction N using WellFoundedGT.induction with | ind N ih => ?_
  by_cases h_few : ∀ i : ι, Few N i
  · exact .of_forall fun d M hNM _ i ↦
      (ncard_le_ncard (sdiff_le_sdiff_left hNM) ((hS i).sdiff)).trans (h_few i)
  obtain ⟨i, h_many⟩ := not_forall.mp h_few
  have h_lt (m : α) (hm : m ∈ S i \ N.carrier) : N < N ⊔ AddSemigroupIdeal.closure {m} :=
    left_lt_sup.mpr fun h_le ↦ hm.2 (AddSemigroupIdeal.closure_le.mp h_le (mem_singleton m))
  have h_larger : ∀ᶠ d : ι in atTop, ∀ m ∈ S i \ N.carrier,
      ∀ M ≥ N ⊔ AddSemigroupIdeal.closure {m}, (∀ j ≤ d, Few M j) → ∀ j : ι, Few M j :=
    (hS i).sdiff.eventually_all.mpr fun m hm ↦ ih _ (h_lt m hm)
  filter_upwards [h_larger, mem_atTop i] with d h_cut hd M hNM hM
  obtain ⟨m, hm, hmM⟩ : ∃ m ∈ S i \ N.carrier, m ∉ S i \ M.carrier :=
    not_subset.mp fun h_sub ↦ h_many ((ncard_le_ncard h_sub ((hS i).sdiff)).trans (hM i hd))
  have hm_mem : m ∈ M := not_not.mp fun hm_not ↦ hmM ⟨hm.1, hm_not⟩
  exact h_cut m hm M
    (sup_le hNM (AddSemigroupIdeal.closure_le.mpr (singleton_subset_iff.mpr hm_mem))) hM

end TauCeti
