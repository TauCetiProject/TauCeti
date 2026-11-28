/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Ideal
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Algebra.Order.Group.Ideal
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Uniform cut-off index for cardinality bounds on semigroup and monomial ideals

Let `α` be an additive semigroup whose additive semigroup ideals satisfy the ascending chain
condition (`WellFoundedGT (AddSemigroupIdeal α)`), let `S : ℕ → Set α` be a sequence of finite
subsets, and let `σ : ℕ → ℕ` be a sequence of upper bounds. By Noetherian induction on ideals,
there exists a uniform cut-off `d : ℕ` (indeed all sufficiently large `d`) such that every
`M : AddSemigroupIdeal α` satisfying `(S i \ M.carrier).ncard ≤ σ i` for all `i ≤ d` already
satisfies it for all `i : ℕ`.

Specializing to `α = J →₀ ℕ` (with `Finite J`) and `S i = Finsupp.degree ⁻¹' {f i}` for any
degree sequence `f : ℕ → ℕ` yields the uniform cut-off degree for monomial ideals in finitely
many variables.

## Main results

* `AddSemigroupIdeal.eventually_forall_ncard_sdiff_le`: uniform cut-off index for any Noetherian
  semigroup-ideal lattice and any sequence of finite subsets `S : ℕ → Set α`.
* `Finsupp.eventually_forall_ncard_degree_sdiff_le`: specialization to monomial ideals
  `AddSemigroupIdeal (J →₀ ℕ)` in finitely many variables `J` and arbitrary degree sequence
  `f : ℕ → ℕ`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/ThetaModuli/FlatClosure.lean` (`eventually_isCutDegree`).
-/

public section

open Filter Set

namespace AddSemigroupIdeal

/-- In a semigroup whose additive semigroup ideals satisfy the ascending chain condition, for any
sequence of finite sets `S : ℕ → Set α` and bounds `σ : ℕ → ℕ`, every sufficiently large `d : ℕ`
is a uniform cut-off: any `M : AddSemigroupIdeal α` omitting at most `σ i` elements of `S i` for
all `i ≤ d` does so for all `i : ℕ`. -/
theorem eventually_forall_ncard_sdiff_le {α : Type*} [AddSemigroup α]
    [WellFoundedGT (AddSemigroupIdeal α)] (S : ℕ → Set α) (hS : ∀ i, (S i).Finite) (σ : ℕ → ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ M : AddSemigroupIdeal α,
      (∀ i ≤ d, (S i \ M.carrier).ncard ≤ σ i) → ∀ i : ℕ, (S i \ M.carrier).ncard ≤ σ i := by
  let Few (M : AddSemigroupIdeal α) (i : ℕ) : Prop := (S i \ M.carrier).ncard ≤ σ i
  suffices h_above : ∀ N : AddSemigroupIdeal α, ∀ᶠ d : ℕ in atTop,
      ∀ M ≥ N, (∀ i ≤ d, Few M i) → ∀ i : ℕ, Few M i from
    (h_above ⊥).mono fun d h_bot M ↦ h_bot M bot_le
  intro N
  induction N using WellFoundedGT.induction with | ind N ih => ?_
  by_cases h_few : ∀ i : ℕ, Few N i
  · exact .of_forall fun d M hNM _ i ↦
      (ncard_le_ncard (sdiff_le_sdiff_left hNM) ((hS i).sdiff)).trans (h_few i)
  obtain ⟨i, h_many⟩ := not_forall.mp h_few
  have h_lt (m : α) (hm : m ∈ S i \ N.carrier) : N < N ⊔ closure {m} :=
    left_lt_sup.mpr fun h_le ↦ hm.2 (closure_le.mp h_le (mem_singleton m))
  have h_larger : ∀ᶠ d : ℕ in atTop, ∀ m ∈ S i \ N.carrier,
      ∀ M ≥ N ⊔ closure {m}, (∀ j ≤ d, Few M j) → ∀ j : ℕ, Few M j :=
    (hS i).sdiff.eventually_all.mpr fun m hm ↦ ih _ (h_lt m hm)
  filter_upwards [h_larger, mem_atTop i] with d h_cut hd M hNM hM
  obtain ⟨m, hm, hmM⟩ : ∃ m ∈ S i \ N.carrier, m ∉ S i \ M.carrier :=
    not_subset.mp fun h_sub ↦ h_many ((ncard_le_ncard h_sub ((hS i).sdiff)).trans (hM i hd))
  have hm_mem : m ∈ M := not_not.mp fun hm_not ↦ hmM ⟨hm.1, hm_not⟩
  exact h_cut m hm M (sup_le hNM (closure_le.mpr (singleton_subset_iff.mpr hm_mem))) hM

end AddSemigroupIdeal

namespace Finsupp

/-- For finitely many variables `J`, any degree sequence `f : ℕ → ℕ`, and any count bounds
`σ : ℕ → ℕ`, every sufficiently large `d : ℕ` is a uniform cut-off for monomial ideals
`M : AddSemigroupIdeal (J →₀ ℕ)`: omitting at most `σ i` monomials of degree `f i` for all
`i ≤ d` forces the same bound for all `i : ℕ`. -/
theorem eventually_forall_ncard_degree_sdiff_le {J : Type*} [Finite J] (f σ : ℕ → ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ M : AddSemigroupIdeal (J →₀ ℕ),
      (∀ i ≤ d, (degree ⁻¹' {f i} \ M.carrier).ncard ≤ σ i) →
        ∀ i : ℕ, (degree ⁻¹' {f i} \ M.carrier).ncard ≤ σ i :=
  AddSemigroupIdeal.eventually_forall_ncard_sdiff_le
    (fun i ↦ degree ⁻¹' {f i}) (fun i ↦ finite_of_degree_eq (f i)) σ

end Finsupp
