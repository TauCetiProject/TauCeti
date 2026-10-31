/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order

/-!
# Finite-stage enumerations: limits and fresh entries

An enumeration in finite stages is a sequence `A : ℕ → Finset ℕ`. The numbers **fresh** at stage
`s` are those entering in the transition to stage `s + 1`. When the stages are monotone, a number
is fresh at most once: it has a unique entry stage.

## Main definitions

* `TauCeti.Enumeration.stageLimit`: the set enumerated, the union `⋃ s, (A s : Set ℕ)` of all
  stages, so that Mathlib's union and supremum API applies to it.
* `TauCeti.Enumeration.fresh`: the numbers entering in the transition to stage `s + 1`.

## Main results

* `TauCeti.Enumeration.unique_entry_stage`: under monotone stages a number is fresh at most once.
* `TauCeti.Enumeration.exists_mem_fresh_of_mem_stageLimit`: a number of the limit that is not in
  the first stage is fresh at some stage.
* `TauCeti.Enumeration.finite_prefix_stabilizes`: under monotone stages, the stages eventually
  agree with the limit below any bound.
* `TauCeti.Enumeration.limit_agrees_of_no_fresh_below`: under monotone stages, if nothing below
  `u` enters after stage `s`, the limit agrees with `A s` below `u`.
* `TauCeti.Enumeration.stageLimit_comp_of_cofinal`: under monotone stages, reindexing by a clock
  with cofinal range does not change the limit; in particular neither does shifting the stages.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

namespace TauCeti

namespace Enumeration

/-- The numbers entering the enumeration `A` in the transition to stage `s + 1`. -/
def fresh (A : ℕ → Finset ℕ) (s : ℕ) : Finset ℕ :=
  A (s + 1) \ A s

/-- Membership in `fresh`. -/
@[simp]
theorem mem_fresh {A : ℕ → Finset ℕ} {s x : ℕ} : x ∈ fresh A s ↔ x ∈ A (s + 1) ∧ x ∉ A s :=
  Finset.mem_sdiff

/-- **Unique entry stage.** Under monotone stages a number is fresh at most once: once entered, it
stays. -/
theorem unique_entry_stage {A : ℕ → Finset ℕ} (hA : Monotone A) {s t x : ℕ}
    (hs : x ∈ fresh A s) (ht : x ∈ fresh A t) : s = t := by
  rw [mem_fresh] at hs ht
  -- an earlier entry would already put the number in the later stage
  rcases lt_trichotomy s t with h | h | h
  · exact (ht.2 (hA (Nat.succ_le_of_lt h) hs.1)).elim
  · exact h
  · exact (hs.2 (hA (Nat.succ_le_of_lt h) ht.1)).elim

/-! ### The limit of an enumeration -/

/-- The set enumerated by the stages `A`: the union of all stages. -/
def stageLimit (A : ℕ → Finset ℕ) : Set ℕ :=
  ⋃ s, (A s : Set ℕ)

/-- The limit is the union of the stages. -/
theorem stageLimit_eq_iUnion (A : ℕ → Finset ℕ) : stageLimit A = ⋃ s, (A s : Set ℕ) :=
  (rfl)

/-- Membership in the limit is membership at some stage. -/
@[simp]
theorem mem_stageLimit {A : ℕ → Finset ℕ} {x : ℕ} : x ∈ stageLimit A ↔ ∃ s, x ∈ A s := by
  simp [stageLimit_eq_iUnion]

/-- Every stage is contained in the limit. -/
theorem subset_stageLimit (A : ℕ → Finset ℕ) (s : ℕ) : (A s : Set ℕ) ⊆ stageLimit A :=
  Set.subset_iUnion (fun s => (A s : Set ℕ)) s

/-- The limit is monotone in the stages. -/
theorem stageLimit_mono {A B : ℕ → Finset ℕ} (h : ∀ s, A s ⊆ B s) :
    stageLimit A ⊆ stageLimit B :=
  Set.iUnion_mono fun s => Finset.coe_subset.2 (h s)

/-- A fresh entry belongs to the limit. -/
theorem mem_stageLimit_of_mem_fresh {A : ℕ → Finset ℕ} {s x : ℕ} (hx : x ∈ fresh A s) :
    x ∈ stageLimit A :=
  mem_stageLimit.2 ⟨s + 1, (mem_fresh.1 hx).1⟩

/-- **An entry stage.** A number of the limit that is not in the first stage is fresh at some
stage: the stage before the first one containing it. -/
theorem exists_mem_fresh_of_mem_stageLimit {A : ℕ → Finset ℕ} {x : ℕ} (hx : x ∈ stageLimit A)
    (h0 : x ∉ A 0) : ∃ s, x ∈ fresh A s := by
  obtain ⟨s, hs, hs'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists h0 (mem_stageLimit.1 hx)
  exact ⟨s, mem_fresh.2 ⟨hs', hs⟩⟩

/-- Under monotone stages, a number is in the limit exactly when it is in every late enough
stage. -/
theorem mem_stageLimit_iff_eventually {A : ℕ → Finset ℕ} (hA : Monotone A) {x : ℕ} :
    x ∈ stageLimit A ↔ ∃ s₀, ∀ s, s₀ ≤ s → x ∈ A s := by
  rw [mem_stageLimit]
  exact ⟨fun ⟨s₀, hx⟩ => ⟨s₀, fun _ hs => hA hs hx⟩, fun ⟨s₀, h⟩ => ⟨s₀, h s₀ le_rfl⟩⟩

/-- **Finite-prefix stabilization.** Under monotone stages, the stages eventually agree with the
limit below any bound `u`. -/
theorem finite_prefix_stabilizes {A : ℕ → Finset ℕ} (hA : Monotone A) (u : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ x, x < u → (x ∈ A s ↔ x ∈ stageLimit A) := by
  classical
  have hA' : Monotone fun s => (A s : Set ℕ) := fun _ _ h => Finset.coe_subset.2 (hA h)
  -- the numbers below `u` that ever enter all lie in one stage of the directed union
  obtain ⟨s₀, hs₀⟩ := hA'.directed_le.exists_mem_subset_of_finset_subset_biUnion
    (s := (Finset.range u).filter (· ∈ stageLimit A)) fun x hx => by
      rw [← stageLimit_eq_iUnion]
      exact (Finset.mem_filter.1 hx).2
  refine ⟨s₀, fun s hs x hx => ⟨fun h => subset_stageLimit A s h, fun h => ?_⟩⟩
  exact hA hs (hs₀ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, h⟩))

/-- **Reindexing by a clock with cofinal range.** Under monotone stages, reading the stages along a
clock `c` whose range is cofinal, so that every stage is at most some value of `c`, gives the same
limit. The clock need not increase: it may return to small stages infinitely often. -/
theorem stageLimit_comp_of_cofinal {A : ℕ → Finset ℕ} (hA : Monotone A) {c : ℕ → ℕ}
    (hc : ∀ s, ∃ t, s ≤ c t) : stageLimit (A ∘ c) = stageLimit A :=
  -- the coerced stages are monotone sets
  Monotone.iSup_comp_eq (f := fun s => (A s : Set ℕ)) (fun _ _ h => Finset.coe_subset.2 (hA h)) hc

/-- **Stage shifts.** Under monotone stages, dropping the first `k` stages does not change the
limit. -/
theorem stageLimit_shift {A : ℕ → Finset ℕ} (hA : Monotone A) (k : ℕ) :
    stageLimit (fun s => A (s + k)) = stageLimit A :=
  Monotone.iUnion_nat_add (f := fun s => (A s : Set ℕ)) (fun _ _ h => Finset.coe_subset.2 (hA h)) k

/-- **No new entries below `u`.** Under monotone stages, if nothing below `u` enters after stage
`s`, then below `u` the limit agrees with `A s`. -/
theorem limit_agrees_of_no_fresh_below {A : ℕ → Finset ℕ} (hA : Monotone A) {s u : ℕ}
    (h : ∀ t, s ≤ t → ∀ z, z < u → z ∉ fresh A t) :
    ∀ z, z < u → (z ∈ A s ↔ z ∈ stageLimit A) := by
  intro z hz
  refine ⟨fun hzs => subset_stageLimit A s hzs, fun hzl => ?_⟩
  by_contra hzs
  -- `z` is not in the first stage, so it is fresh at some stage `t`
  obtain ⟨t, ht⟩ := exists_mem_fresh_of_mem_stageLimit hzl fun h0 => hzs (hA (Nat.zero_le s) h0)
  rcases le_or_gt s t with hst | hts
  · exact h t hst z hz ht
  · exact hzs (hA hts (mem_fresh.1 ht).1)

end Enumeration

end TauCeti
