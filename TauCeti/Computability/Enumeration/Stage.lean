/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum
public import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order

/-!
# Finite-stage enumerations: limits and fresh entries

An enumeration in finite stages is a sequence `A : ℕ → Finset α`. The elements **fresh** at stage
`s` are those entering in the transition to stage `s + 1`. When the stages are monotone, an element
is fresh at most once: it has a unique entry stage.

## Main definitions

* `TauCeti.Enumeration.stageLimit`: the set enumerated, the union `⋃ s, (A s : Set α)` of all
  stages, so that Mathlib's union and supremum API applies to it.
* `TauCeti.Enumeration.fresh`: the elements entering in the transition to stage `s + 1`.

## Main results

* `TauCeti.Enumeration.unique_entry_stage`: under monotone stages an element is fresh at most once.
* `TauCeti.Enumeration.exists_mem_fresh_of_mem_stageLimit`: every element of the limit outside the
  first stage is fresh at some stage.
* `TauCeti.Enumeration.finite_prefix_stabilizes`: under monotone stages, the stages eventually
  agree with the limit below any bound.
* `TauCeti.Enumeration.agrees_of_no_fresh_below`: under monotone stages, if nothing below `u`
  enters between stages `s` and `t`, then `A s` and `A t` agree below `u`.
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

variable {α : Type*}

/-- The elements entering the enumeration `A` in the transition to stage `s + 1`. -/
def fresh [DecidableEq α] (A : ℕ → Finset α) (s : ℕ) : Finset α :=
  A (s + 1) \ A s

/-- Fresh entries form the difference of the consecutive stages. -/
theorem fresh_eq_sdiff [DecidableEq α] (A : ℕ → Finset α) (s : ℕ) :
    fresh A s = A (s + 1) \ A s :=
  (rfl)

/-- Membership in `fresh`. -/
@[simp]
theorem mem_fresh [DecidableEq α] {A : ℕ → Finset α} {s : ℕ} {x : α} :
    x ∈ fresh A s ↔ x ∈ A (s + 1) ∧ x ∉ A s :=
  Finset.mem_sdiff

/-- **Unique entry stage.** Under monotone stages an element is fresh at most once: once entered, it
stays. -/
theorem unique_entry_stage [DecidableEq α] {A : ℕ → Finset α} (hA : Monotone A)
    {s t : ℕ} {x : α}
    (hs : x ∈ fresh A s) (ht : x ∈ fresh A t) : s = t := by
  rw [mem_fresh] at hs ht
  -- An earlier entry would already put the element in the later stage.
  rcases lt_trichotomy s t with h | h | h
  · exact (ht.2 (hA (Nat.succ_le_of_lt h) hs.1)).elim
  · exact h
  · exact (hs.2 (hA (Nat.succ_le_of_lt h) ht.1)).elim

/-- For increasing stages, adding the size of the fresh batch to the old size gives
the new size. -/
theorem card_fresh_add_card [DecidableEq α] {A : ℕ → Finset α} {s : ℕ}
    (h : A s ⊆ A (s + 1)) :
    (fresh A s).card + (A s).card = (A (s + 1)).card := by
  rw [fresh_eq_sdiff]
  exact Finset.card_sdiff_add_card_eq_card h

/-! ### The limit of an enumeration -/

/-- The set enumerated by the stages `A`: the union of all stages. -/
def stageLimit (A : ℕ → Finset α) : Set α :=
  ⋃ s, (A s : Set α)

/-- The limit is the union of the stages. -/
theorem stageLimit_eq_iUnion (A : ℕ → Finset α) : stageLimit A = ⋃ s, (A s : Set α) :=
  (rfl)

/-- Membership in the limit is membership at some stage. -/
@[simp]
theorem mem_stageLimit {A : ℕ → Finset α} {x : α} : x ∈ stageLimit A ↔ ∃ s, x ∈ A s := by
  simp [stageLimit_eq_iUnion]

/-- Every stage is contained in the limit. -/
theorem subset_stageLimit (A : ℕ → Finset α) (s : ℕ) : (A s : Set α) ⊆ stageLimit A :=
  Set.subset_iUnion (fun s => (A s : Set α)) s

/-- The limit is monotone in the stages. -/
theorem stageLimit_mono {A B : ℕ → Finset α} (h : ∀ s, A s ⊆ B s) :
    stageLimit A ⊆ stageLimit B :=
  Set.iUnion_mono fun s => Finset.coe_subset.2 (h s)

/-- The stagewise product of two increasing enumerations has the product of their limits. -/
theorem stageLimit_product {β : Type*} {A : ℕ → Finset α} {B : ℕ → Finset β}
    (hA : Monotone A) (hB : Monotone B) :
    stageLimit (fun s => A s ×ˢ B s) = stageLimit A ×ˢ stageLimit B := by
  simp only [stageLimit_eq_iUnion, Finset.coe_product]
  exact Set.iUnion_prod_of_monotone (fun _ _ h => Finset.coe_subset.2 (hA h))
    (fun _ _ h => Finset.coe_subset.2 (hB h))

/-- At the limit, stagewise disjoint sums retain both the left and the right tags. -/
@[simp]
theorem stageLimit_disjSum {β : Type*} (A : ℕ → Finset α) (B : ℕ → Finset β) :
    stageLimit (fun s => (A s).disjSum (B s)) =
      Sum.inl '' stageLimit A ∪ Sum.inr '' stageLimit B := by
  ext x
  cases x <;> simp [Set.mem_image]

/-- A fresh entry belongs to the limit. -/
theorem mem_stageLimit_of_mem_fresh [DecidableEq α] {A : ℕ → Finset α} {s : ℕ} {x : α}
    (hx : x ∈ fresh A s) : x ∈ stageLimit A :=
  mem_stageLimit.2 ⟨s + 1, (mem_fresh.1 hx).1⟩

/-- **An entry stage.** An element of the limit that is not in the first stage is fresh at some
stage: the stage before the first one containing it. -/
theorem exists_mem_fresh_of_mem_stageLimit [DecidableEq α] {A : ℕ → Finset α} {x : α}
    (hx : x ∈ stageLimit A) (h0 : x ∉ A 0) : ∃ s, x ∈ fresh A s := by
  obtain ⟨s, hs, hs'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists h0 (mem_stageLimit.1 hx)
  exact ⟨s, mem_fresh.2 ⟨hs', hs⟩⟩

/-- Under monotone stages, an element is in the limit exactly when it is in every late enough
stage. -/
theorem mem_stageLimit_iff_eventually {A : ℕ → Finset α} (hA : Monotone A) {x : α} :
    x ∈ stageLimit A ↔ ∃ s₀, ∀ s, s₀ ≤ s → x ∈ A s := by
  rw [mem_stageLimit]
  exact ⟨fun ⟨s₀, hx⟩ => ⟨s₀, fun _ hs => hA hs hx⟩, fun ⟨s₀, h⟩ => ⟨s₀, h s₀ le_rfl⟩⟩

/-- Every finite subset of the limit is already contained in a stage of a directed enumeration. -/
theorem exists_subset_stage_of_subset_stageLimit {A : ℕ → Finset α} (hA : Directed (· ⊆ ·) A)
    {D : Finset α} (hD : (D : Set α) ⊆ stageLimit A) : ∃ s, D ⊆ A s := by
  have hdir : Directed (· ⊆ ·) fun s => (A s : Set α) := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hA i j
    exact ⟨k, Finset.coe_subset.mpr hik, Finset.coe_subset.mpr hjk⟩
  rw [stageLimit_eq_iUnion] at hD
  obtain ⟨s, hs⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hD
  exact ⟨s, Finset.coe_subset.mp hs⟩

/-- Increasing finite stages have unbounded cardinalities exactly when their limit is
infinite. -/
theorem stageLimit_infinite_iff {A : ℕ → Finset α} (hA : Monotone A) :
    (stageLimit A).Infinite ↔ ∀ n, ∃ s, n ≤ (A s).card := by
  constructor
  · intro h n
    obtain ⟨D, hD, hcard⟩ := h.exists_subset_card_eq n
    obtain ⟨s, hs⟩ := exists_subset_stage_of_subset_stageLimit hA.directed_le hD
    exact ⟨s, hcard ▸ Finset.card_le_card hs⟩
  · intro h hfin
    obtain ⟨s, hs⟩ := h (hfin.toFinset.card + 1)
    have hle : (A s).card ≤ hfin.toFinset.card :=
      Finset.card_le_card fun x hx => hfin.mem_toFinset.mpr (subset_stageLimit A s hx)
    omega

/-- An increasing enumeration with at least one fresh entry at every transition
has an infinite limit. -/
theorem stageLimit_infinite_of_fresh_nonempty {A : ℕ → Finset α} [DecidableEq α]
    (hA : Monotone A) (hstep : ∀ s, (fresh A s).Nonempty) : (stageLimit A).Infinite := by
  apply (stageLimit_infinite_iff hA).mpr
  suffices hcard : ∀ s, s ≤ (A s).card by exact fun n => ⟨n, hcard n⟩
  intro s
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have h := card_fresh_add_card (hA (Nat.le_succ s))
    have hpos := Finset.card_pos.mpr (hstep s)
    omega

/-- **Finite-prefix stabilization.** Under monotone stages, the stages eventually agree with the
limit below any bound `u`. -/
theorem finite_prefix_stabilizes {A : ℕ → Finset ℕ} (hA : Monotone A) (u : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ x, x < u → (x ∈ A s ↔ x ∈ stageLimit A) := by
  classical
  -- All limit members in the finite prefix appear together in one stage.
  obtain ⟨s₀, hs₀⟩ := exists_subset_stage_of_subset_stageLimit (D :=
      (Finset.range u).filter (· ∈ stageLimit A)) hA.directed_le
    fun _ hx => (Finset.mem_filter.mp hx).2
  refine ⟨s₀, fun s hs x hx => ⟨fun h => subset_stageLimit A s h, fun h => ?_⟩⟩
  exact hA hs (hs₀ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, h⟩))

/-- **Reindexing by a clock with cofinal range.** Under monotone stages, reading the stages along a
clock `c` whose range is cofinal, so that every stage is at most some value of `c`, gives the same
limit. The clock need not increase: it may return to small stages infinitely often. -/
theorem stageLimit_comp_of_cofinal {A : ℕ → Finset α} (hA : Monotone A) {c : ℕ → ℕ}
    (hc : ∀ s, ∃ t, s ≤ c t) : stageLimit (A ∘ c) = stageLimit A :=
  -- the coerced stages are monotone sets
  Monotone.iSup_comp_eq (f := fun s => (A s : Set α)) (fun _ _ h => Finset.coe_subset.2 (hA h)) hc

/-- **Stage shifts.** Under monotone stages, dropping the first `k` stages does not change the
limit. -/
theorem stageLimit_shift {A : ℕ → Finset α} (hA : Monotone A) (k : ℕ) :
    stageLimit (fun s => A (s + k)) = stageLimit A :=
  Monotone.iUnion_nat_add (f := fun s => (A s : Set α)) (fun _ _ h => Finset.coe_subset.2 (hA h)) k

/-- **No new entries below `u` between two stages.** Under monotone stages, if nothing below `u`
enters from stage `s` up to a later stage `t`, then below `u` the stages `A s` and `A t` agree. -/
theorem agrees_of_no_fresh_below {A : ℕ → Finset ℕ} (hA : Monotone A) {s t u : ℕ} (hst : s ≤ t)
    (h : ∀ t', s ≤ t' → t' < t → ∀ z, z < u → z ∉ fresh A t') :
    ∀ z, z < u → (z ∈ A s ↔ z ∈ A t) := by
  intro z hz
  refine ⟨fun hzs => hA hst hzs, fun hzt => ?_⟩
  induction t, hst using Nat.le_induction with
  | base => exact hzt
  | succ t hst ih =>
    by_contra hzs
    exact h t hst t.lt_succ_self z hz <| mem_fresh.2 ⟨hzt, fun hzt' =>
      hzs <| ih (fun t' h₁ h₂ => h t' h₁ (h₂.trans t.lt_succ_self)) hzt'⟩

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
