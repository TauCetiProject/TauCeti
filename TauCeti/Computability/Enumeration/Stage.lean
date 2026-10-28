/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Nat.Find

/-!
# Finite-stage enumerations: limits and fresh entries

An enumeration in finite stages is a sequence `A : ℕ → Finset ℕ`. The numbers **fresh** at stage
`s` are those entering in the transition to stage `s + 1`. When the stages are monotone, a number
is fresh at most once: it has a unique entry stage.

## Main definitions

* `TauCeti.Enumeration.stageLimit`: the set enumerated, the union of all stages.
* `TauCeti.Enumeration.fresh`: the numbers entering in the transition to stage `s + 1`.

## Main results

* `TauCeti.Enumeration.unique_entry_stage`: under monotone stages a number is fresh at most once.
* `TauCeti.Enumeration.exists_mem_fresh_of_mem_stageLimit`: a number of the limit that is not in
  the first stage is fresh at some stage.
* `TauCeti.Enumeration.finite_prefix_stabilizes`: under monotone stages, the stages eventually
  agree with the limit below any bound.
* `TauCeti.Enumeration.stageLimit_comp_of_cofinal`: under monotone stages, reindexing by a
  cofinal clock does not change the limit; in particular neither does shifting the stages.

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

/-- The set enumerated by the stages `A`: the numbers that appear at some stage. -/
def stageLimit (A : ℕ → Finset ℕ) : Set ℕ :=
  {x | ∃ s, x ∈ A s}

/-- Membership in the limit is membership at some stage. -/
@[simp]
theorem mem_stageLimit {A : ℕ → Finset ℕ} {x : ℕ} : x ∈ stageLimit A ↔ ∃ s, x ∈ A s :=
  Iff.rfl

/-- Every stage is contained in the limit. -/
theorem subset_stageLimit (A : ℕ → Finset ℕ) (s : ℕ) : (A s : Set ℕ) ⊆ stageLimit A :=
  fun _ hx => ⟨s, hx⟩

/-- A fresh entry belongs to the limit. -/
theorem mem_stageLimit_of_mem_fresh {A : ℕ → Finset ℕ} {s x : ℕ} (hx : x ∈ fresh A s) :
    x ∈ stageLimit A :=
  ⟨s + 1, (mem_fresh.1 hx).1⟩

/-- **An entry stage.** A number of the limit that is not in the first stage is fresh at some
stage: the stage before the first one containing it. -/
theorem exists_mem_fresh_of_mem_stageLimit {A : ℕ → Finset ℕ} {x : ℕ} (hx : x ∈ stageLimit A)
    (h0 : x ∉ A 0) : ∃ s, x ∈ fresh A s := by
  classical
  have hex : ∃ s, x ∈ A s := hx
  -- the first stage containing `x` is positive
  have hpos : Nat.find hex ≠ 0 := fun h => h0 (h ▸ Nat.find_spec hex)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_one_of_ne_zero hpos
  refine ⟨s, mem_fresh.2 ⟨hs ▸ Nat.find_spec hex, fun hmem => ?_⟩⟩
  have := Nat.find_min' hex hmem
  omega

/-- Under monotone stages, a number is in the limit exactly when it is in every late enough
stage. -/
theorem mem_stageLimit_iff_eventually {A : ℕ → Finset ℕ} (hA : Monotone A) {x : ℕ} :
    x ∈ stageLimit A ↔ ∃ s₀, ∀ s, s₀ ≤ s → x ∈ A s :=
  ⟨fun ⟨s₀, hx⟩ => ⟨s₀, fun _ hs => hA hs hx⟩, fun ⟨s₀, h⟩ => ⟨s₀, h s₀ le_rfl⟩⟩

/-- **Finite-prefix stabilization.** Under monotone stages, the stages eventually agree with the
limit below any bound `u`. -/
theorem finite_prefix_stabilizes {A : ℕ → Finset ℕ} (hA : Monotone A) (u : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ x, x < u → (x ∈ A s ↔ x ∈ stageLimit A) := by
  induction u with
  | zero => exact ⟨0, fun _ _ x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ u ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    -- a stage by which `u` has entered, if it ever does
    obtain ⟨t, ht⟩ : ∃ t, u ∈ stageLimit A → u ∈ A t := by
      by_cases hu : u ∈ stageLimit A
      · obtain ⟨t, ht⟩ := hu
        exact ⟨t, fun _ => ht⟩
      · exact ⟨0, fun h => absurd h hu⟩
    refine ⟨max s₁ t, fun s hs x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
    · exact hs₁ s ((le_max_left _ _).trans hs) x hx
    · exact ⟨fun h => ⟨s, h⟩, fun h => hA ((le_max_right _ _).trans hs) (ht h)⟩

/-- **Reindexing by a cofinal clock.** Under monotone stages, reading the stages along a clock
`c` that eventually passes every stage gives the same limit. -/
theorem stageLimit_comp_of_cofinal {A : ℕ → Finset ℕ} (hA : Monotone A) {c : ℕ → ℕ}
    (hc : ∀ s, ∃ t, s ≤ c t) : stageLimit (A ∘ c) = stageLimit A := by
  ext x
  refine ⟨fun ⟨t, hx⟩ => ⟨c t, hx⟩, fun ⟨s, hx⟩ => ?_⟩
  obtain ⟨t, hst⟩ := hc s
  exact ⟨t, hA hst hx⟩

/-- **Stage shifts.** Under monotone stages, dropping the first `k` stages does not change the
limit. -/
theorem stageLimit_shift {A : ℕ → Finset ℕ} (hA : Monotone A) (k : ℕ) :
    stageLimit (fun s => A (s + k)) = stageLimit A :=
  stageLimit_comp_of_cofinal (c := (· + k)) hA fun s => ⟨s, Nat.le_add_right s k⟩

end Enumeration

end TauCeti
