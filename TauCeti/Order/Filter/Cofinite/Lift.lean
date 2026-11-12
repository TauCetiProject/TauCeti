/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Find

/-!
# Lifting cofinite bounds along a surjection

A countable family can be lifted along a surjection while satisfying every member of a
countable decreasing family of bounds eventually. The bounds may depend on the family index.
This supplies a common diagonal choice for lifting convergent families and coefficients of
weighted restricted series.

`TauCeti.exists_lift_tendsto_cofinite_nhds` is the case of bounds constant in the family index,
taken from an antitone neighbourhood basis.

## Implementation notes

Choose an injection `r : ι → ℕ`, which tends to infinity along the cofinite filter. For each
`α`, choose a lift in the bound indexed by
`Nat.findGreatest (fun m ↦ g α ∈ φ '' V m α) (r α)` whenever that image contains `g α`,
and otherwise use an arbitrary preimage. The cap `r α` makes the search finite even when the
admissible indices are unbounded; `findGreatest` also handles the empty case. For each fixed
`j`, eventually `j ≤ r α` and `g α ∈ φ '' V j α`, so the chosen index is at least `j`.
Antitonicity then puts the chosen lift in `V j α`.
-/

public section

open Filter Set

namespace TauCeti

variable {ι M N : Type*} [Countable ι]

/-- A countable family lifts along a surjection while eventually satisfying every decreasing
bound, if its images eventually lie in the images of those bounds. Bounds may vary with the
family index. -/
theorem exists_lift_eventually_mem_cofinite (φ : M → N) (hsurj : Function.Surjective φ)
    (V : ℕ → ι → Set M) (hV : ∀ α, Antitone (fun n ↦ V n α)) (g : ι → N)
    (hg : ∀ n, ∀ᶠ α in cofinite, g α ∈ φ '' V n α) :
    ∃ f : ι → M, (∀ α, φ (f α) = g α) ∧ ∀ n, ∀ᶠ α in cofinite, f α ∈ V n α := by
  classical
  obtain ⟨r, hr⟩ := exists_injective_nat ι
  have hr' : Tendsto r cofinite atTop := Nat.cofinite_eq_atTop ▸ hr.tendsto_cofinite
  let n (α : ι) := Nat.findGreatest (fun m ↦ g α ∈ φ '' V m α) (r α)
  have hpick : ∀ α, ∃ x, φ x = g α ∧ (g α ∈ φ '' V (n α) α → x ∈ V (n α) α) := by
    intro α
    by_cases h : g α ∈ φ '' V (n α) α
    · obtain ⟨x, hx, hφx⟩ := h
      exact ⟨x, hφx, fun _ ↦ hx⟩
    · obtain ⟨x, hx⟩ := hsurj (g α)
      exact ⟨x, hx, fun hc ↦ (h hc).elim⟩
  choose f hf using hpick
  refine ⟨f, fun α ↦ (hf α).1, fun j ↦ ?_⟩
  filter_upwards [hg j, hr'.eventually_ge_atTop j] with α hα hj
  have hle : j ≤ n α := Nat.le_findGreatest hj hα
  have hspec : g α ∈ φ '' V (n α) α := Nat.findGreatest_spec (P := fun m ↦ g α ∈ φ '' V m α) hj hα
  exact hV α hle ((hf α).2 hspec)

end TauCeti
