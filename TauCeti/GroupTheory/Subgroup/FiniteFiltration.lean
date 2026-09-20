/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Finite decreasing filtrations of groups

An antitone sequence of subgroups whose first term is finite is eventually trivial whenever its
intersection is trivial. This elementary observation is useful for ramification filtrations.

## Main results

* `TauCeti.exists_forall_eq_bot_of_antitone_iInf_eq_bot`: a decreasing filtration with finite
  first term and trivial intersection is eventually trivial.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- An antitone sequence of subgroups with finite first term and trivial intersection is
eventually the trivial subgroup. -/
theorem exists_forall_eq_bot_of_antitone_iInf_eq_bot (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] (hInf : ⨅ i, f i = ⊥) : ∃ N, ∀ i, N ≤ i → f i = ⊥ := by
  classical
  let _ := Fintype.ofFinite (f 0)
  have key : ∀ g : f 0, ∃ n : ℕ, ∀ i, n ≤ i → (g : G) ∈ f i → (g : G) = 1 := by
    intro g
    by_cases hg : ∀ i : ℕ, (g : G) ∈ f i
    · exact ⟨0, fun _ _ _ ↦ by
        have : (g : G) ∈ (⊥ : Subgroup G) := by
          rw [← hInf]
          exact Subgroup.mem_iInf.mpr hg
        rwa [Subgroup.mem_bot] at this⟩
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (g : G) ∉ f n := by
        by_contra h
        exact hg fun i ↦ not_not.mp fun hi ↦ h ⟨i, hi⟩
      exact ⟨n, fun i hi hmem ↦ absurd (hf hi hmem) hn⟩
  choose n hn using key
  refine ⟨Finset.univ.sup n, fun i hi ↦ le_bot_iff.mp fun g hg ↦ ?_⟩
  rw [Subgroup.mem_bot]
  let g₀ : f 0 := ⟨g, hf (Nat.zero_le i) hg⟩
  exact hn g₀ i (le_trans (Finset.le_sup (Finset.mem_univ g₀)) hi) hg

end TauCeti
