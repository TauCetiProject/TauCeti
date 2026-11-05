/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Orthogonality for additive valuations

A finite sum of elements with pairwise distinct finite additive valuations has valuation equal to
the least valuation of its terms. Terms of infinite valuation, such as zero terms, cause no
exception, so the same formula also covers a family all of whose terms have infinite valuation.

This is the elementary nonarchimedean orthogonality principle used, for the additive valuation of
a discrete valuation ring, for power bases whose terms have valuations in distinct congruence
classes.
-/

public section

namespace AddValuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] (v : AddValuation R Γ₀)

/-- The additive valuation of a finite sum of terms with pairwise distinct finite valuations is the
infimum of their valuations. -/
theorem map_sum_eq_inf_of_ne {ι : Type*} (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) ≠ ⊤ → v (f j) ≠ ⊤ → v (f i) ≠ v (f j)) :
    v (∑ i ∈ s, f i) = s.inf fun i ↦ v (f i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨j, hj, hjmin⟩ := s.exists_min_image (fun i ↦ v (f i)) hs
  rw [le_antisymm (Finset.inf_le hj) (Finset.le_inf hjmin)]
  rcases eq_or_ne (v (f j)) ⊤ with htop | htop
  · rw [htop, ← top_le_iff, ← htop]
    exact v.map_le_sum hjmin
  refine v.toValuation.map_sum_eq_of_lt hj fun i hi ↦ ?_
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  refine (lt_of_le_of_ne (hjmin i hi.1) fun heq ↦ ?_).dual
  exact h i hi.1 j hj hi.2 (heq ▸ htop) htop heq.symm

end AddValuation
