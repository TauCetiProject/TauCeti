/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Totally bounded sets from Cauchy subsequences

A subset `s` of a uniform space is totally bounded as soon as every sequence in `s` has a Cauchy
subsequence (`TauCeti.totallyBounded_of_forall_exists_cauchySeq`). In a complete space this gives a
sequential criterion for relative compactness in which the limits of the subsequences need not lie
in `s`; compare `IsSeqCompact.totallyBounded`, which asks for subsequences converging in `s`.
-/

public section

open Filter Set

namespace TauCeti

variable {α : Type*} [UniformSpace α] {s : Set α}

/-- A set in which every sequence has a Cauchy subsequence is totally bounded. -/
theorem totallyBounded_of_forall_exists_cauchySeq
    (h : ∀ u : ℕ → α, (∀ n, u n ∈ s) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (u ∘ φ)) :
    TotallyBounded s := by
  intro V hV
  by_contra! hcov
  -- A sequence in `s` whose terms avoid the `V`-balls around all earlier terms.
  obtain ⟨u, hus, hu⟩ :
      ∃ u : ℕ → α, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u n ∉ SetRel.ball V (u m) := by
    have hcov' : ∀ t : Set α, t.Finite → ∃ a ∈ s, ∀ b ∈ t, a ∉ SetRel.ball V b := fun t ht ↦ by
      obtain ⟨a, has, ha⟩ := not_subset.1 (hcov t ht)
      exact ⟨a, has, fun b hb hab ↦ ha (mem_iUnion₂.2 ⟨b, hb, hab⟩)⟩
    simpa only [forall_and, forall_mem_image, not_and, mem_Iio] using
      seq_of_forall_finite_exists hcov'
  obtain ⟨φ, hφ, hcauchy⟩ := h u hus
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    hcauchy.mem_entourage hV
  exact hu (φ (N + 1)) (φ N) (hφ (Nat.lt_add_one N)) (hN (N + 1) N N.le_succ le_rfl)

end TauCeti
