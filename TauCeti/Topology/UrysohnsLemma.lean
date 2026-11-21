/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.UrysohnsLemma

/-!
# Urysohn cutoffs along a compact exhaustion

On a locally compact R₁ space, every compact exhaustion `K` carries continuous cutoffs `g j`
with values in `[0, 1]`, equal to one on `K j` and supported in `K (j + 1)`
(`CompactExhaustion.exists_cutoffs`).
-/

public section

open Set

/-- Cutoffs along a compact exhaustion: continuous functions with values in `[0, 1]`, equal to
one on `K j` and with topological support in `K (j + 1)`. -/
theorem CompactExhaustion.exists_cutoffs {X : Type*} [TopologicalSpace X] [R1Space X]
    [LocallyCompactSpace X] (K : CompactExhaustion X) :
    ∃ g : ℕ → C(X, ℝ), (∀ j, EqOn (g j) 1 (K j)) ∧ (∀ j, tsupport (g j) ⊆ K (j + 1)) ∧
      ∀ j x, g j x ∈ Icc 0 1 := by
  have hg (j : ℕ) : ∃ g : C(X, ℝ), EqOn g 1 (K j) ∧ tsupport g ⊆ K (j + 1) ∧
      ∀ x, g x ∈ Icc 0 1 := by
    obtain ⟨g, hg1, -, hgs, hgr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      (K.isCompact j) isOpen_interior (K.subset_interior_succ j)
    exact ⟨g, hg1, hgs.trans interior_subset, hgr⟩
  choose g hg1 hgs hgr using hg
  exact ⟨g, hg1, hgs, hgr⟩
