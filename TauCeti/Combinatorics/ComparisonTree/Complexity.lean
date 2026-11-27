/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ComparisonTree.Basic

/-!
# Comparison complexity

A problem for comparison trees on `n` items is a set `A` of admissible rankings
`σ : Equiv.Perm (Fin n)` together with a relation `R` between rankings and outputs, `R σ a`
meaning that `a` is a correct output on `σ`. Sorting, for instance, admits all rankings and
relates `σ` only to itself; finding the smallest item relates `σ` to the item of rank `0`.

A tree solves the problem when its output on every admissible ranking is correct
(`TauCeti.CompTree.Solves`). A number `v` is the comparison complexity of the problem
(`TauCeti.IsComparisonComplexity`) when some tree of depth at most `v` solves it and every tree
that solves it makes at least `v` comparisons on some admissible ranking. The first clause is an
upper bound on the depth and the second a lower bound on the cost; since the cost is at most the
depth, each clause is the stronger of its two possible forms.

For a nonempty set of admissible rankings the comparison complexity is the least depth of a tree
that solves the problem (`TauCeti.isComparisonComplexity_iff_isLeast`): pruning the branches that
no admissible ranking follows brings the depth of a solving tree down to its largest cost on an
admissible ranking. With no admissible ranking no number is the comparison complexity.

## Main definitions

* `TauCeti.CompTree.Solves t A R`: the tree `t` solves the problem with admissible rankings `A`
  and correctness relation `R`.
* `TauCeti.IsComparisonComplexity A R v`: `v` is the comparison complexity of that problem.

## Main results

* `TauCeti.IsComparisonComplexity.unique`: a problem has at most one comparison complexity.
* `TauCeti.isComparisonComplexity_iff_isLeast`: for nonempty `A`, the comparison complexity is
  the least depth of a tree that solves the problem.

## References

* Jeff Erickson, *Algorithms*, lecture notes, Lecture 12, "Lower Bounds", §12.2 and §12.5
  (revision of Fall 2013): comparison trees solving a problem and lower bounds on their depth.
-/

public section

namespace TauCeti

universe u

variable {n : ℕ} {α : Type u}

namespace CompTree

/-- The tree `t` solves the problem with admissible rankings `A` and correctness relation `R`:
for every ranking `σ ∈ A`, the output of `t` on `σ` is related to `σ` by `R`. -/
def Solves (t : CompTree n α) (A : Set (Equiv.Perm (Fin n)))
    (R : Equiv.Perm (Fin n) → α → Prop) : Prop :=
  ∀ σ ∈ A, R σ (t.eval ⇑σ)

theorem solves_iff {t : CompTree n α} {A : Set (Equiv.Perm (Fin n))}
    {R : Equiv.Perm (Fin n) → α → Prop} : t.Solves A R ↔ ∀ σ ∈ A, R σ (t.eval ⇑σ) :=
  Iff.rfl

/-- A tree whose output agrees on every admissible ranking with that of a tree solving a problem
solves the problem as well. -/
theorem Solves.of_eval_eq {t t' : CompTree n α} {A : Set (Equiv.Perm (Fin n))}
    {R : Equiv.Perm (Fin n) → α → Prop} (ht : t.Solves A R)
    (h : ∀ σ ∈ A, t'.eval ⇑σ = t.eval ⇑σ) : t'.Solves A R :=
  fun σ hσ => (h σ hσ).symm ▸ ht σ hσ

/-- Pruning for rankings: a tree that solves a problem with a nonempty set of admissible rankings
can be replaced by a tree that solves it, has the same cost on every admissible ranking, and has
as depth the largest cost of the original tree on an admissible ranking. -/
theorem Solves.exists_prune {t : CompTree n α} {A : Set (Equiv.Perm (Fin n))}
    {R : Equiv.Perm (Fin n) → α → Prop} (ht : t.Solves A R) (hA : A.Nonempty) :
    ∃ t' : CompTree n α, t'.Solves A R ∧ (∀ σ ∈ A, t'.cost ⇑σ = t.cost ⇑σ) ∧
      ∃ σ ∈ A, (∀ τ ∈ A, t.cost ⇑τ ≤ t.cost ⇑σ) ∧ t'.depth = t.cost ⇑σ := by
  obtain ⟨t', ht', σ, ⟨σ, hσ, rfl⟩, hmax, hdepth⟩ :=
    t.exists_prune (hA.image fun σ : Equiv.Perm (Fin n) => ⇑σ)
  refine ⟨t', ht.of_eval_eq fun τ hτ => (ht' τ ⟨τ, hτ, rfl⟩).1,
    fun τ hτ => (ht' τ ⟨τ, hτ, rfl⟩).2, σ, hσ, fun τ hτ => hmax τ ⟨τ, hτ, rfl⟩,
    hdepth⟩

end CompTree

/-- The number `v` is the comparison complexity of the problem with admissible rankings `A` and
correctness relation `R`: some tree of depth at most `v` solves the problem, and every tree that
solves it makes at least `v` comparisons on some admissible ranking. -/
structure IsComparisonComplexity (A : Set (Equiv.Perm (Fin n)))
    (R : Equiv.Perm (Fin n) → α → Prop) (v : ℕ) : Prop where
  /-- Some tree of depth at most `v` solves the problem. -/
  exists_solves_depth_le : ∃ t : CompTree n α, t.Solves A R ∧ t.depth ≤ v
  /-- Every tree that solves the problem makes at least `v` comparisons on some admissible
  ranking. -/
  exists_le_cost : ∀ t : CompTree n α, t.Solves A R → ∃ σ ∈ A, v ≤ t.cost ⇑σ

namespace IsComparisonComplexity

variable {A : Set (Equiv.Perm (Fin n))} {R : Equiv.Perm (Fin n) → α → Prop} {v w : ℕ}

/-- A problem that has a comparison complexity has an admissible ranking. -/
theorem nonempty (h : IsComparisonComplexity A R v) : A.Nonempty := by
  obtain ⟨t, ht, -⟩ := h.exists_solves_depth_le
  obtain ⟨σ, hσ, -⟩ := h.exists_le_cost t ht
  exact ⟨σ, hσ⟩

/-- Every tree that solves the problem has depth at least its comparison complexity. -/
theorem le_depth (h : IsComparisonComplexity A R v) {t : CompTree n α} (ht : t.Solves A R) :
    v ≤ t.depth := by
  obtain ⟨σ, -, hσ⟩ := h.exists_le_cost t ht
  exact hσ.trans (t.cost_le_depth _)

/-- A problem has at most one comparison complexity. -/
theorem unique (hv : IsComparisonComplexity A R v) (hw : IsComparisonComplexity A R w) :
    v = w := by
  obtain ⟨t, ht, htv⟩ := hv.exists_solves_depth_le
  obtain ⟨s, hs, hsw⟩ := hw.exists_solves_depth_le
  exact le_antisymm ((hv.le_depth hs).trans hsw) ((hw.le_depth ht).trans htv)

end IsComparisonComplexity

/-- With no admissible ranking no number is the comparison complexity, although every tree solves
the problem. -/
theorem not_isComparisonComplexity_empty (R : Equiv.Perm (Fin n) → α → Prop) (v : ℕ) :
    ¬IsComparisonComplexity ∅ R v :=
  fun h => Set.not_nonempty_empty h.nonempty

/-- For a problem with a nonempty set of admissible rankings, a number is its comparison
complexity exactly when it is the least depth of a tree that solves the problem. -/
theorem isComparisonComplexity_iff_isLeast {A : Set (Equiv.Perm (Fin n))}
    {R : Equiv.Perm (Fin n) → α → Prop} {v : ℕ} (hA : A.Nonempty) :
    IsComparisonComplexity A R v ↔ IsLeast (CompTree.depth '' {t | t.Solves A R}) v := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, fun t ht => ?_⟩⟩
  · obtain ⟨t, ht, htv⟩ := h.exists_solves_depth_le
    exact ⟨t, ht, le_antisymm htv (h.le_depth ht)⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact h.le_depth ht
  · obtain ⟨t, ht, htv⟩ := h.1
    exact ⟨t, ht, htv.le⟩
  · obtain ⟨t', ht', -, σ, hσ, -, hdepth⟩ := ht.exists_prune hA
    exact ⟨σ, hσ, hdepth ▸ h.2 ⟨t', ht', rfl⟩⟩

end TauCeti
