/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectedness of a graph whose vertices descend to a root

A graph on a well-founded order in which every vertex other than a fixed root has a neighbour
below it is connected: well-founded induction walks every vertex down to the root. Numbering the
vertices of a diagram by `Fin n` so that every nonzero vertex has a neighbour with a smaller
number is what makes connectedness of the Dynkin diagrams, finite and affine alike, a short check.

## Main results

* `SimpleGraph.connected_of_exists_adj_lt`: a graph on a type with a well-founded `<`, in which
  every vertex other than `v₀` has an adjacent vertex below it, is connected.
-/

public section

namespace SimpleGraph

variable {V : Type*} [LT V] [WellFoundedLT V] {G : SimpleGraph V}

/-- **A graph on a well-founded order in which every vertex other than `v₀` has a neighbour below
it is connected.** Every vertex reaches `v₀` by descending along such neighbours. -/
theorem connected_of_exists_adj_lt (v₀ : V) (h : ∀ v ≠ v₀, ∃ w < v, G.Adj w v) :
    G.Connected := by
  refine (connected_iff_exists_forall_reachable G).2 ⟨v₀, fun v ↦ ?_⟩
  induction v using WellFoundedLT.induction with
  | ind v ih =>
    rcases eq_or_ne v v₀ with rfl | hv
    · rfl
    · obtain ⟨w, hwv, hadj⟩ := h v hv
      exact (ih w hwv).trans hadj.reachable

end SimpleGraph
