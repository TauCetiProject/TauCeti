/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Nat.Dist

/-!
# Metric bounds for simple graphs

If a `ℕ`-valued vertex labelling changes by at most `1` along every edge of a simple graph `G`,
then the label distance between the endpoints of any walk is at most the length of the walk, and
therefore at most the extended graph distance (and the graph distance between reachable vertices).

## Main results

* `SimpleGraph.Walk.natDist_le_length`: endpoint `Nat.dist` is at most walk length when every
  edge changes the label by at most `1`.
* `SimpleGraph.natDist_le_edist`: endpoint `Nat.dist` is at most `G.edist` under the same edge
  bound.
* `SimpleGraph.natDist_le_dist`: endpoint `Nat.dist` is at most `G.dist` for reachable vertices
  under the same edge bound.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- If a `ℕ`-valued function on vertices changes by at most `1` along every edge of `G`, then the
distance between its endpoint values is at most the length of any walk between them. -/
theorem Walk.natDist_le_length {f : V → ℕ}
    (hf : ∀ ⦃a b : V⦄, G.Adj a b → Nat.dist (f a) (f b) ≤ 1)
    {u v : V} (w : G.Walk u v) : Nat.dist (f u) (f v) ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab _ ih =>
    have hstep := hf hab
    simp only [Walk.length_cons, Nat.dist] at ih hstep ⊢
    omega

/-- If a `ℕ`-valued function on vertices changes by at most `1` along every edge of `G`, then the
distance between its values at two vertices is at most their extended graph distance. -/
theorem natDist_le_edist {f : V → ℕ}
    (hf : ∀ ⦃a b : V⦄, G.Adj a b → Nat.dist (f a) (f b) ≤ 1)
    (u v : V) : (Nat.dist (f u) (f v) : ℕ∞) ≤ G.edist u v :=
  le_iInf fun w ↦ Nat.cast_le.2 (w.natDist_le_length hf)

/-- If a `ℕ`-valued function on vertices changes by at most `1` along every edge of `G`, then the
distance between its values at two reachable vertices is at most their graph distance. -/
theorem natDist_le_dist {f : V → ℕ}
    (hf : ∀ ⦃a b : V⦄, G.Adj a b → Nat.dist (f a) (f b) ≤ 1)
    {u v : V} (huv : G.Reachable u v) : Nat.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨w, hw⟩ := huv.exists_walk_length_eq_dist
  exact hw ▸ w.natDist_le_length hf

end SimpleGraph
