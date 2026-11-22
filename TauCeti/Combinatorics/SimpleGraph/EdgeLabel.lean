/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Involution edge labellings of simple graphs

Pointwise identities for `{1, c}`-valued edge labellings of a `SimpleGraph V` when `c * c = 1`:

* `SimpleGraph.ite_adj_eq_inv_of_mul_self_eq_one`: reversing `(u, v)` inverts
  `if G.Adj u v then c else 1`.
* `SimpleGraph.ite_mem_inv_mul_ite_adj_mul`: conjugating the `{1, c}`-labelling of `G` by the
  `{1, c}`-indicator of `S` switches `G` by the complete-graph cut
  `(⊤ : SimpleGraph V).between S Sᶜ`.
* `SimpleGraph.ite_adj_mul_ite_adj_mul_ite_adj`: the directed product around `(u, v, w)` equals
  `c` when an odd number of pairs among `(u, v)`, `(v, w)`, and `(w, u)` are adjacent in `G`, and
  `1` otherwise.
-/

public section

open scoped symmDiff

namespace SimpleGraph

section Involution

variable {V Γ : Type*}

/-- When `c * c = 1`, reversing `(u, v)` inverts `if G.Adj u v then c else 1`. -/
theorem ite_adj_eq_inv_of_mul_self_eq_one [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v : V) :
    (if G.Adj v u then c else 1) = (if G.Adj u v then c else 1)⁻¹ := by
  simp only [G.adj_comm]
  split_ifs <;> simp [inv_eq_of_mul_eq_one_right hc]

/-- Conjugating an involution edge labelling of `G` by the `{1, c}`-valued indicator of `S` switches
`G` by the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ`. -/
theorem ite_mem_inv_mul_ite_adj_mul [DecidableEq V] [Group Γ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (S : Set V) [DecidablePred (· ∈ S)] (u v : V) :
    (if u ∈ S then c else 1)⁻¹ * (if G.Adj u v then c else 1) * (if v ∈ S then c else 1) =
      if (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj u v then c else 1 := by
  simp only [symmDiff_adj, top_between_compl_adj]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hadj : G.Adj u v <;>
    simp [hu, hv, hadj, hc, inv_eq_of_mul_eq_one_right hc]

/-- When `c * c = 1`, the directed product around `(u, v, w)` equals `c` if an odd number of the
pairs `(u, v)`, `(v, w)`, and `(w, u)` are adjacent in `G` (equivalently, if `{u, v, w}` spans an
odd number of edges when `u`, `v`, `w` are pairwise distinct), and `1` otherwise. -/
theorem ite_adj_mul_ite_adj_mul_ite_adj [Monoid Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v w : V) :
    (if G.Adj u v then c else 1) * (if G.Adj v w then c else 1) * (if G.Adj w u then c else 1) =
      if Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) then c else 1 := by
  by_cases h1 : G.Adj u v <;> by_cases h2 : G.Adj v w <;> by_cases h3 : G.Adj w u <;>
    simp [h1, h2, h3, hc]

end Involution

end SimpleGraph
