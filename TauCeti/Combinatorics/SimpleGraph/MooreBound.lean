/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The Moore bound for the diameter

A finite graph whose degrees are at most `k` has, around a fixed vertex `x`, one vertex at
distance `0`, at most `k` vertices at distance `1`, and at most `k (k - 1) ^ i` vertices at
distance `i + 1`: each vertex at distance `i + 1 ≥ 1` has a neighbour at distance `i`, so at most
`k - 1` of its neighbours lie at distance `i + 2`. Summing over the distances up to the
eccentricity of `x`, or up to the diameter of a connected graph, bounds the number of vertices by
the Moore number `1 + k + k (k - 1) + ⋯ + k (k - 1) ^ (d - 1)`.

## Main definitions

* `TauCeti.mooreBound k d`: the Moore number `1 + k ∑_(i < d) (k - 1) ^ i`, with natural-number
  subtraction, so that `mooreBound 0 d = 1`. The lemmas `TauCeti.mooreBound_succ`,
  `TauCeti.mooreBound_two` and `TauCeti.mooreBound_two_left` compute it.

## Main results

* `SimpleGraph.exists_adj_dist_eq_of_dist_eq_add_one`: a vertex at distance `i + 1` from `x` has
  a neighbour at distance `i` from `x`.
* `SimpleGraph.card_filter_dist_eq_add_one_le`: if all degrees are at most `k`, then at most
  `k (k - 1) ^ i` vertices lie at distance `i + 1` from `x`.
* `SimpleGraph.card_le_mooreBound_of_eccent_le`: if all degrees are at most `k` and the
  eccentricity of some vertex is at most `d`, then there are at most `mooreBound k d` vertices.
* `SimpleGraph.card_le_mooreBound`: a connected finite graph whose degrees are at most `k` has at
  most `mooreBound k G.diam` vertices.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012, §12.7,
  pp. 177–178. The book states the bound for `k`-regular graphs; the same count gives it for
  graphs whose degrees are at most `k`.
-/

public section

open Finset

namespace TauCeti

/-- The Moore number
`1 + k ∑_(i < d) (k - 1) ^ i = 1 + k + k (k - 1) + ⋯ + k (k - 1) ^ (d - 1)`, with natural-number
subtraction, so that `mooreBound 0 d = 1`. It bounds the number of vertices of a connected graph
of diameter `d` whose degrees are at most `k`. -/
def mooreBound (k d : ℕ) : ℕ :=
  1 + k * ∑ i ∈ range d, (k - 1) ^ i

variable {k d : ℕ}

/-- The defining formula of `mooreBound`. -/
theorem mooreBound_def : mooreBound k d = 1 + k * ∑ i ∈ range d, (k - 1) ^ i := (rfl)

/-- The Moore number for diameter `0` is `1`. -/
@[simp]
theorem mooreBound_zero : mooreBound k 0 = 1 := by
  simp [mooreBound_def]

/-- The Moore number for `d + 1` adds `k (k - 1) ^ d`, the bound on the number of vertices at
distance `d + 1`, to the Moore number for `d`. -/
theorem mooreBound_succ : mooreBound k (d + 1) = mooreBound k d + k * (k - 1) ^ d := by
  simp only [mooreBound_def, sum_range_succ, mul_add, add_assoc]

/-- The Moore number for diameter `1` is `k + 1`, the number of vertices of `K_(k + 1)`. -/
@[simp]
theorem mooreBound_one : mooreBound k 1 = k + 1 := by
  simp [mooreBound_succ, add_comm]

/-- The Moore number for diameter `2` is `k ^ 2 + 1`. -/
theorem mooreBound_two : mooreBound k 2 = k ^ 2 + 1 := by
  rw [mooreBound_succ, mooreBound_one]
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, pow_one]
    ring

/-- For `k = 0` the Moore number is `1` for every diameter. -/
@[simp]
theorem mooreBound_zero_left : mooreBound 0 d = 1 := by
  simp [mooreBound_def]

/-- For `k = 2` the Moore number is `2 d + 1`, the number of vertices of the cycle of length
`2 d + 1`. -/
theorem mooreBound_two_left : mooreBound 2 d = 2 * d + 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [mooreBound_succ, ih]
    simp only [Nat.reduceSub, one_pow]
    ring

end TauCeti

namespace SimpleGraph

open TauCeti

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex at distance `i + 1` from `x` has a neighbour at distance `i` from `x`. -/
theorem exists_adj_dist_eq_of_dist_eq_add_one {x w : V} {i : ℕ} (h : G.dist x w = i + 1) :
    ∃ u, G.Adj u w ∧ G.dist x u = i := by
  obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist x w ≠ 0)
  cases hq : p.reverse with
  | nil =>
    have := congrArg Walk.length hq
    simp only [Walk.length_reverse, Walk.length_nil] at this
    omega
  | cons hadj q =>
    have hlen : q.length = i := by
      have := congrArg Walk.length hq
      simp only [Walk.length_reverse, Walk.length_cons] at this
      omega
    refine ⟨_, hadj.symm, le_antisymm ?_ ?_⟩
    · rw [dist_comm, ← hlen]
      exact dist_le q
    · have := hadj.symm.reachable.dist_triangle_right x
      rw [dist_eq_one_iff_adj.mpr hadj.symm] at this
      omega

variable [Fintype V] [DecidableRel G.Adj] {k : ℕ}

/-- If all degrees are at most `k`, then at most `k (k - 1) ^ i` vertices lie at distance `i + 1`
from a vertex `x`. -/
theorem card_filter_dist_eq_add_one_le (hdeg : ∀ v, G.degree v ≤ k) (x : V) (i : ℕ) :
    #{v | G.dist x v = i + 1} ≤ k * (k - 1) ^ i := by
  classical
  induction i with
  | zero =>
    calc #{v | G.dist x v = 0 + 1} ≤ #(G.neighborFinset x) :=
          card_le_card fun v hv => by simpa using hv
      _ ≤ k * (k - 1) ^ 0 := by simpa using hdeg x
  | succ i ih =>
    have hsub : ({v | G.dist x v = i + 1 + 1} : Finset V) ⊆
        ({v | G.dist x v = i + 1} : Finset V).biUnion
          fun v => {w ∈ G.neighborFinset v | G.dist x w = i + 1 + 1} := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      obtain ⟨u, hadj, hu⟩ := exists_adj_dist_eq_of_dist_eq_add_one hw
      simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_neighborFinset]
      exact ⟨u, hu, hadj, hw⟩
    have hle : ∀ v ∈ ({v | G.dist x v = i + 1} : Finset V),
        #{w ∈ G.neighborFinset v | G.dist x w = i + 1 + 1} ≤ k - 1 := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨u, hadj, hu⟩ := exists_adj_dist_eq_of_dist_eq_add_one hv
      have hlt : #{w ∈ G.neighborFinset v | G.dist x w = i + 1 + 1} < G.degree v := by
        rw [← card_neighborFinset_eq_degree]
        refine card_lt_card (filter_ssubset.mpr ⟨u, ?_, ?_⟩)
        · simpa using hadj.symm
        · omega
      have := hdeg v
      omega
    calc #{v | G.dist x v = i + 1 + 1}
        ≤ #({v | G.dist x v = i + 1} : Finset V) * (k - 1) :=
          (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ hle)
      _ ≤ k * (k - 1) ^ i * (k - 1) := Nat.mul_le_mul_right _ ih
      _ = k * (k - 1) ^ (i + 1) := by ring

/-- If all degrees are at most `k` and some vertex has eccentricity at most `d`, then the graph
has at most `mooreBound k d` vertices. -/
theorem card_le_mooreBound_of_eccent_le (hdeg : ∀ v, G.degree v ≤ k) {x : V} {d : ℕ}
    (hx : G.eccent x ≤ d) : Fintype.card V ≤ mooreBound k d := by
  classical
  have hedist : ∀ v, G.edist x v ≤ d := fun v => edist_le_eccent.trans hx
  have hreach : ∀ v, G.Reachable x v := fun v =>
    reachable_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top d) (hedist v))
  have hdist : ∀ v, G.dist x v ≤ d := fun v => by
    have := hedist v
    rw [← (hreach v).coe_dist_eq_edist] at this
    exact_mod_cast this
  have hcover : (univ : Finset V) ⊆ (range (d + 1)).biUnion fun i => {v | G.dist x v = i} := by
    intro v _
    simpa [Nat.lt_succ_iff] using hdist v
  have hzero : #{v | G.dist x v = 0} ≤ 1 :=
    card_le_one.mpr fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      rw [(hreach a).dist_eq_zero_iff] at ha
      rw [(hreach b).dist_eq_zero_iff] at hb
      rw [← ha, ← hb]
  calc Fintype.card V = #(univ : Finset V) := card_univ.symm
    _ ≤ ∑ i ∈ range (d + 1), #{v | G.dist x v = i} :=
        (card_le_card hcover).trans card_biUnion_le
    _ = #{v | G.dist x v = 0} + ∑ i ∈ range d, #{v | G.dist x v = i + 1} := by
        rw [sum_range_succ', add_comm]
    _ ≤ 1 + ∑ i ∈ range d, k * (k - 1) ^ i :=
        add_le_add hzero (sum_le_sum fun i _ => card_filter_dist_eq_add_one_le hdeg x i)
    _ = mooreBound k d := by rw [mooreBound_def, mul_sum]

/-- The Moore bound for the diameter: a connected finite graph whose degrees are at most `k` has
at most `1 + k + k (k - 1) + ⋯ + k (k - 1) ^ (D - 1)` vertices, where `D` is its diameter. -/
theorem card_le_mooreBound (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) :
    Fintype.card V ≤ mooreBound k G.diam := by
  have : Nonempty V := hconn.nonempty
  refine card_le_mooreBound_of_eccent_le hdeg (x := Classical.arbitrary V) ?_
  rw [natCast_diam_eq_ediam_iff.mpr (connected_iff_ediam_ne_top.mp hconn)]
  exact eccent_le_ediam

end SimpleGraph
