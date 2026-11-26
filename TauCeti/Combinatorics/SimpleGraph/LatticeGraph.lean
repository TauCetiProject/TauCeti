/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Ring.Abs
public import TauCeti.Algebra.BigOperators.Pi

/-!
# The hypercubic lattice `ℤ^d`

The hypercubic lattice is the nearest-neighbour graph `TauCeti.latticeGraph d` on `ℤ^d`, written
`Fin d → ℤ`: two points are adjacent when their `ℓ¹` distance `∑ i, |x i - y i|` is `1`. It is the
graph on which Bernoulli bond percolation is studied.

The adjacency is characterised coordinatewise: the neighbours of `x` are the `2d` points
`x ± eᵢ`, where `eᵢ = Pi.single i 1` is the `i`-th unit vector. The graph is therefore locally
finite and `2d`-regular, and it is connected, since every unit vector is a single step.

## Main definitions

* `TauCeti.latticeGraph d` — the nearest-neighbour graph on `ℤ^d`.

## Main results

* `TauCeti.latticeGraph_adj_iff_exists` — `y` is a neighbour of `x` iff `y = x ± eᵢ` for some `i`;
* `TauCeti.latticeGraph_degree` — every point has exactly `2d` neighbours;
* `TauCeti.connected_latticeGraph` — the lattice is connected;
* `TauCeti.latticeGraph_zero` — `ℤ^0` is a single point and its lattice has no edge.

## References

* G. Grimmett, *Probability on Graphs*, 2nd ed., Cambridge University Press, 2018, Section 3.1.
-/

public section

open Finset SimpleGraph

namespace TauCeti

variable {d : ℕ}

/-- The nearest-neighbour graph on `ℤ^d`: two points are adjacent when their `ℓ¹` distance is
`1`, that is, when they differ by `±1` in exactly one coordinate. -/
def latticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) :=
  SimpleGraph.fromRel fun x y => ∑ i, |x i - y i| = 1

/-- Two points of `ℤ^d` are adjacent exactly when their `ℓ¹` distance is `1`. -/
@[simp]
theorem latticeGraph_adj {x y : Fin d → ℤ} :
    (latticeGraph d).Adj x y ↔ ∑ i, |x i - y i| = 1 := by
  rw [latticeGraph, fromRel_adj]
  refine ⟨fun ⟨_, h⟩ => h.elim id fun h => ?_, fun h => ⟨?_, .inl h⟩⟩
  · simpa only [abs_sub_comm] using h
  · rintro rfl
    simp at h

instance (d : ℕ) : DecidableRel (latticeGraph d).Adj := fun _ _ =>
  decidable_of_iff' _ latticeGraph_adj

/-- The neighbours of `x` in `ℤ^d` are the points `x + eᵢ` and `x - eᵢ`. -/
theorem latticeGraph_adj_iff_exists {x y : Fin d → ℤ} :
    (latticeGraph d).Adj x y ↔ ∃ i, y = x + Pi.single i 1 ∨ y = x - Pi.single i 1 := by
  have h i : |x i - y i| = |(y - x) i| := by simp [abs_sub_comm]
  simp only [latticeGraph_adj, h, sum_abs_eq_one_iff, sub_eq_iff_eq_add', ← sub_eq_add_neg]

/-- `ℤ^0` is a single point, and its lattice has no edge. -/
@[simp]
theorem latticeGraph_zero : latticeGraph 0 = ⊥ := by
  ext x y
  simp

private theorem injective_sumElim_add_sub_single (x : Fin d → ℤ) :
    Function.Injective (Sum.elim (fun i => x + Pi.single i 1) fun i => x - Pi.single i 1) := by
  -- Compare coordinate `i`. Two points `x ± eᵢ`, `x ± eⱼ` with the same sign agree there only if
  -- `i = j`, and points of opposite signs never agree there: `x i + 1 ≠ x i - [j = i]`.
  rintro (i | i) (j | j) h <;>
    · have := congrFun h i
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply, Pi.single_apply] at this
      split_ifs at this <;> first | omega | simp_all

instance (x : Fin d → ℤ) : Fintype ((latticeGraph d).neighborSet x) :=
  Fintype.ofFinset (univ.image (Sum.elim (fun i => x + Pi.single i 1) fun i => x - Pi.single i 1))
    fun y => by
      rw [mem_neighborSet, latticeGraph_adj_iff_exists]
      simp [exists_or, eq_comm]

/-- Every point of `ℤ^d` has exactly `2d` neighbours. -/
@[simp]
theorem latticeGraph_degree (x : Fin d → ℤ) : (latticeGraph d).degree x = 2 * d := by
  rw [← card_neighborSet_eq_degree]
  simp only [Fintype.card_ofFinset]
  rw [card_image_of_injective _ (injective_sumElim_add_sub_single x), card_univ,
    Fintype.card_sum, Fintype.card_fin, two_mul]

private theorem latticeGraph_reachable_add_single (x : Fin d → ℤ) (i : Fin d) (k : ℤ) :
    (latticeGraph d).Reachable x (x + Pi.single i k) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    refine ih.trans (Adj.reachable (latticeGraph_adj_iff_exists.2 ⟨i, .inl ?_⟩))
    rw [Pi.single_add, add_assoc]
  | pred k ih =>
    refine ih.trans (Adj.reachable (latticeGraph_adj_iff_exists.2 ⟨i, .inr ?_⟩))
    rw [Pi.single_sub, add_sub_assoc]

/-- The lattice `ℤ^d` is connected. -/
theorem connected_latticeGraph : (latticeGraph d).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun y => ?_⟩
  have key (s : Finset (Fin d)) : (latticeGraph d).Reachable 0 (∑ i ∈ s, Pi.single i (y i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [sum_insert ha, add_comm]
      exact ih.trans (latticeGraph_reachable_add_single _ a _)
  simpa [Finset.univ_sum_single] using key univ

end TauCeti
