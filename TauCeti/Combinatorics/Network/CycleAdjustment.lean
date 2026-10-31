/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Decomposition

/-!
# Residual cycle adjustments

Let `f` and `g` be assignments of an arrow family `Q` with the same excess at every vertex. Their
residual difference `TauCeti.residualDifference f g` is a nonnegative residual circulation, so any
path–cycle decomposition `D` of it has no paths: it writes the residual difference as a sum of
positively weighted directed cycles `c₀, …, cₙ₋₁` of the residual arrow family. Updating `f` along
these cycles one at a time gives a sequence of assignments `D.cycleUpdate f k`, for `k ≤ n`, which
starts at `f` and ends at `g`.

When `f` and `g` lie between bounds `lo` and `hi`, every assignment of the sequence lies between
the same bounds and has the same excess as `f`, and each step is a residual cycle update within the
residual capacities of the current assignment. So two feasible assignments of the same excess are
connected by finitely many feasible cycle adjustments. If `f` and `g` take values in an additive
subgroup, then so does their residual difference, the cycle weights can be chosen in the subgroup
by `TauCeti.exists_pathCycleDecomposition`, and then every assignment of the sequence takes values
in it too.

The update along the first `k` cycles is defined for a decomposition of any nonnegative residual
assignment `r`; the bounds then only need `r` to be at most the residual capacities of `f`.

## Main definitions

* `TauCeti.PathCycleDecomposition.cycleUpdate D f k`: the residual update of `f` along the first
  `k` cycles of `D`.

## Main results

* `TauCeti.PathCycleDecomposition.cycleUpdate_succ`: each step updates the previous assignment
  along one cycle.
* `TauCeti.PathCycleDecomposition.cycleUpdate_length_residualDifference`: for a decomposition of
  the residual difference between assignments of the same excess, the last assignment is `g`.
* `TauCeti.PathCycleDecomposition.excessAt_cycleUpdate`: every assignment of the sequence has the
  excess of `f`.
* `TauCeti.PathCycleDecomposition.cycleUpdate_mem_Icc`: every assignment of the sequence is
  feasible.
* `TauCeti.PathCycleDecomposition.assignment_mem_Icc_residualCapacity_cycleUpdate`: each cycle lies
  within the residual capacities of the assignment it updates.
* `TauCeti.PathCycleDecomposition.cycleUpdate_mem`: the sequence preserves values in an additive
  subgroup.

## References

* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993, Section 3.5 (flow decomposition and the residual difference
  of two flows).
-/

public section

namespace TauCeti

namespace PathCycleDecomposition

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

section Preorder

variable [Preorder K] {r : Assignment (ResidualHom Q) K} (D : PathCycleDecomposition r)

/-- The residual update of `f` along the first `k` cycles of a path–cycle decomposition `D` of a
residual assignment. For `k` at least the number of cycles, it is the update along all of them. -/
noncomputable def cycleUpdate (f : Assignment Q K) (k : ℕ) : Assignment Q K :=
  residualUpdate f ((D.cycles.take k).map WeightedClosedWalk.assignment).sum

theorem cycleUpdate_def (f : Assignment Q K) (k : ℕ) :
    D.cycleUpdate f k =
      residualUpdate f ((D.cycles.take k).map WeightedClosedWalk.assignment).sum :=
  (rfl)

@[simp]
theorem cycleUpdate_zero (f : Assignment Q K) : D.cycleUpdate f 0 = f := by
  simp [cycleUpdate_def]

/-- Each step of the sequence updates the previous assignment along the next cycle. -/
theorem cycleUpdate_succ (f : Assignment Q K) {k : ℕ} (hk : k < D.cycles.length) :
    D.cycleUpdate f (k + 1) = residualUpdate (D.cycleUpdate f k) D.cycles[k].assignment := by
  rw [cycleUpdate_def, cycleUpdate_def, residualUpdate_residualUpdate, List.take_add_one,
    List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

/-- Once all cycles are used, the sequence is the update along the cycle assignment of `D`. -/
theorem cycleUpdate_of_length_le (f : Assignment Q K) {k : ℕ} (hk : D.cycles.length ≤ k) :
    D.cycleUpdate f k = residualUpdate f D.cycleAssignment := by
  rw [cycleUpdate_def, List.take_of_length_le hk, cycleAssignment_def]

/-- **Excess along cycle adjustments.** Updating along cycles never changes the excess. -/
@[simp]
theorem excessAt_cycleUpdate (f : Assignment Q K) (k : ℕ) (v : V) :
    excessAt (D.cycleUpdate f k) v = excessAt f v :=
  (WeightedClosedWalk.isCirculation_sum_map_assignment _).excessAt_residualUpdate f v

/-- Cycle adjustments preserve values in an additive subgroup containing the values of `f` and the
cycle weights. -/
theorem cycleUpdate_mem {S : Type*} [SetLike S K] [AddSubgroupClass S K] (H : S)
    {f : Assignment Q K} (hf : ∀ ⦃v w⦄ (e : Q v w), f e ∈ H)
    (hD : ∀ c ∈ D.cycles, c.weight ∈ H) (k : ℕ) {v w : V} (e : Q v w) :
    D.cycleUpdate f k e ∈ H := by
  refine residualUpdate_mem H hf (fun _ _ a ↦ ?_) e
  simp only [Pi.list_sum_apply, List.map_map]
  refine list_sum_mem fun _ hx ↦ ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  simp only [Function.comp_apply, WeightedClosedWalk.assignment_def]
  exact walkAssignment_mem c.walk (hD c (List.mem_of_mem_take hc)) a

end Preorder

section PartialOrder

variable [PartialOrder K] [IsOrderedAddMonoid K] {r : Assignment (ResidualHom Q) K}
  (D : PathCycleDecomposition r)

private theorem sum_take_nonneg (k : ℕ) :
    0 ≤ ((D.cycles.take k).map WeightedClosedWalk.assignment).sum :=
  List.sum_nonneg fun _ hx ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact D.assignment_nonneg_of_mem_cycles (List.mem_of_mem_take hc)

private theorem sum_take_le (k : ℕ) :
    ((D.cycles.take k).map WeightedClosedWalk.assignment).sum ≤ r :=
  calc ((D.cycles.take k).map WeightedClosedWalk.assignment).sum
      ≤ (D.cycles.map WeightedClosedWalk.assignment).sum :=
        ((List.take_sublist k D.cycles).map _).sum_le_sum fun _ hx ↦ by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
          exact D.assignment_nonneg_of_mem_cycles hc
    _ = D.cycleAssignment := D.cycleAssignment_def.symm
    _ ≤ r := D.cycleAssignment_le

/-- **Feasibility along cycle adjustments.** If the decomposed residual assignment is at most the
residual capacities of `f`, then every assignment of the sequence lies within the bounds. -/
theorem cycleUpdate_mem_Icc {lo hi f : Assignment Q K} (hr : r ≤ residualCapacity lo hi f)
    (k : ℕ) : D.cycleUpdate f k ∈ Set.Icc lo hi :=
  residualUpdate_mem_Icc ⟨D.sum_take_nonneg k, (D.sum_take_le k).trans hr⟩

/-- Each cycle lies within the residual capacities of the assignment it updates, so every step of
the sequence is a feasible residual cycle update. -/
theorem assignment_mem_Icc_residualCapacity_cycleUpdate {lo hi f : Assignment Q K}
    (hr : r ≤ residualCapacity lo hi f) {k : ℕ} (hk : k < D.cycles.length) :
    D.cycles[k].assignment ∈ Set.Icc 0 (residualCapacity lo hi (D.cycleUpdate f k)) := by
  refine ⟨D.assignment_nonneg_of_mem_cycles (List.getElem_mem hk), fun v w a ↦ ?_⟩
  have hsucc := (D.sum_take_le (k + 1)).trans hr v w a
  rw [List.take_add_one, List.getElem?_eq_getElem hk] at hsucc
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, add_zero, Pi.add_apply] at hsucc
  rw [cycleUpdate_def, residualCapacity_residualUpdate]
  calc D.cycles[k].assignment a
      ≤ residualCapacity lo hi f a - ((D.cycles.take k).map WeightedClosedWalk.assignment).sum a :=
        le_sub_iff_add_le'.2 hsucc
    _ ≤ _ := le_add_of_nonneg_right (D.sum_take_nonneg k _ _ _)

end PartialOrder

section Lattice

variable [Lattice K] [IsOrderedAddMonoid K]

/-- **Residual cycle adjustments end at the target.** For a path–cycle decomposition of the
residual difference from `f` to an assignment `g` of the same excess, updating `f` along all its
cycles gives `g`. -/
theorem cycleUpdate_length_residualDifference {f g : Assignment Q K}
    (hfg : ∀ v, excessAt f v = excessAt g v) (D : PathCycleDecomposition (residualDifference f g)) :
    D.cycleUpdate f D.cycles.length = g := by
  have hpath : D.pathAssignment = 0 := by
    rw [pathAssignment_def, D.paths_eq_nil (isCirculation_residualDifference hfg), List.map_nil,
      List.sum_nil]
  rw [D.cycleUpdate_of_length_le f le_rfl, ← zero_add D.cycleAssignment, ← hpath,
    pathAssignment_add_cycleAssignment, residualUpdate_residualDifference]

end Lattice

end PathCycleDecomposition

end TauCeti
