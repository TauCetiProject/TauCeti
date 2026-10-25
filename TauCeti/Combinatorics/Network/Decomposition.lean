/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import TauCeti.Combinatorics.Network.Augmentation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int

/-!
# Path–cycle decomposition of nonnegative arrow assignments

Every nonnegative arrow assignment `f` on a finite arrow family is a finite sum of positively
weighted directed paths and directed cycles, with equality on every arrow. No conservation or
capacity condition is needed: each path runs from a vertex of negative excess of `f` (a supply
vertex) to a vertex of positive excess (a demand vertex), and its interior vertices are
unrestricted. The total weight of the paths leaving a supply vertex is minus its excess, the total
weight of the paths entering a demand vertex is its excess, and every component is bounded
arrowwise by `f`. A walk of weight `q` contributes `n • q` to an arrow it traverses `n` times, as
in `TauCeti.walkAssignment`, so the theory needs no multiplicative unit; paths and cycles traverse
each arrow at most once.

There is such a decomposition with at most as many components as arrows of positive value, and
with all weights in any additive subgroup containing the values of `f`. For an ordinary `s`–`t`
flow every path of a decomposition runs from `s` to `t`, and the path weights add up to the value
of the flow; for a circulation there are no paths at all.

## Main definitions

* `TauCeti.WeightedWalk` and `TauCeti.WeightedClosedWalk`: directed walks and closed walks with a
  weight, and their assignments.
* `TauCeti.PathCycleDecomposition f`: a decomposition of `f` into positively weighted directed
  paths from supply to demand vertices and positively weighted directed cycles.
* `TauCeti.PathCycleDecomposition.pathAssignment` and
  `TauCeti.PathCycleDecomposition.cycleAssignment`: the sums of the path and cycle components.

## Main results

* `TauCeti.exists_pathCycleDecomposition`: every nonnegative assignment has a path–cycle
  decomposition with at most as many components as arrows of positive value, all of whose weights
  lie in any given additive subgroup containing the values of the assignment.
* `TauCeti.PathCycleDecomposition.sum_weight_filter_source_eq_negPart` and
  `TauCeti.PathCycleDecomposition.sum_weight_filter_target_eq_posPart`: the supply and demand
  identities.
* `TauCeti.PathCycleDecomposition.assignment_le_of_mem_paths` and
  `TauCeti.PathCycleDecomposition.assignment_le_of_mem_cycles`: every component is bounded
  arrowwise by the decomposed assignment.
* `TauCeti.PathCycleDecomposition.paths_eq_nil`: a decomposition of a circulation consists of
  cycles only.
* `TauCeti.PathCycleDecomposition.source_eq_of_mem_paths`,
  `TauCeti.PathCycleDecomposition.target_eq_of_mem_paths` and
  `TauCeti.PathCycleDecomposition.sum_weight_paths_eq_val`: the decomposition of an ordinary
  `s`–`t` flow, whose paths run from `s` to `t` with total weight the value of the flow.
* `TauCeti.PathCycleDecomposition.pathAssignment_apply_le_val`: the path components of a
  decomposition of an ordinary flow carry at most its value on every arrow.
* `TauCeti.Flow.exists_paths_card_eq_val`: an integer `s`–`t` flow carrying at most one unit on
  every arrow carries as many arrow-disjoint `s`–`t` paths as its value.

## Implementation notes

The decomposition is built by peeling off one weighted path or cycle at a time. If the arrows of
positive value contain a directed cycle, that cycle is subtracted with its bottleneck as weight;
otherwise a path of positive arrows from a vertex that no positive arrow enters to a vertex that no
positive arrow leaves is subtracted with its bottleneck as weight. Each step makes the value of a
positive arrow zero, which bounds the number of components, and each weight is a value of the
current assignment, which keeps the weights in the subgroup.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993, Section 3.5.
-/

public section

namespace TauCeti

open Finset Relation

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- A directed walk along the arrow family `Q`, together with its endpoints and a weight. -/
structure WeightedWalk (Q : V → V → Type v) (K : Type w) where
  /-- The first vertex of the walk. -/
  source : V
  /-- The last vertex of the walk. -/
  target : V
  /-- The walk itself. -/
  walk : ArrowWalk Q source target
  /-- The weight of the walk. -/
  weight : K

/-- A closed directed walk along the arrow family `Q`, together with its base vertex and a
weight. -/
structure WeightedClosedWalk (Q : V → V → Type v) (K : Type w) where
  /-- The first and last vertex of the closed walk. -/
  base : V
  /-- The closed walk itself. -/
  walk : ArrowWalk Q base base
  /-- The weight of the closed walk. -/
  weight : K

section AddCommMonoid

variable [AddCommMonoid K]

/-- The assignment of a weighted walk: its walk weighted by its weight. -/
noncomputable def WeightedWalk.assignment (p : WeightedWalk Q K) : Assignment Q K :=
  walkAssignment p.walk p.weight

theorem WeightedWalk.assignment_def (p : WeightedWalk Q K) :
    p.assignment = walkAssignment p.walk p.weight :=
  (rfl)

/-- The assignment of a weighted closed walk: its walk weighted by its weight. -/
noncomputable def WeightedClosedWalk.assignment (c : WeightedClosedWalk Q K) : Assignment Q K :=
  walkAssignment c.walk c.weight

theorem WeightedClosedWalk.assignment_def (c : WeightedClosedWalk Q K) :
    c.assignment = walkAssignment c.walk c.weight :=
  (rfl)

end AddCommMonoid

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- The excess at `v` of a sum of weighted walks is the total weight of the walks ending at `v`
minus the total weight of the walks starting at `v`. -/
theorem WeightedWalk.excessAt_sum_map_assignment [DecidableEq V] (l : List (WeightedWalk Q K))
    (v : V) :
    excessAt (l.map WeightedWalk.assignment).sum v =
      ((l.filter fun p ↦ p.target = v).map WeightedWalk.weight).sum -
        ((l.filter fun p ↦ p.source = v).map WeightedWalk.weight).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, excessAt_add, ih, assignment_def, excessAt_walkAssignment]
    by_cases hs : p.source = v <;> by_cases ht : p.target = v <;>
      simp [hs, ht, Ne.symm] <;> abel

/-- The excess of a sum of weighted closed walks vanishes. -/
theorem WeightedClosedWalk.isCirculation_sum_map_assignment (l : List (WeightedClosedWalk Q K)) :
    IsCirculation (l.map WeightedClosedWalk.assignment).sum :=
  (isCirculation_iff_mem_ker _).2 <| list_sum_mem fun _ hx ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact (isCirculation_iff_mem_ker _).1 (isCirculation_walkAssignment c.walk c.weight)

/-- A *path–cycle decomposition* of the arrow assignment `f`: finite lists of positively weighted
directed paths and positively weighted directed cycles whose assignments add up to `f`, such that
every path starts at a vertex of negative excess of `f` and ends at a vertex of positive excess
of `f`. -/
@[ext]
structure PathCycleDecomposition [Preorder K] (f : Assignment Q K) where
  /-- The weighted paths. -/
  paths : List (WeightedWalk Q K)
  /-- The weighted cycles. -/
  cycles : List (WeightedClosedWalk Q K)
  /-- Every path component is a directed path. -/
  isPath_walk : ∀ p ∈ paths, p.walk.IsPath
  /-- Every cycle component is a directed cycle. -/
  isCycle_walk : ∀ c ∈ cycles, c.walk.IsCycle
  /-- Every path component has positive weight. -/
  weight_pos_of_mem_paths : ∀ p ∈ paths, 0 < p.weight
  /-- Every cycle component has positive weight. -/
  weight_pos_of_mem_cycles : ∀ c ∈ cycles, 0 < c.weight
  /-- Every path starts at a vertex of negative excess. -/
  excessAt_source_neg : ∀ p ∈ paths, excessAt f p.source < 0
  /-- Every path ends at a vertex of positive excess. -/
  excessAt_target_pos : ∀ p ∈ paths, 0 < excessAt f p.target
  /-- The components add up to the decomposed assignment. -/
  sum_paths_add_sum_cycles :
    (paths.map WeightedWalk.assignment).sum + (cycles.map WeightedClosedWalk.assignment).sum = f

namespace PathCycleDecomposition

section Preorder

variable [Preorder K] {f : Assignment Q K} (D : PathCycleDecomposition f)

/-- The sum of the path components of a decomposition. -/
noncomputable def pathAssignment : Assignment Q K :=
  (D.paths.map WeightedWalk.assignment).sum

/-- The sum of the cycle components of a decomposition. -/
noncomputable def cycleAssignment : Assignment Q K :=
  (D.cycles.map WeightedClosedWalk.assignment).sum

theorem pathAssignment_def : D.pathAssignment = (D.paths.map WeightedWalk.assignment).sum :=
  (rfl)

theorem cycleAssignment_def :
    D.cycleAssignment = (D.cycles.map WeightedClosedWalk.assignment).sum :=
  (rfl)

@[simp]
theorem pathAssignment_add_cycleAssignment : D.pathAssignment + D.cycleAssignment = f :=
  D.sum_paths_add_sum_cycles

/-- The cycle components form a circulation. -/
theorem isCirculation_cycleAssignment : IsCirculation D.cycleAssignment :=
  WeightedClosedWalk.isCirculation_sum_map_assignment _

/-- The path components have the same excess as the decomposed assignment. -/
@[simp]
theorem excessAt_pathAssignment (v : V) : excessAt D.pathAssignment v = excessAt f v := by
  conv_rhs => rw [← D.pathAssignment_add_cycleAssignment]
  rw [excessAt_add, (isCirculation_iff _).1 D.isCirculation_cycleAssignment, add_zero]

/-- The excess of the decomposed assignment at `v` is the total weight of the paths ending at `v`
minus the total weight of the paths starting at `v`. -/
theorem excessAt_eq_sum_sub_sum [DecidableEq V] (v : V) :
    excessAt f v = ((D.paths.filter fun p ↦ p.target = v).map WeightedWalk.weight).sum -
      ((D.paths.filter fun p ↦ p.source = v).map WeightedWalk.weight).sum := by
  rw [← D.excessAt_pathAssignment, pathAssignment_def,
    WeightedWalk.excessAt_sum_map_assignment]

/-- No path of a decomposition starts at a vertex of nonnegative excess. -/
theorem source_ne_of_mem_paths {p : WeightedWalk Q K} (hp : p ∈ D.paths) {v : V}
    (hv : 0 ≤ excessAt f v) : p.source ≠ v := by
  rintro rfl
  exact (D.excessAt_source_neg p hp).not_ge hv

/-- No path of a decomposition ends at a vertex of nonpositive excess. -/
theorem target_ne_of_mem_paths {p : WeightedWalk Q K} (hp : p ∈ D.paths) {v : V}
    (hv : excessAt f v ≤ 0) : p.target ≠ v := by
  rintro rfl
  exact (D.excessAt_target_pos p hp).not_ge hv

/-- A decomposition of a circulation has no path components. -/
theorem paths_eq_nil (hf : IsCirculation f) : D.paths = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun p hp ↦
    D.source_ne_of_mem_paths hp ((isCirculation_iff f).1 hf p.source).ge rfl

end Preorder

section PartialOrder

variable [PartialOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}
  (D : PathCycleDecomposition f)

theorem assignment_nonneg_of_mem_paths {p : WeightedWalk Q K} (hp : p ∈ D.paths) :
    0 ≤ p.assignment :=
  walkAssignment_nonneg _ (D.weight_pos_of_mem_paths p hp).le

theorem assignment_nonneg_of_mem_cycles {c : WeightedClosedWalk Q K} (hc : c ∈ D.cycles) :
    0 ≤ c.assignment :=
  walkAssignment_nonneg _ (D.weight_pos_of_mem_cycles c hc).le

theorem pathAssignment_nonneg : 0 ≤ D.pathAssignment :=
  List.sum_nonneg <| by simpa using fun p hp ↦ D.assignment_nonneg_of_mem_paths hp

theorem cycleAssignment_nonneg : 0 ≤ D.cycleAssignment :=
  List.sum_nonneg <| by simpa using fun c hc ↦ D.assignment_nonneg_of_mem_cycles hc

include D in
/-- An assignment with a path–cycle decomposition is nonnegative. -/
theorem nonneg : 0 ≤ f := by
  rw [← D.pathAssignment_add_cycleAssignment]
  exact add_nonneg D.pathAssignment_nonneg D.cycleAssignment_nonneg

theorem pathAssignment_le : D.pathAssignment ≤ f := by
  conv_rhs => rw [← D.pathAssignment_add_cycleAssignment]
  exact le_add_of_nonneg_right D.cycleAssignment_nonneg

theorem cycleAssignment_le : D.cycleAssignment ≤ f := by
  conv_rhs => rw [← D.pathAssignment_add_cycleAssignment]
  exact le_add_of_nonneg_left D.pathAssignment_nonneg

/-- Every path component is bounded arrowwise by the decomposed assignment. -/
theorem assignment_le_of_mem_paths {p : WeightedWalk Q K} (hp : p ∈ D.paths) :
    p.assignment ≤ f :=
  (List.single_le_sum (by simpa using fun p hp ↦ D.assignment_nonneg_of_mem_paths hp) _
    (List.mem_map_of_mem hp)).trans D.pathAssignment_le

/-- Every cycle component is bounded arrowwise by the decomposed assignment. -/
theorem assignment_le_of_mem_cycles {c : WeightedClosedWalk Q K} (hc : c ∈ D.cycles) :
    c.assignment ≤ f :=
  (List.single_le_sum (by simpa using fun c hc ↦ D.assignment_nonneg_of_mem_cycles hc) _
    (List.mem_map_of_mem hc)).trans D.cycleAssignment_le

/-- Every arrow of a cycle component has positive value in the decomposed assignment. -/
theorem pos_of_mem_arrows_of_mem_cycles {c : WeightedClosedWalk Q K} (hc : c ∈ D.cycles)
    {a : Σ x y, Q x y} (ha : a ∈ c.walk.arrows) : 0 < f a.2.2 := by
  have hle := D.assignment_le_of_mem_cycles hc a.1 a.2.1 a.2.2
  rw [WeightedClosedWalk.assignment_def,
    walkAssignment_eq_of_mem (D.isCycle_walk c hc).nodup_arrows _ ha] at hle
  exact (D.weight_pos_of_mem_cycles c hc).trans_le hle

/-- A decomposition has no components exactly when it decomposes the zero assignment. -/
theorem paths_eq_nil_and_cycles_eq_nil_iff : D.paths = [] ∧ D.cycles = [] ↔ f = 0 := by
  constructor
  · rintro ⟨hp, hc⟩
    rw [← D.pathAssignment_add_cycleAssignment, pathAssignment_def, cycleAssignment_def, hp, hc]
    simp
  · rintro rfl
    refine ⟨D.paths_eq_nil isCirculation_zero, List.eq_nil_iff_forall_not_mem.2 fun c hc ↦ ?_⟩
    have hcyc := D.isCycle_walk c hc
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c.walk.arrows hcyc.arrows_ne_nil
    simpa using D.pos_of_mem_arrows_of_mem_cycles hc ha

end PartialOrder

/-! ### Decompositions of ordinary flows -/

section Flow

variable {cap : Assignment Q K} {s t : V}

/-- Every path of a decomposition of an ordinary `s`–`t` flow starts at `s`. -/
theorem source_eq_of_mem_paths [Preorder K] {f : Flow cap s t} (D : PathCycleDecomposition f.toFun)
    {p : WeightedWalk Q K} (hp : p ∈ D.paths) : p.source = s := by
  by_contra h
  refine D.source_ne_of_mem_paths hp ?_ rfl
  by_cases ht : p.source = t
  · rw [ht]
    exact f.excessAt_sink_nonneg
  · exact (f.conserve _ h ht).ge

/-- Every path of a decomposition of an ordinary `s`–`t` flow ends at `t`. -/
theorem target_eq_of_mem_paths [PartialOrder K] [IsOrderedAddMonoid K] {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) {p : WeightedWalk Q K} (hp : p ∈ D.paths) :
    p.target = t := by
  by_contra h
  refine D.target_ne_of_mem_paths hp ?_ rfl
  by_cases hs : p.target = s
  · rw [hs, f.excessAt_source]
    exact neg_nonpos.2 f.val_nonneg
  · exact (f.conserve _ hs h).le

/-- The path weights of a decomposition of an ordinary `s`–`t` flow add up to its value. -/
theorem sum_weight_paths_eq_val [PartialOrder K] [IsOrderedAddMonoid K] {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) : (D.paths.map WeightedWalk.weight).sum = f.val := by
  classical
  have hs : (D.paths.filter fun p ↦ p.source = t) = [] :=
    List.filter_eq_nil_iff.2 fun p hp ↦ by
      simpa using D.source_ne_of_mem_paths hp f.excessAt_sink_nonneg
  have ht : (D.paths.filter fun p ↦ p.target = t) = D.paths :=
    List.filter_eq_self.2 fun p hp ↦ decide_eq_true (D.target_eq_of_mem_paths hp)
  rw [f.val_def]
  simpa [hs, ht] using (D.excessAt_eq_sum_sub_sum t).symm

/-- The path components of a decomposition of an ordinary `s`–`t` flow carry at most the value of
the flow on every arrow. -/
theorem pathAssignment_apply_le_val [PartialOrder K] [IsOrderedAddMonoid K] {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) {x y : V} (e : Q x y) : D.pathAssignment e ≤ f.val := by
  rw [← D.sum_weight_paths_eq_val, pathAssignment_def]
  simp only [Pi.list_sum_apply, List.map_map, Function.comp_def, WeightedWalk.assignment_def]
  refine List.sum_le_sum fun p hp ↦ ?_
  have hq := (D.weight_pos_of_mem_paths p hp).le
  exact (walkAssignment_mem_Icc (D.isPath_walk p hp).nodup_arrows hq (fun _ _ _ ↦ hq)
    fun _ _ ↦ le_rfl).2 _ _ e

end Flow

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}
  (D : PathCycleDecomposition f)

/-- **Supply identity.** The total weight of the paths starting at `v` is the negative part of the
excess at `v`: minus the excess at a supply vertex, and zero elsewhere. -/
theorem sum_weight_filter_source_eq_negPart [DecidableEq V] (v : V) :
    ((D.paths.filter fun p ↦ p.source = v).map WeightedWalk.weight).sum = (excessAt f v)⁻ := by
  rcases le_total 0 (excessAt f v) with hv | hv
  · rw [negPart_eq_zero.2 hv, List.filter_eq_nil_iff.2 fun p hp ↦ by
      simpa using D.source_ne_of_mem_paths hp hv]
    simp
  · have h : (D.paths.filter fun p ↦ p.target = v) = [] :=
      List.filter_eq_nil_iff.2 fun p hp ↦ by simpa using D.target_ne_of_mem_paths hp hv
    rw [negPart_eq_neg.2 hv, D.excessAt_eq_sum_sub_sum v, h]
    simp

omit [IsOrderedAddMonoid K] in
/-- **Demand identity.** The total weight of the paths ending at `v` is the positive part of the
excess at `v`: the excess at a demand vertex, and zero elsewhere. -/
theorem sum_weight_filter_target_eq_posPart [DecidableEq V] (v : V) :
    ((D.paths.filter fun p ↦ p.target = v).map WeightedWalk.weight).sum = (excessAt f v)⁺ := by
  rcases le_total (excessAt f v) 0 with hv | hv
  · rw [posPart_eq_zero.2 hv, List.filter_eq_nil_iff.2 fun p hp ↦ by
      simpa using D.target_ne_of_mem_paths hp hv]
    simp
  · have h : (D.paths.filter fun p ↦ p.source = v) = [] :=
      List.filter_eq_nil_iff.2 fun p hp ↦ by simpa using D.source_ne_of_mem_paths hp hv
    rw [posPart_eq_self.2 hv, D.excessAt_eq_sum_sub_sum v, h]
    simp

end LinearOrder

end PathCycleDecomposition

/-! ### Existence -/

section Existence

variable [LinearOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}

/-- Adding a positively weighted cycle to a decomposed assignment. -/
private def PathCycleDecomposition.consCycle {g : Assignment Q K} (D : PathCycleDecomposition g)
    (c : WeightedClosedWalk Q K) (hc : c.walk.IsCycle) (hpos : 0 < c.weight)
    (hfg : f = g + c.assignment) : PathCycleDecomposition f where
  paths := D.paths
  cycles := c :: D.cycles
  isPath_walk := D.isPath_walk
  isCycle_walk := List.forall_mem_cons.2 ⟨hc, D.isCycle_walk⟩
  weight_pos_of_mem_paths := D.weight_pos_of_mem_paths
  weight_pos_of_mem_cycles := List.forall_mem_cons.2 ⟨hpos, D.weight_pos_of_mem_cycles⟩
  excessAt_source_neg p hp := by
    rw [hfg, excessAt_add, WeightedClosedWalk.assignment_def,
      (isCirculation_iff _).1 (isCirculation_walkAssignment _ _), add_zero]
    exact D.excessAt_source_neg p hp
  excessAt_target_pos p hp := by
    rw [hfg, excessAt_add, WeightedClosedWalk.assignment_def,
      (isCirculation_iff _).1 (isCirculation_walkAssignment _ _), add_zero]
    exact D.excessAt_target_pos p hp
  sum_paths_add_sum_cycles := by
    rw [hfg, List.map_cons, List.sum_cons]
    conv_rhs => rw [← D.sum_paths_add_sum_cycles]
    abel

/-- Adding a positively weighted path to a decomposed assignment, when the path runs from a
vertex of negative excess to one of positive excess and no vertex changes from negative or
positive excess to the opposite sign. -/
private def PathCycleDecomposition.consPath {g : Assignment Q K} (D : PathCycleDecomposition g)
    (p : WeightedWalk Q K) (hp : p.walk.IsPath) (hpos : 0 < p.weight)
    (hs : excessAt f p.source < 0) (ht : 0 < excessAt f p.target)
    (hneg : ∀ v, excessAt g v < 0 → excessAt f v < 0)
    (hpos' : ∀ v, 0 < excessAt g v → 0 < excessAt f v) (hfg : f = g + p.assignment) :
    PathCycleDecomposition f where
  paths := p :: D.paths
  cycles := D.cycles
  isPath_walk := List.forall_mem_cons.2 ⟨hp, D.isPath_walk⟩
  isCycle_walk := D.isCycle_walk
  weight_pos_of_mem_paths := List.forall_mem_cons.2 ⟨hpos, D.weight_pos_of_mem_paths⟩
  weight_pos_of_mem_cycles := D.weight_pos_of_mem_cycles
  excessAt_source_neg := List.forall_mem_cons.2
    ⟨hs, fun p hp ↦ hneg _ (D.excessAt_source_neg p hp)⟩
  excessAt_target_pos := List.forall_mem_cons.2
    ⟨ht, fun p hp ↦ hpos' _ (D.excessAt_target_pos p hp)⟩
  sum_paths_add_sum_cycles := by
    rw [hfg, List.map_cons, List.sum_cons]
    conv_rhs => rw [← D.sum_paths_add_sum_cycles]
    abel

/-- **Path–cycle decomposition.** Every nonnegative arrow assignment `f` on a finite arrow family
is a sum of positively weighted directed paths, each from a vertex of negative excess to a vertex
of positive excess, and positively weighted directed cycles. The number of components is at most
the number of arrows on which `f` is positive, and if the values of `f` lie in an additive subgroup
`H`, then so do all weights. -/
theorem exists_pathCycleDecomposition (H : AddSubgroup K) (hf : 0 ≤ f)
    (hH : ∀ ⦃x y : V⦄ (e : Q x y), f e ∈ H) :
    ∃ D : PathCycleDecomposition f, (∀ p ∈ D.paths, p.weight ∈ H) ∧
      (∀ c ∈ D.cycles, c.weight ∈ H) ∧
      D.paths.length + D.cycles.length ≤ #{a : Σ x y, Q x y | 0 < f a.2.2} := by
  classical
  suffices ∀ n (f : Assignment Q K), 0 ≤ f → (∀ ⦃x y : V⦄ (e : Q x y), f e ∈ H) →
      #{a : Σ x y, Q x y | 0 < f a.2.2} = n →
      ∃ D : PathCycleDecomposition f, (∀ p ∈ D.paths, p.weight ∈ H) ∧
        (∀ c ∈ D.cycles, c.weight ∈ H) ∧
        D.paths.length + D.cycles.length ≤ #{a : Σ x y, Q x y | 0 < f a.2.2} from
    this _ f hf hH rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hH hn
  subst hn
  -- Peeling off a walk of positive arrows weighted by its bottleneck leaves a nonnegative
  -- assignment with values in `H` and fewer positive arrows, which is decomposed by induction.
  have peel {s t : V} (p : ArrowWalk Q s t) (hnd : p.arrows.Nodup) (hne : p.arrows ≠ [])
      (hpos : ∀ a ∈ p.arrows, 0 < f a.2.2) :
      ∃ q : K, 0 < q ∧ q ∈ H ∧ 0 ≤ f - walkAssignment p q ∧
        ∃ D : PathCycleDecomposition (f - walkAssignment p q),
          (∀ p ∈ D.paths, p.weight ∈ H) ∧ (∀ c ∈ D.cycles, c.weight ∈ H) ∧
          D.paths.length + D.cycles.length + 1 ≤ #{a : Σ x y, Q x y | 0 < f a.2.2} := by
    obtain ⟨hq, hqH, hg, hgH, hcard⟩ :=
      sub_walkAssignment_bottleneck_spec H hf hH hnd hne hpos
    obtain ⟨D, hP, hC, hlen⟩ := ih _ hcard _ hg hgH rfl
    exact ⟨_, hq, hqH, hg, D, hP, hC, by omega⟩
  by_cases hz : ∀ ⦃x y : V⦄ (e : Q x y), f e ≤ 0
  · -- The zero assignment has the empty decomposition.
    have hf0 : f = 0 :=
      funext fun x ↦ funext fun y ↦ funext fun e ↦ le_antisymm (hz e) (hf x y e)
    subst hf0
    exact ⟨⟨[], [], by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      by simp, by simp, by simp⟩
  simp only [not_forall, not_le] at hz
  obtain ⟨x, y, e, he⟩ := hz
  by_cases hcyc : ∃ v, TransGen (fun v w ↦ ∃ e : Q v w, 0 < f e) v v
  · -- Some cycle consists of positive arrows: peel it off.
    obtain ⟨v, hv⟩ := hcyc
    obtain ⟨c, hc, hpos⟩ := exists_isCycle_iff_transGen.2 hv
    have hne : c.arrows ≠ [] := hc.arrows_ne_nil
    obtain ⟨q, hq, hqH, -, D, hP, hC, hlen⟩ := peel c hc.nodup_arrows hne hpos
    refine ⟨D.consCycle ⟨v, c, q⟩ hc hq (sub_add_cancel _ _).symm, hP,
      List.forall_mem_cons.2 ⟨hqH, hC⟩, ?_⟩
    simp only [PathCycleDecomposition.consCycle, List.length_cons]
    omega
  · -- The positive arrows contain no cycle: peel off a path from a vertex no positive arrow
    -- enters to a vertex no positive arrow leaves.
    simp only [not_exists] at hcyc
    have hfacyc : f.IsAcyclic := (Assignment.isAcyclic_iff_forall_not_transGen f).2 hcyc
    obtain ⟨s, t, p, hp, hst, hpos, hin, hout⟩ := exists_isPath_of_isAcyclic hf hfacyc e he
    have hne : p.arrows ≠ [] := p.arrows_ne_nil hst
    obtain ⟨q, hq, hqH, hg, D, hP, hC, hlen⟩ := peel p hp.nodup_arrows hne hpos
    obtain ⟨hs, ht, hneg, hpos'⟩ := excessAt_sign_of_sub_walkAssignment hst hq hg hin hout
    refine ⟨D.consPath ⟨s, t, p, q⟩ hp hq hs ht hneg hpos' (sub_add_cancel _ _).symm,
      List.forall_mem_cons.2 ⟨hqH, hP⟩, hC, ?_⟩
    simp only [PathCycleDecomposition.consPath, List.length_cons]
    omega

/-- Every nonnegative arrow assignment on a finite arrow family has a path–cycle
decomposition. -/
theorem nonempty_pathCycleDecomposition (hf : 0 ≤ f) : Nonempty (PathCycleDecomposition f) :=
  let ⟨D, _⟩ := exists_pathCycleDecomposition ⊤ hf fun _ _ _ ↦ AddSubgroup.mem_top _
  ⟨D⟩

end Existence

/-- An integer `s`–`t` flow between distinct vertices carrying at most one unit on every arrow
carries as many directed `s`–`t` paths as its value, no two of which traverse a common arrow:
every arrow of these paths carries one unit of the flow. -/
theorem Flow.exists_paths_card_eq_val {cap : Assignment Q ℤ} {s t : V} (hst : s ≠ t)
    (f : Flow cap s t) (hf : ∀ ⦃x y : V⦄ (e : Q x y), f.toFun e ≤ 1) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk Q s t), (k : ℤ) = f.val ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ a ∈ (P i).arrows, f.toFun a.2.2 = 1) ∧
      Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  obtain ⟨D⟩ := nonempty_pathCycleDecomposition (f := f.toFun) fun _ _ e ↦ f.nonneg e
  -- Every path of the decomposition runs from `s` to `t`.
  have hwalk (p : WeightedWalk Q ℤ) (hp : p ∈ D.paths) :
      ∃ q : ArrowWalk Q s t, q.IsPath ∧ q.arrows = p.walk.arrows := by
    obtain ⟨x, y, w, q⟩ := p
    obtain rfl : x = s := D.source_eq_of_mem_paths hp
    obtain rfl : y = t := D.target_eq_of_mem_paths hp
    exact ⟨w, D.isPath_walk _ hp, rfl⟩
  -- A path of the decomposition places its weight on each of its arrows.
  have happly {p : WeightedWalk Q ℤ} (hp : p ∈ D.paths) {x y : V} {e : Q x y}
      (he : ⟨x, y, e⟩ ∈ p.walk.arrows) : p.assignment e = p.weight := by
    rw [WeightedWalk.assignment_def]
    exact walkAssignment_eq_of_mem (D.isPath_walk p hp).nodup_arrows _ he
  -- Every path of the decomposition has weight one, since its arrows carry at most one unit.
  have hweight (p : WeightedWalk Q ℤ) (hp : p ∈ D.paths) : p.weight = 1 := by
    obtain ⟨q, -, hq⟩ := hwalk p hp
    obtain ⟨⟨x, y, e⟩, he⟩ := List.exists_mem_of_ne_nil _ (q.arrows_ne_nil hst)
    rw [hq] at he
    have hle : p.assignment e ≤ 1 := (D.assignment_le_of_mem_paths hp x y e).trans (hf e)
    rw [happly hp he] at hle
    have := D.weight_pos_of_mem_paths p hp
    omega
  choose P hP hPa using fun i : Fin D.paths.length ↦
    hwalk D.paths[(i : ℕ)] (List.getElem_mem _)
  refine ⟨D.paths.length, P, ?_, hP, fun i ⟨x, y, e⟩ ha ↦ ?_, fun i j hij a hai haj ↦ ?_⟩
  · rw [← D.sum_weight_paths_eq_val, List.map_congr_left hweight, List.map_const',
      List.sum_replicate, nsmul_one]
  · -- Each path places one unit on each of its arrows, and no arrow carries more.
    rw [hPa] at ha
    have hle : D.paths[(i : ℕ)].assignment e ≤ f.toFun e :=
      D.assignment_le_of_mem_paths (List.getElem_mem _) x y e
    rw [happly (List.getElem_mem _) ha, hweight _ (List.getElem_mem _)] at hle
    exact le_antisymm (hf e) hle
  · -- An arrow on two different paths would carry at least two units.
    obtain ⟨x, y, e⟩ := a
    rw [hPa] at hai haj
    have hsum :
        D.pathAssignment e = ∑ k : Fin D.paths.length, D.paths[(k : ℕ)].assignment e := by
      rw [Fin.sum_univ_fun_getElem D.paths fun p ↦ p.assignment e,
        PathCycleDecomposition.pathAssignment_def]
      simp only [Pi.list_sum_apply, List.map_map, Function.comp_def]
    have hpair : D.paths[(i : ℕ)].assignment e + D.paths[(j : ℕ)].assignment e ≤
        D.pathAssignment e := by
      rw [hsum, ← sum_pair (f := fun k : Fin D.paths.length ↦ D.paths[(k : ℕ)].assignment e)
        hij]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ ↦
        D.assignment_nonneg_of_mem_paths (List.getElem_mem _) x y e
    rw [happly (List.getElem_mem _) hai, happly (List.getElem_mem _) haj,
      hweight _ (List.getElem_mem _), hweight _ (List.getElem_mem _)] at hpair
    have : D.pathAssignment e ≤ 1 := (D.pathAssignment_le x y e).trans (hf e)
    omega

end TauCeti
