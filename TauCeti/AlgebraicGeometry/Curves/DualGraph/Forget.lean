/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Contraction

/-!
# Forgetting a marking of a stable dual graph

Forgetting the marking `none` of a dual graph with markings indexed by `Option ι` is reindexing
its markings along `some : ι → Option ι`, `TauCeti.DualGraph.reindex`.

Forgetting one marking of a stable `(n + 1)`-pointed curve of genus `g` is the input of Knudsen's
single-marking contraction. Write `B = ω(s₁ + ⋯ + sₙ)` for the log-canonical sheaf of the curve
with the remaining markings. Its degree on a component is the log-canonical degree of the
corresponding vertex after forgetting, which drops by one on the component carrying the
forgotten marking and is unchanged elsewhere. This file proves the dual-graph form of the
fibrewise facts behind the contraction:

* `B` is nef: the graph with the marking forgotten is semistable;
* at most one component has degree zero, and it carries the forgotten marking;
* in the stable range `2g - 2 + n > 0` that component is a rational tail with exactly one
  remaining marking or a rational bridge with no remaining marking, by
  `TauCeti.DualGraph.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_eq_zero`, so it is
  contracted by a single stabilization step;
* that step yields a stable graph, and when it contracts a tail the log-canonical degrees of the
  remaining vertices are those of `B`, by
  `TauCeti.DualGraph.IsSemistable.logCanonicalDegree_contractTail`. This is the numerical
  dual-graph analogue of `B` being the pullback of the log-canonical sheaf of the contracted
  curve; it does not prove the sheaf-level formula.

In particular, after forgetting one marking of a stable graph in the stable range, stabilization
takes at most one step.

## Main results

* `TauCeti.DualGraph.logCanonicalDegree_reindex_some`: forgetting the marking `none` lowers the
  log-canonical degree of the vertex carrying it by one.
* `TauCeti.DualGraph.IsStable.isSemistable_reindex_some`: forgetting a marking of a stable graph
  leaves a semistable graph.
* `TauCeti.DualGraph.IsStable.subsingleton_logCanonicalDegree_reindex_some_eq_zero`: at most one
  vertex then has log-canonical degree zero.
* `TauCeti.DualGraph.IsStable.isStable_of_stabilizationStep_reindex_some`: a stabilization step
  then yields a stable graph.
* `TauCeti.DualGraph.IsStable.exists_reflGen_stabilizationStep_reindex_some_isStable`: in the
  stable range, at most one stabilization step makes the graph stable again.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §1, for the contraction forgetting one marking.
* [Stacks, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N), contracting rational tails and
  rational bridges.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset

universe u v

variable {ι : Type v}

/-! ### Forgetting one marking -/

section Forget

variable [Fintype ι] (G : DualGraph.{u} (Option ι))

/-- Forgetting the marking `none` removes it from the vertex carrying it. -/
theorem numMarkings_reindex_some (x : G.Vertex) :
    (G.reindex some).numMarkings x + (if G.marking none = x then 1 else 0) = G.numMarkings x := by
  simp only [numMarkings_def, card_filter, Fintype.sum_option]
  omega

/-- Forgetting the marking `none` lowers the log-canonical degree of the vertex carrying it by one
and leaves the other log-canonical degrees unchanged. -/
@[simp]
theorem logCanonicalDegree_reindex_some (x : G.Vertex) :
    (G.reindex some).logCanonicalDegree x =
      G.logCanonicalDegree x - if G.marking none = x then 1 else 0 := by
  have := G.numMarkings_reindex_some x
  rw [logCanonicalDegree_def, logCanonicalDegree_def, genus_reindex, valence_reindex]
  split_ifs at this ⊢ <;> omega

variable {G}

/-- **Forgetting a marking keeps the log-canonical sheaf nef.** Forgetting one marking of a stable
graph leaves a semistable graph. -/
theorem IsStable.isSemistable_reindex_some (hG : G.IsStable) : (G.reindex some).IsSemistable :=
  (isSemistable_iff _).mpr fun x ↦ by
    have := G.isStable_iff.mp hG x
    rw [logCanonicalDegree_reindex_some]
    split_ifs <;> omega

/-- After forgetting one marking of a stable graph, a vertex has log-canonical degree zero exactly
when it carries the forgotten marking and had log-canonical degree one. -/
theorem IsStable.logCanonicalDegree_reindex_some_eq_zero_iff (hG : G.IsStable) {x : G.Vertex} :
    (G.reindex some).logCanonicalDegree x = 0 ↔
      G.marking none = x ∧ G.logCanonicalDegree x = 1 := by
  have := G.isStable_iff.mp hG x
  rw [logCanonicalDegree_reindex_some]
  split_ifs with h <;> simp [h] <;> omega

/-- After forgetting one marking of a stable graph, at most one vertex has log-canonical degree
zero: the one carrying the forgotten marking. -/
theorem IsStable.subsingleton_logCanonicalDegree_reindex_some_eq_zero (hG : G.IsStable) :
    {x : G.Vertex | (G.reindex some).logCanonicalDegree x = 0}.Subsingleton :=
  fun _ hx _ hy ↦ ((hG.logCanonicalDegree_reindex_some_eq_zero_iff.mp hx).1.symm.trans
    (hG.logCanonicalDegree_reindex_some_eq_zero_iff.mp hy).1)

/-- After forgetting one marking of a stable graph, every vertex other than one of nonpositive
log-canonical degree has positive log-canonical degree. -/
theorem IsStable.logCanonicalDegree_reindex_some_pos_of_ne (hG : G.IsStable) {x y : G.Vertex}
    (hx : (G.reindex some).logCanonicalDegree x ≤ 0) (hy : y ≠ x) :
    0 < (G.reindex some).logCanonicalDegree y := by
  have hx₀ := le_antisymm hx ((isSemistable_iff _).mp hG.isSemistable_reindex_some x)
  have hmx := (hG.logCanonicalDegree_reindex_some_eq_zero_iff.mp hx₀).1
  have := G.isStable_iff.mp hG y
  rw [logCanonicalDegree_reindex_some, ite_eq_right (hmx.trans_ne hy.symm)]
  omega

/-- A stabilization step after forgetting one marking of a stable graph yields a stable graph. -/
theorem IsStable.isStable_of_stabilizationStep_reindex_some (hG : G.IsStable)
    {H : DualGraph.{u} ι} (h : StabilizationStep (G.reindex some) H) : H.IsStable := by
  cases h with
  | contractTail hx hm =>
    have hdeg := hx.logCanonicalDegree_eq
    refine (isStable_iff _).mpr fun ⟨y, hy⟩ ↦ ?_
    rw [hG.isSemistable_reindex_some.logCanonicalDegree_contractTail hx hm y hy]
    exact hG.logCanonicalDegree_reindex_some_pos_of_ne (by omega) hy
  | @contractBridge x hx hm =>
    have hdeg := hx.logCanonicalDegree_eq
    have hm₀ : (G.reindex some).numMarkings x = 0 := by
      simpa [numMarkings_def, filter_eq_empty_iff] using hm
    refine (isStable_iff _).mpr fun ⟨y, hy⟩ ↦ ?_
    rw [logCanonicalDegree_contractBridge]
    exact hG.logCanonicalDegree_reindex_some_pos_of_ne (by omega) hy

/-- **Stabilization after forgetting a marking takes at most one step.** In the stable range
`2g - 2 + n > 0` for the remaining `n` markings, forgetting one marking of a stable graph gives a
graph which is either stable or becomes stable after a single stabilization step. -/
theorem IsStable.exists_reflGen_stabilizationStep_reindex_some_isStable (hG : G.IsStable)
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι) :
    ∃ H, Relation.ReflGen StabilizationStep (G.reindex some) H ∧ H.IsStable := by
  by_cases hs : (G.reindex some).IsStable
  · exact ⟨_, .refl, hs⟩
  · obtain ⟨H, hH⟩ := (G.reindex some).exists_stabilizationStep_of_not_isStable
      (by rwa [arithmeticGenus_reindex]) hs
    exact ⟨H, .single hH, hG.isStable_of_stabilizationStep_reindex_some hH⟩

end Forget

end DualGraph

end TauCeti
