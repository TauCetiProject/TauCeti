/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Contraction
import Mathlib.Data.Fintype.BigOperators

/-!
# Forgetting a marking of a stable dual graph

Reindexing the markings of a pointed nodal curve along a map `e : κ → ι` keeps the curve and
takes the `e i`-th marking as the new `i`-th marking; along an equivalence this reorders the
markings, and along `some : ι → Option ι` it forgets the marking `none`. The dual graph of the
reindexed curve is `TauCeti.DualGraph.reindex`.

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
  remaining vertices are those of `B`, so `B` is the pullback of the log-canonical sheaf of the
  contracted curve.

In particular, after forgetting one marking of a stable graph in the stable range, stabilization
takes at most one step.

## Main definitions

* `TauCeti.DualGraph.reindex`: the dual graph with markings reindexed along a map.

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

universe u v w

variable {ι : Type v} {κ : Type w}

/-! ### Reindexing the markings -/

section Reindex

variable (G : DualGraph.{u} ι)

/-- The dual graph with markings reindexed along `e : κ → ι`: the same curve, with the `e i`-th
marking of `G` as its `i`-th marking. Along an equivalence this reorders the markings, and along
`some : ι → Option ι` it forgets the marking `none`. -/
abbrev reindex (e : κ → ι) : DualGraph.{u} κ where
  Vertex := G.Vertex
  Edge := G.Edge
  endpoint := G.endpoint
  genus := G.genus
  marking i := G.marking (e i)
  connected := G.connected

variable (e : κ → ι)

@[simp]
lemma reindex_id : G.reindex id = G :=
  rfl

/-- Reindexing twice is reindexing along the composite. -/
@[simp]
lemma reindex_reindex {μ : Type*} (f : μ → κ) : (G.reindex e).reindex f = G.reindex (e ∘ f) :=
  rfl

@[simp]
lemma endpoint_reindex (x : G.Edge) (i : Fin 2) : (G.reindex e).endpoint x i = G.endpoint x i :=
  rfl

@[simp]
lemma genus_reindex (x : G.Vertex) : (G.reindex e).genus x = G.genus x :=
  rfl

@[simp]
lemma marking_reindex (i : κ) : (G.reindex e).marking i = G.marking (e i) :=
  rfl

/-- Reindexing the markings does not change the valences. -/
@[simp]
lemma valence_reindex (x : G.Vertex) : (G.reindex e).valence x = G.valence x := by
  rw [valence_def, valence_def]

/-- Reindexing the markings does not change the arithmetic genus. -/
@[simp]
lemma arithmeticGenus_reindex : (G.reindex e).arithmeticGenus = G.arithmeticGenus := by
  rw [arithmeticGenus_def, arithmeticGenus_def, firstBetti_def, firstBetti_def]

/-- Reindexing along an equivalence does not change the number of markings on a vertex. -/
@[simp]
theorem numMarkings_reindex_equiv [Fintype ι] [Fintype κ] (e : κ ≃ ι) (x : G.Vertex) :
    (G.reindex e).numMarkings x = G.numMarkings x := by
  simp only [numMarkings_def, card_filter]
  exact e.sum_comp fun i ↦ if G.marking i = x then 1 else 0

/-- Reindexing along an equivalence does not change the log-canonical degrees. -/
@[simp]
theorem logCanonicalDegree_reindex_equiv [Fintype ι] [Fintype κ] (e : κ ≃ ι) (x : G.Vertex) :
    (G.reindex e).logCanonicalDegree x = G.logCanonicalDegree x := by
  rw [logCanonicalDegree_def, logCanonicalDegree_def, numMarkings_reindex_equiv, genus_reindex,
    valence_reindex]

/-- Reindexing along an equivalence preserves stability. -/
@[simp]
theorem isStable_reindex_equiv_iff [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    (G.reindex e).IsStable ↔ G.IsStable := by
  simp only [isStable_iff, logCanonicalDegree_reindex_equiv]

/-- Reindexing along an equivalence preserves semistability. -/
@[simp]
theorem isSemistable_reindex_equiv_iff [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    (G.reindex e).IsSemistable ↔ G.IsSemistable := by
  simp only [isSemistable_iff, logCanonicalDegree_reindex_equiv]

end Reindex

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

/-- **Forgetting a marking and contracting the resulting tail.** If forgetting one marking of a
stable graph leaves a rational tail with at most one marking, contracting it does not change the
log-canonical degrees of the other vertices: the log-canonical sheaf of the curve with the marking
forgotten is the pullback of that of the contracted curve. -/
theorem IsStable.logCanonicalDegree_contractTail_reindex_some (hG : G.IsStable) {x : G.Vertex}
    (hx : (G.reindex some).IsRationalTail x) (hm : (G.reindex some).numMarkings x ≤ 1)
    (y : G.Vertex) (hy : y ≠ x) :
    ((G.reindex some).contractTail ((isRationalTail_iff _).mp hx).2).logCanonicalDegree ⟨y, hy⟩ =
      (G.reindex some).logCanonicalDegree y := by
  have hdeg := hx.logCanonicalDegree_eq
  have := (isSemistable_iff _).mp hG.isSemistable_reindex_some x
  rw [logCanonicalDegree_contractTail]
  split_ifs <;> omega

/-- A stabilization step after forgetting one marking of a stable graph yields a stable graph. -/
theorem IsStable.isStable_of_stabilizationStep_reindex_some (hG : G.IsStable)
    {H : DualGraph.{u} ι} (h : StabilizationStep (G.reindex some) H) : H.IsStable := by
  cases h with
  | contractTail hx hm =>
    have hdeg := hx.logCanonicalDegree_eq
    refine (isStable_iff _).mpr fun ⟨y, hy⟩ ↦ ?_
    rw [hG.logCanonicalDegree_contractTail_reindex_some hx hm y hy]
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
