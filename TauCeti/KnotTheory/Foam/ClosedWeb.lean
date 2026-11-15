/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sum
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Unlabelled closed webs

A closed web is a finite oriented trivalent graph whose components may also be vertex-free
circles. It is the boundary data of a foam: an unlabelled prefoam is a surface with seams whose
boundary is such a web, and labelled webs and foams decorate the records defined here.

The incidence data are recorded at the level of edge ends. Every oriented interval edge `e` has a
source end `srcEnd e` and a target end `tgtEnd e`, and these are always different ends, even when
both lie at the same vertex (an interval loop). Each end lies at a vertex, every vertex has exactly
three ends, and a permutation `rot` of the ends cycles through the three ends at each vertex,
recording their cyclic order. At every vertex at least one edge starts and at least one edge ends,
so each vertex is either a merge (two incoming edges) or a split (two outgoing edges). Vertex-free
circles carry no incidence data and are recorded as a finite type.

## Main definitions

* `TauCeti.ClosedWeb`: unlabelled closed webs.
* `TauCeti.ClosedWeb.inDegree`, `TauCeti.ClosedWeb.outDegree`, `TauCeti.ClosedWeb.IsMerge`,
  `TauCeti.ClosedWeb.IsSplit`: the orientation pattern at a vertex.
* `TauCeti.ClosedWeb.IsNilvalent`: webs without vertices, which consist only of circles.
* `TauCeti.ClosedWeb.circles`, the empty web `∅`, `TauCeti.ClosedWeb.disjointUnion`, the reversal
  `TauCeti.ClosedWeb.reverse` of interval orientations, and the mirror
  `TauCeti.ClosedWeb.mirror` reversing every cyclic order.
* `TauCeti.ClosedWeb.Iso`: isomorphisms of webs, with the unit, associativity and symmetry
  isomorphisms of the disjoint union.
* `TauCeti.ClosedWeb.theta`: the theta web, with one split and one merge vertex.

## Main results

* `TauCeti.ClosedWeb.minimalPeriod_rot`: the rotation is a three-cycle at every end; in
  particular the mirror changes the cyclic order at every end (`TauCeti.ClosedWeb.mirror_rot_ne`).
* `TauCeti.ClosedWeb.three_mul_card_vertex`: the handshake identity `3 |V| = 2 |E|`.
* `TauCeti.ClosedWeb.inDegree_add_outDegree` and `TauCeti.ClosedWeb.isSplit_iff_not_isMerge`.
* `TauCeti.ClosedWeb.Iso.ext`: an isomorphism is determined by its maps on edges and circles.
* `TauCeti.ClosedWeb.IsNilvalent.isoCircles`: a nilvalent web is its set of circles.

## References

* Goertz, Marino, Wedrich, *Monoidal 2-categories from foam evaluation*, arXiv:2602.11120,
  Definition 3.4. The records here separate the two ends of each interval edge and treat
  vertex-free circles as separate components.
* L.-H. Robert, E. Wagner, *A closed formula for the evaluation of sl(N)-foams*,
  arXiv:1702.04140, Section 2.
-/

public section

namespace TauCeti

open Equiv Function

universe u v w x

/-- An unlabelled closed web: finitely many trivalent vertices, oriented interval edges and
vertex-free circles. The two ends of every interval edge are recorded separately, each end lies at
a vertex, and `rot` cycles through the three ends at each vertex in their cyclic order. -/
structure ClosedWeb : Type (u + 1) where
  /-- The vertices. -/
  Vertex : Type u
  /-- The oriented interval edges. -/
  Edge : Type u
  /-- The ends of interval edges. -/
  End : Type u
  /-- The vertex-free circles. -/
  Circle : Type u
  /-- The end at which an edge starts. -/
  srcEnd : Edge → End
  /-- The end at which an edge finishes. -/
  tgtEnd : Edge → End
  /-- The vertex at which an end lies. -/
  vertex : End → Vertex
  /-- The cyclic order of the ends around each vertex. -/
  rot : Perm End
  /-- Every end is the source end or the target end of exactly one edge, and not both. -/
  sumElim_bijective : Bijective (Sum.elim srcEnd tgtEnd)
  /-- The ends at a vertex form exactly one cycle of the rotation. -/
  vertex_eq_vertex_iff {x y : End} : vertex x = vertex y ↔ rot.SameCycle x y
  /-- Every vertex has three ends. -/
  card_fiber_vertex (v : Vertex) : Nat.card {x // vertex x = v} = 3
  /-- At least one edge starts at every vertex. -/
  exists_vertex_srcEnd_eq (v : Vertex) : ∃ e, vertex (srcEnd e) = v
  /-- At least one edge finishes at every vertex. -/
  exists_vertex_tgtEnd_eq (v : Vertex) : ∃ e, vertex (tgtEnd e) = v
  /-- There are finitely many interval edges. -/
  finite_edge : Finite Edge
  /-- There are finitely many circles. -/
  finite_circle : Finite Circle

namespace ClosedWeb

attribute [instance] finite_edge finite_circle

variable (W : ClosedWeb.{u})

/-! ### Ends of edges -/

/-- The ends of a web are the source ends and the target ends of its edges. -/
noncomputable def endsEquiv : W.Edge ⊕ W.Edge ≃ W.End := Equiv.ofBijective _ W.sumElim_bijective

/-- The left copy of the edges gives the source ends. -/
@[simp] theorem endsEquiv_inl (e : W.Edge) : W.endsEquiv (.inl e) = W.srcEnd e := (rfl)

/-- The right copy of the edges gives the target ends. -/
@[simp] theorem endsEquiv_inr (e : W.Edge) : W.endsEquiv (.inr e) = W.tgtEnd e := (rfl)

/-- The source end of an edge comes from the left copy of the edges. -/
@[simp] theorem endsEquiv_symm_srcEnd (e : W.Edge) : W.endsEquiv.symm (W.srcEnd e) = .inl e :=
  W.endsEquiv.symm_apply_eq.2 (W.endsEquiv_inl e).symm

/-- The target end of an edge comes from the right copy of the edges. -/
@[simp] theorem endsEquiv_symm_tgtEnd (e : W.Edge) : W.endsEquiv.symm (W.tgtEnd e) = .inr e :=
  W.endsEquiv.symm_apply_eq.2 (W.endsEquiv_inr e).symm

/-- Distinct edges have distinct source ends. -/
theorem srcEnd_injective : Injective W.srcEnd := W.sumElim_bijective.1.comp Sum.inl_injective

/-- Distinct edges have distinct target ends. -/
theorem tgtEnd_injective : Injective W.tgtEnd := W.sumElim_bijective.1.comp Sum.inr_injective

/-- Two edges have the same source end exactly when they are equal. -/
@[simp] theorem srcEnd_inj {e e' : W.Edge} : W.srcEnd e = W.srcEnd e' ↔ e = e' :=
  W.srcEnd_injective.eq_iff

/-- Two edges have the same target end exactly when they are equal. -/
@[simp] theorem tgtEnd_inj {e e' : W.Edge} : W.tgtEnd e = W.tgtEnd e' ↔ e = e' :=
  W.tgtEnd_injective.eq_iff

/-- A source end is never a target end. In particular the two ends of an interval loop, which lie
at the same vertex, are different ends. -/
theorem srcEnd_ne_tgtEnd (e e' : W.Edge) : W.srcEnd e ≠ W.tgtEnd e' :=
  fun h ↦ Sum.inl_ne_inr (W.sumElim_bijective.1 (a₁ := .inl e) (a₂ := .inr e') h)

/-- Every end is a source end or a target end. -/
theorem exists_srcEnd_eq_or_exists_tgtEnd_eq (x : W.End) :
    (∃ e, W.srcEnd e = x) ∨ ∃ e, W.tgtEnd e = x := by
  obtain ⟨e | e, rfl⟩ := W.endsEquiv.surjective x
  exacts [.inl ⟨e, rfl⟩, .inr ⟨e, rfl⟩]

instance : Finite W.End := .of_equiv _ W.endsEquiv

/-- Every vertex is the vertex of one of its ends. -/
theorem vertex_surjective : Surjective W.vertex :=
  fun v ↦ let ⟨_, h⟩ := W.exists_vertex_srcEnd_eq v; ⟨_, h⟩

instance : Finite W.Vertex := .of_surjective _ W.vertex_surjective

/-- A web has twice as many edge ends as interval edges. -/
theorem card_end : Nat.card W.End = 2 * Nat.card W.Edge := by
  rw [← Nat.card_congr W.endsEquiv, Nat.card_sum, two_mul]

/-- A web has three times as many edge ends as vertices. -/
theorem card_end_eq_three_mul : Nat.card W.End = 3 * Nat.card W.Vertex := by
  have := Fintype.ofFinite W.Vertex
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv W.vertex), Nat.card_sigma]
  simp [W.card_fiber_vertex, Nat.card_eq_fintype_card, mul_comm]

/-- The handshake identity for trivalent webs: three times the number of vertices is twice the
number of interval edges. -/
theorem three_mul_card_vertex : 3 * Nat.card W.Vertex = 2 * Nat.card W.Edge := by
  rw [← card_end_eq_three_mul, card_end]

/-! ### The cyclic order at a vertex -/

/-- The rotation keeps every end at its vertex. -/
@[simp] theorem vertex_rot (x : W.End) : W.vertex (W.rot x) = W.vertex x :=
  W.vertex_eq_vertex_iff.2 (Perm.SameCycle.refl _ _ |>.apply_left)

/-- The inverse rotation keeps every end at its vertex. -/
@[simp] theorem vertex_rot_symm (x : W.End) : W.vertex (W.rot.symm x) = W.vertex x := by
  rw [← W.vertex_rot, Equiv.apply_symm_apply]

/-- The rotation is a three-cycle at every end: the cycle through an end consists of the three
ends at its vertex. -/
@[simp] theorem minimalPeriod_rot (x : W.End) : minimalPeriod W.rot x = 3 := by
  rw [← Perm.ncard_setOf_sameCycle, ← W.card_fiber_vertex (W.vertex x),
    ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y ↦
    ⟨fun h ↦ (W.vertex_eq_vertex_iff.2 h).symm, fun h ↦ W.vertex_eq_vertex_iff.1 h.symm⟩)

/-- Rotating three times around a vertex returns to the starting end. -/
@[simp] theorem rot_rot_rot (x : W.End) : W.rot (W.rot (W.rot x)) = x := by
  simpa [W.minimalPeriod_rot] using iterate_minimalPeriod (f := W.rot) (x := x)

/-- No end is fixed by the rotation. -/
theorem rot_ne_self (x : W.End) : W.rot x ≠ x :=
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod (n := 1) one_ne_zero
    (by rw [minimalPeriod_rot]; norm_num)

/-- Rotating twice around a vertex never returns to the starting end. -/
theorem rot_rot_ne_self (x : W.End) : W.rot (W.rot x) ≠ x :=
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod (n := 2) two_ne_zero
    (by rw [minimalPeriod_rot]; norm_num)

/-- The ends at the vertex of `x` are `x`, `rot x` and `rot (rot x)`. -/
theorem vertex_eq_vertex_iff_eq_or_eq_or_eq {x y : W.End} :
    W.vertex x = W.vertex y ↔ y = x ∨ y = W.rot x ∨ y = W.rot (W.rot x) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := (W.vertex_eq_vertex_iff.1 h).exists_nat_pow_eq
    have hp : IsPeriodicPt W.rot 3 x := W.minimalPeriod_rot x ▸ isPeriodicPt_minimalPeriod _ _
    rw [← Perm.iterate_eq_pow, ← hp.iterate_mod_apply]
    obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    all_goals simp [h]
  · rintro (rfl | rfl | rfl) <;> simp

/-! ### Merge and split vertices -/

/-- The number of edges finishing at a vertex. -/
noncomputable def inDegree (v : W.Vertex) : ℕ := Nat.card {e // W.vertex (W.tgtEnd e) = v}

/-- The number of edges starting at a vertex. -/
noncomputable def outDegree (v : W.Vertex) : ℕ := Nat.card {e // W.vertex (W.srcEnd e) = v}

/-- The in-degree counts the edges whose target end lies at the vertex. -/
theorem inDegree_def (v : W.Vertex) :
    W.inDegree v = Nat.card {e // W.vertex (W.tgtEnd e) = v} := (rfl)

/-- The out-degree counts the edges whose source end lies at the vertex. -/
theorem outDegree_def (v : W.Vertex) :
    W.outDegree v = Nat.card {e // W.vertex (W.srcEnd e) = v} := (rfl)

/-- The three ends at a vertex are its incoming and outgoing edge ends. An interval loop at `v`
counts once in each degree. -/
theorem inDegree_add_outDegree (v : W.Vertex) : W.inDegree v + W.outDegree v = 3 := by
  rw [← W.card_fiber_vertex v, add_comm, inDegree, outDegree, ← Nat.card_sum]
  exact Nat.card_congr <|
    (Equiv.subtypeSum (p := fun z ↦ W.vertex (W.endsEquiv z) = v)).symm.trans
      (W.endsEquiv.subtypeEquiv fun _ ↦ Iff.rfl)

/-- Some edge finishes at every vertex. -/
theorem inDegree_pos (v : W.Vertex) : 0 < W.inDegree v := by
  obtain ⟨e, he⟩ := W.exists_vertex_tgtEnd_eq v
  have : Nonempty {e // W.vertex (W.tgtEnd e) = v} := ⟨⟨e, he⟩⟩
  exact Nat.card_pos

/-- Some edge starts at every vertex. -/
theorem outDegree_pos (v : W.Vertex) : 0 < W.outDegree v := by
  obtain ⟨e, he⟩ := W.exists_vertex_srcEnd_eq v
  have : Nonempty {e // W.vertex (W.srcEnd e) = v} := ⟨⟨e, he⟩⟩
  exact Nat.card_pos

/-- A merge vertex: two edges finish there and one starts. -/
def IsMerge (v : W.Vertex) : Prop := W.inDegree v = 2

/-- A split vertex: one edge finishes there and two start. -/
def IsSplit (v : W.Vertex) : Prop := W.outDegree v = 2

/-- A merge vertex has in-degree two. -/
theorem isMerge_iff (v : W.Vertex) : W.IsMerge v ↔ W.inDegree v = 2 := Iff.rfl

/-- A split vertex has out-degree two. -/
theorem isSplit_iff (v : W.Vertex) : W.IsSplit v ↔ W.outDegree v = 2 := Iff.rfl

/-- A merge vertex is one at which exactly one edge starts. -/
theorem isMerge_iff_outDegree_eq_one (v : W.Vertex) : W.IsMerge v ↔ W.outDegree v = 1 := by
  have := W.inDegree_add_outDegree v
  rw [isMerge_iff]
  omega

/-- A split vertex is one at which exactly one edge finishes. -/
theorem isSplit_iff_inDegree_eq_one (v : W.Vertex) : W.IsSplit v ↔ W.inDegree v = 1 := by
  have := W.inDegree_add_outDegree v
  rw [isSplit_iff]
  omega

/-- Every vertex is a merge or a split. -/
theorem isMerge_or_isSplit (v : W.Vertex) : W.IsMerge v ∨ W.IsSplit v := by
  have := W.inDegree_add_outDegree v
  have := W.inDegree_pos v
  have := W.outDegree_pos v
  rw [isMerge_iff, isSplit_iff]
  omega

/-- A vertex is a split exactly when it is not a merge. -/
theorem isSplit_iff_not_isMerge (v : W.Vertex) : W.IsSplit v ↔ ¬W.IsMerge v := by
  have := W.inDegree_add_outDegree v
  have := W.inDegree_pos v
  have := W.outDegree_pos v
  rw [isMerge_iff, isSplit_iff]
  omega

/-- A vertex is a merge exactly when it is not a split. -/
theorem isMerge_iff_not_isSplit (v : W.Vertex) : W.IsMerge v ↔ ¬W.IsSplit v := by
  rw [isSplit_iff_not_isMerge, not_not]

/-- A vertex that is not a merge is a split. -/
@[simp] theorem not_isMerge (v : W.Vertex) : ¬W.IsMerge v ↔ W.IsSplit v :=
  (W.isSplit_iff_not_isMerge v).symm

/-- A vertex that is not a split is a merge. -/
@[simp] theorem not_isSplit (v : W.Vertex) : ¬W.IsSplit v ↔ W.IsMerge v :=
  (W.isMerge_iff_not_isSplit v).symm

/-! ### Nilvalent webs -/

/-- A web is nilvalent when it has no vertices; it then consists of vertex-free circles only. -/
def IsNilvalent : Prop := IsEmpty W.Vertex

/-- A nilvalent web is one with no vertices. -/
theorem isNilvalent_iff : W.IsNilvalent ↔ IsEmpty W.Vertex := Iff.rfl

/-- A web has no vertices exactly when it has no edge ends. -/
theorem isNilvalent_iff_isEmpty_end : W.IsNilvalent ↔ IsEmpty W.End :=
  ⟨fun h ↦ have := W.isNilvalent_iff.1 h; W.vertex.isEmpty,
    fun _ ↦ W.vertex_surjective.isEmpty⟩

/-- A web has no vertices exactly when it has no interval edges. -/
theorem isNilvalent_iff_isEmpty_edge : W.IsNilvalent ↔ IsEmpty W.Edge := by
  rw [isNilvalent_iff_isEmpty_end, ← W.endsEquiv.isEmpty_congr, isEmpty_sum, and_self]

/-! ### Circles, the empty web, reversal, mirror and disjoint union -/

/-- The nilvalent web whose components are the circles `C`. -/
@[expose]
def circles (C : Type u) [Finite C] : ClosedWeb.{u} where
  Vertex := PEmpty
  Edge := PEmpty
  End := PEmpty
  Circle := C
  srcEnd := PEmpty.elim
  tgtEnd := PEmpty.elim
  vertex := PEmpty.elim
  rot := Equiv.refl _
  sumElim_bijective := ⟨fun x ↦ x.elim (fun e ↦ e.elim) (fun e ↦ e.elim), fun x ↦ x.elim⟩
  vertex_eq_vertex_iff {x} := x.elim
  card_fiber_vertex v := v.elim
  exists_vertex_srcEnd_eq v := v.elim
  exists_vertex_tgtEnd_eq v := v.elim
  finite_edge := inferInstance
  finite_circle := inferInstance

/-- The empty web, with no vertices, edges or circles. -/
instance : EmptyCollection ClosedWeb.{u} := ⟨circles PEmpty⟩

/-- The empty web is the web of no circles. -/
theorem empty_eq_circles : (∅ : ClosedWeb.{u}) = circles PEmpty := (rfl)

/-- A web of circles is nilvalent. -/
@[simp] theorem isNilvalent_circles (C : Type u) [Finite C] : (circles C).IsNilvalent :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The empty web is nilvalent. -/
@[simp] theorem isNilvalent_empty : (∅ : ClosedWeb.{u}).IsNilvalent := isNilvalent_circles _

/-- The reversed web `Wʳ`: every interval edge is traversed in the opposite direction, so source
and target ends are exchanged; the cyclic orders are unchanged. -/
@[expose]
def reverse : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  End := W.End
  Circle := W.Circle
  srcEnd := W.tgtEnd
  tgtEnd := W.srcEnd
  vertex := W.vertex
  rot := W.rot
  sumElim_bijective := by
    have h : Sum.elim W.tgtEnd W.srcEnd = Sum.elim W.srcEnd W.tgtEnd ∘ Sum.swap := by
      ext (e | e) <;> rfl
    rw [h]
    exact W.sumElim_bijective.comp (Equiv.sumComm _ _).bijective
  vertex_eq_vertex_iff := W.vertex_eq_vertex_iff
  card_fiber_vertex := W.card_fiber_vertex
  exists_vertex_srcEnd_eq := W.exists_vertex_tgtEnd_eq
  exists_vertex_tgtEnd_eq := W.exists_vertex_srcEnd_eq
  finite_edge := W.finite_edge
  finite_circle := W.finite_circle

/-- The mirror web `Wᵐ`: the cyclic order at every vertex is reversed; orientations are
unchanged. -/
@[expose]
def mirror : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  End := W.End
  Circle := W.Circle
  srcEnd := W.srcEnd
  tgtEnd := W.tgtEnd
  vertex := W.vertex
  rot := W.rot⁻¹
  sumElim_bijective := W.sumElim_bijective
  vertex_eq_vertex_iff := W.vertex_eq_vertex_iff.trans Perm.sameCycle_inv.symm
  card_fiber_vertex := W.card_fiber_vertex
  exists_vertex_srcEnd_eq := W.exists_vertex_srcEnd_eq
  exists_vertex_tgtEnd_eq := W.exists_vertex_tgtEnd_eq
  finite_edge := W.finite_edge
  finite_circle := W.finite_circle

/-- The source ends of the reversed web are the target ends. -/
@[simp] theorem reverse_srcEnd : W.reverse.srcEnd = W.tgtEnd := (rfl)

/-- The target ends of the reversed web are the source ends. -/
@[simp] theorem reverse_tgtEnd : W.reverse.tgtEnd = W.srcEnd := (rfl)

/-- Reversal keeps the vertex of every end. -/
@[simp] theorem reverse_vertex : W.reverse.vertex = W.vertex := (rfl)

/-- Reversal keeps the cyclic orders. -/
@[simp] theorem reverse_rot : W.reverse.rot = W.rot := (rfl)

/-- Mirroring keeps the source ends. -/
@[simp] theorem mirror_srcEnd : W.mirror.srcEnd = W.srcEnd := (rfl)

/-- Mirroring keeps the target ends. -/
@[simp] theorem mirror_tgtEnd : W.mirror.tgtEnd = W.tgtEnd := (rfl)

/-- Mirroring keeps the vertex of every end. -/
@[simp] theorem mirror_vertex : W.mirror.vertex = W.vertex := (rfl)

/-- Mirroring inverts the rotation. -/
@[simp] theorem mirror_rot : W.mirror.rot = W.rot⁻¹ := (rfl)

/-- Reversal is an involution. -/
@[simp] theorem reverse_reverse : W.reverse.reverse = W := (rfl)

/-- Mirroring is an involution. -/
@[simp] theorem mirror_mirror : W.mirror.mirror = W := (rfl)

/-- Reversal and mirroring commute. -/
theorem mirror_reverse : W.reverse.mirror = W.mirror.reverse := (rfl)

/-- Reversal exchanges incoming and outgoing edges. -/
@[simp] theorem inDegree_reverse (v : W.Vertex) : W.reverse.inDegree v = W.outDegree v := (rfl)

/-- Reversal exchanges incoming and outgoing edges. -/
@[simp] theorem outDegree_reverse (v : W.Vertex) : W.reverse.outDegree v = W.inDegree v := (rfl)

/-- Reversal turns merges into splits. -/
@[simp] theorem isMerge_reverse (v : W.Vertex) : W.reverse.IsMerge v ↔ W.IsSplit v := Iff.rfl

/-- Reversal turns splits into merges. -/
@[simp] theorem isSplit_reverse (v : W.Vertex) : W.reverse.IsSplit v ↔ W.IsMerge v := Iff.rfl

/-- Mirroring keeps in-degrees. -/
@[simp] theorem inDegree_mirror (v : W.Vertex) : W.mirror.inDegree v = W.inDegree v := (rfl)

/-- Mirroring keeps out-degrees. -/
@[simp] theorem outDegree_mirror (v : W.Vertex) : W.mirror.outDegree v = W.outDegree v := (rfl)

/-- Mirroring keeps merge vertices. -/
@[simp] theorem isMerge_mirror (v : W.Vertex) : W.mirror.IsMerge v ↔ W.IsMerge v := Iff.rfl

/-- Mirroring keeps split vertices. -/
@[simp] theorem isSplit_mirror (v : W.Vertex) : W.mirror.IsSplit v ↔ W.IsSplit v := Iff.rfl

/-- Reversal keeps nilvalence. -/
@[simp] theorem isNilvalent_reverse : W.reverse.IsNilvalent ↔ W.IsNilvalent := Iff.rfl

/-- Mirroring keeps nilvalence. -/
@[simp] theorem isNilvalent_mirror : W.mirror.IsNilvalent ↔ W.IsNilvalent := Iff.rfl

/-- A web of circles is its own reversal. -/
@[simp] theorem reverse_circles (C : Type u) [Finite C] : (circles C).reverse = circles C := (rfl)

/-- A web of circles is its own mirror. -/
@[simp] theorem mirror_circles (C : Type u) [Finite C] : (circles C).mirror = circles C := (rfl)

/-- The empty web is its own reversal. -/
@[simp] theorem reverse_empty : (∅ : ClosedWeb.{u}).reverse = ∅ := (rfl)

/-- The empty web is its own mirror. -/
@[simp] theorem mirror_empty : (∅ : ClosedWeb.{u}).mirror = ∅ := (rfl)

/-- The mirror changes the cyclic order at every end: on the three ends `a, b, c = rot b` at a
vertex, the rotation sends `a` to `b` while the mirrored rotation sends `a` to `c`. -/
theorem mirror_rot_ne (x : W.End) : W.mirror.rot x ≠ W.rot x :=
  fun h ↦ W.rot_rot_ne_self x (Perm.inv_eq_iff_eq.1 (W.mirror_rot ▸ h)).symm

/-- The disjoint union of two webs. -/
@[expose]
def disjointUnion (W₁ W₂ : ClosedWeb.{u}) : ClosedWeb.{u} where
  Vertex := W₁.Vertex ⊕ W₂.Vertex
  Edge := W₁.Edge ⊕ W₂.Edge
  End := W₁.End ⊕ W₂.End
  Circle := W₁.Circle ⊕ W₂.Circle
  srcEnd := Sum.map W₁.srcEnd W₂.srcEnd
  tgtEnd := Sum.map W₁.tgtEnd W₂.tgtEnd
  vertex := Sum.map W₁.vertex W₂.vertex
  rot := Perm.sumCongr W₁.rot W₂.rot
  sumElim_bijective := by
    have h : Sum.elim (Sum.map W₁.srcEnd W₂.srcEnd) (Sum.map W₁.tgtEnd W₂.tgtEnd) =
        Sum.map (Sum.elim W₁.srcEnd W₁.tgtEnd) (Sum.elim W₂.srcEnd W₂.tgtEnd) ∘
          Equiv.sumSumSumComm _ _ _ _ := by
      ext ((e | e) | (e | e)) <;> rfl
    rw [h]
    exact (W₁.sumElim_bijective.sumMap W₂.sumElim_bijective).comp (Equiv.bijective _)
  vertex_eq_vertex_iff {x y} := by
    rcases x with x | x <;> rcases y with y | y
    · simpa using W₁.vertex_eq_vertex_iff
    · exact iff_of_false (by simp) (Perm.not_sameCycle_sumCongr_inl_inr _ _ _ _)
    · exact iff_of_false (by simp) fun h ↦ Perm.not_sameCycle_sumCongr_inl_inr _ _ _ _ h.symm
    · simpa using W₂.vertex_eq_vertex_iff
  card_fiber_vertex v := by
    rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
    rcases v with v | v <;> simp [W₁.card_fiber_vertex, W₂.card_fiber_vertex]
  exists_vertex_srcEnd_eq
    | .inl v => (W₁.exists_vertex_srcEnd_eq v).imp' Sum.inl fun _ h ↦ congrArg Sum.inl h
    | .inr v => (W₂.exists_vertex_srcEnd_eq v).imp' Sum.inr fun _ h ↦ congrArg Sum.inr h
  exists_vertex_tgtEnd_eq
    | .inl v => (W₁.exists_vertex_tgtEnd_eq v).imp' Sum.inl fun _ h ↦ congrArg Sum.inl h
    | .inr v => (W₂.exists_vertex_tgtEnd_eq v).imp' Sum.inr fun _ h ↦ congrArg Sum.inr h
  finite_edge := inferInstanceAs (Finite (W₁.Edge ⊕ W₂.Edge))
  finite_circle := inferInstanceAs (Finite (W₁.Circle ⊕ W₂.Circle))

section disjointUnion

variable (W₁ W₂ : ClosedWeb.{u})

/-- The source ends of a disjoint union are those of its pieces. -/
@[simp] theorem disjointUnion_srcEnd :
    (W₁.disjointUnion W₂).srcEnd = Sum.map W₁.srcEnd W₂.srcEnd := (rfl)

/-- The target ends of a disjoint union are those of its pieces. -/
@[simp] theorem disjointUnion_tgtEnd :
    (W₁.disjointUnion W₂).tgtEnd = Sum.map W₁.tgtEnd W₂.tgtEnd := (rfl)

/-- Each end of a disjoint union lies at its vertex in its own piece. -/
@[simp] theorem disjointUnion_vertex :
    (W₁.disjointUnion W₂).vertex = Sum.map W₁.vertex W₂.vertex := (rfl)

/-- The rotation of a disjoint union rotates each piece separately. -/
@[simp] theorem disjointUnion_rot : (W₁.disjointUnion W₂).rot = Perm.sumCongr W₁.rot W₂.rot := (rfl)

/-- Reversal distributes over disjoint union. -/
theorem reverse_disjointUnion :
    (W₁.disjointUnion W₂).reverse = W₁.reverse.disjointUnion W₂.reverse := (rfl)

/-- Mirroring distributes over disjoint union. -/
theorem mirror_disjointUnion :
    (W₁.disjointUnion W₂).mirror = W₁.mirror.disjointUnion W₂.mirror := (rfl)

/-- A disjoint union is nilvalent exactly when both pieces are. -/
@[simp] theorem isNilvalent_disjointUnion :
    (W₁.disjointUnion W₂).IsNilvalent ↔ W₁.IsNilvalent ∧ W₂.IsNilvalent := isEmpty_sum

/-- The in-degree of a vertex of the first piece of a disjoint union is its in-degree there. -/
@[simp] theorem inDegree_disjointUnion_inl (v : W₁.Vertex) :
    (W₁.disjointUnion W₂).inDegree (.inl v) = W₁.inDegree v := by
  simp [inDegree, disjointUnion, Nat.card_congr Equiv.subtypeSum]

/-- The in-degree of a vertex of the second piece of a disjoint union is its in-degree there. -/
@[simp] theorem inDegree_disjointUnion_inr (v : W₂.Vertex) :
    (W₁.disjointUnion W₂).inDegree (.inr v) = W₂.inDegree v := by
  simp [inDegree, disjointUnion, Nat.card_congr Equiv.subtypeSum]

/-- The out-degree of a vertex of the first piece of a disjoint union is its out-degree there. -/
@[simp] theorem outDegree_disjointUnion_inl (v : W₁.Vertex) :
    (W₁.disjointUnion W₂).outDegree (.inl v) = W₁.outDegree v := by
  simp [outDegree, disjointUnion, Nat.card_congr Equiv.subtypeSum]

/-- The out-degree of a vertex of the second piece of a disjoint union is its out-degree there. -/
@[simp] theorem outDegree_disjointUnion_inr (v : W₂.Vertex) :
    (W₁.disjointUnion W₂).outDegree (.inr v) = W₂.outDegree v := by
  simp [outDegree, disjointUnion, Nat.card_congr Equiv.subtypeSum]

/-- A vertex of the first piece is a merge in the disjoint union exactly when it is one there. -/
@[simp] theorem isMerge_disjointUnion_inl (v : W₁.Vertex) :
    (W₁.disjointUnion W₂).IsMerge (.inl v) ↔ W₁.IsMerge v :=
  iff_of_eq (congrArg (· = 2) (inDegree_disjointUnion_inl W₁ W₂ v))

/-- A vertex of the second piece is a merge in the disjoint union exactly when it is one there. -/
@[simp] theorem isMerge_disjointUnion_inr (v : W₂.Vertex) :
    (W₁.disjointUnion W₂).IsMerge (.inr v) ↔ W₂.IsMerge v :=
  iff_of_eq (congrArg (· = 2) (inDegree_disjointUnion_inr W₁ W₂ v))

/-- A vertex of the first piece is a split in the disjoint union exactly when it is one there. -/
@[simp] theorem isSplit_disjointUnion_inl (v : W₁.Vertex) :
    (W₁.disjointUnion W₂).IsSplit (.inl v) ↔ W₁.IsSplit v :=
  iff_of_eq (congrArg (· = 2) (outDegree_disjointUnion_inl W₁ W₂ v))

/-- A vertex of the second piece is a split in the disjoint union exactly when it is one there. -/
@[simp] theorem isSplit_disjointUnion_inr (v : W₂.Vertex) :
    (W₁.disjointUnion W₂).IsSplit (.inr v) ↔ W₂.IsSplit v :=
  iff_of_eq (congrArg (· = 2) (outDegree_disjointUnion_inr W₁ W₂ v))

end disjointUnion

/-! ### Isomorphisms -/

/-- An isomorphism of closed webs: bijections of vertices, interval edges, edge ends and circles
that preserve the source and target ends of every edge, the vertex of every end and the cyclic
orders. -/
structure Iso (W₁ : ClosedWeb.{u}) (W₂ : ClosedWeb.{v}) where
  /-- The bijection of vertices. -/
  vertexEquiv : W₁.Vertex ≃ W₂.Vertex
  /-- The bijection of interval edges. -/
  edgeEquiv : W₁.Edge ≃ W₂.Edge
  /-- The bijection of edge ends. -/
  endEquiv : W₁.End ≃ W₂.End
  /-- The bijection of circles. -/
  circleEquiv : W₁.Circle ≃ W₂.Circle
  /-- Source ends are preserved. -/
  map_srcEnd (e : W₁.Edge) : W₂.srcEnd (edgeEquiv e) = endEquiv (W₁.srcEnd e)
  /-- Target ends are preserved. -/
  map_tgtEnd (e : W₁.Edge) : W₂.tgtEnd (edgeEquiv e) = endEquiv (W₁.tgtEnd e)
  /-- The vertex of every end is preserved. -/
  map_vertex (x : W₁.End) : W₂.vertex (endEquiv x) = vertexEquiv (W₁.vertex x)
  /-- The cyclic orders are preserved. -/
  map_rot (x : W₁.End) : W₂.rot (endEquiv x) = endEquiv (W₁.rot x)

attribute [simp] Iso.map_srcEnd Iso.map_tgtEnd Iso.map_vertex Iso.map_rot

namespace Iso

variable {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}} {W₃ : ClosedWeb.{w}} {W₄ : ClosedWeb.{x}}

/-- The identity isomorphism. -/
@[expose, refl, simps]
def refl (W : ClosedWeb.{u}) : W.Iso W where
  vertexEquiv := .refl _
  edgeEquiv := .refl _
  endEquiv := .refl _
  circleEquiv := .refl _
  map_srcEnd _ := rfl
  map_tgtEnd _ := rfl
  map_vertex _ := rfl
  map_rot _ := rfl

/-- The inverse of an isomorphism. -/
@[expose, symm, simps]
def symm (f : W₁.Iso W₂) : W₂.Iso W₁ where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  endEquiv := f.endEquiv.symm
  circleEquiv := f.circleEquiv.symm
  map_srcEnd e := (Equiv.eq_symm_apply _).2 <| by rw [← f.map_srcEnd, Equiv.apply_symm_apply]
  map_tgtEnd e := (Equiv.eq_symm_apply _).2 <| by rw [← f.map_tgtEnd, Equiv.apply_symm_apply]
  map_vertex x := (Equiv.eq_symm_apply _).2 <| by rw [← f.map_vertex, Equiv.apply_symm_apply]
  map_rot x := (Equiv.eq_symm_apply _).2 <| by rw [← f.map_rot, Equiv.apply_symm_apply]

/-- The composite of two isomorphisms. -/
@[expose, trans, simps]
def trans (f : W₁.Iso W₂) (g : W₂.Iso W₃) : W₁.Iso W₃ where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  endEquiv := f.endEquiv.trans g.endEquiv
  circleEquiv := f.circleEquiv.trans g.circleEquiv
  map_srcEnd _ := by simp
  map_tgtEnd _ := by simp
  map_vertex _ := by simp
  map_rot _ := by simp

/-- An isomorphism is determined by its bijections of interval edges and of circles: every end is
the source or target end of an edge, and every vertex is the vertex of an end. -/
@[ext]
theorem ext {f g : W₁.Iso W₂} (hedge : f.edgeEquiv = g.edgeEquiv)
    (hcircle : f.circleEquiv = g.circleEquiv) : f = g := by
  have hend : f.endEquiv = g.endEquiv := by
    ext x
    obtain ⟨e, rfl⟩ | ⟨e, rfl⟩ := W₁.exists_srcEnd_eq_or_exists_tgtEnd_eq x
    · rw [← f.map_srcEnd, ← g.map_srcEnd, hedge]
    · rw [← f.map_tgtEnd, ← g.map_tgtEnd, hedge]
  have hvertex : f.vertexEquiv = g.vertexEquiv := by
    ext v
    obtain ⟨x, rfl⟩ := W₁.vertex_surjective v
    rw [← f.map_vertex, ← g.map_vertex, hend]
  cases f
  cases g
  simp_all

/-- Inverting an isomorphism twice gives it back. -/
@[simp] theorem symm_symm (f : W₁.Iso W₂) : f.symm.symm = f := (rfl)

/-- The identity is a left unit for composition. -/
@[simp] theorem refl_trans (f : W₁.Iso W₂) : (refl W₁).trans f = f := (rfl)

/-- The identity is a right unit for composition. -/
@[simp] theorem trans_refl (f : W₁.Iso W₂) : f.trans (refl W₂) = f := (rfl)

/-- An isomorphism composed after its inverse is the identity. -/
@[simp] theorem symm_trans_self (f : W₁.Iso W₂) : f.symm.trans f = refl W₂ := by ext <;> simp

/-- An isomorphism composed with its inverse is the identity. -/
@[simp] theorem self_trans_symm (f : W₁.Iso W₂) : f.trans f.symm = refl W₁ := by ext <;> simp

/-- Composition of isomorphisms is associative. -/
theorem trans_assoc (f : W₁.Iso W₂) (g : W₂.Iso W₃) (h : W₃.Iso W₄) :
    (f.trans g).trans h = f.trans (g.trans h) := (rfl)

/-- The inverse of the identity is the identity. -/
@[simp] theorem refl_symm (W : ClosedWeb.{u}) : (refl W).symm = refl W := (rfl)

/-- The inverse of a composite is the composite of the inverses in the opposite order. -/
@[simp] theorem symm_trans (f : W₁.Iso W₂) (g : W₂.Iso W₃) :
    (f.trans g).symm = g.symm.trans f.symm := (rfl)

/-- An isomorphism preserves the inverse rotations. -/
@[simp] theorem map_rot_symm (f : W₁.Iso W₂) (x : W₁.End) :
    W₂.rot.symm (f.endEquiv x) = f.endEquiv (W₁.rot.symm x) := by
  rw [Equiv.symm_apply_eq, map_rot, Equiv.apply_symm_apply]

/-- The inverse of an isomorphism preserves source ends. -/
@[simp] theorem srcEnd_edgeEquiv_symm (f : W₁.Iso W₂) (e : W₂.Edge) :
    W₁.srcEnd (f.edgeEquiv.symm e) = f.endEquiv.symm (W₂.srcEnd e) := f.symm.map_srcEnd e

/-- The inverse of an isomorphism preserves target ends. -/
@[simp] theorem tgtEnd_edgeEquiv_symm (f : W₁.Iso W₂) (e : W₂.Edge) :
    W₁.tgtEnd (f.edgeEquiv.symm e) = f.endEquiv.symm (W₂.tgtEnd e) := f.symm.map_tgtEnd e

/-- The inverse of an isomorphism preserves the vertex of every end. -/
@[simp] theorem vertex_endEquiv_symm (f : W₁.Iso W₂) (x : W₂.End) :
    W₁.vertex (f.endEquiv.symm x) = f.vertexEquiv.symm (W₂.vertex x) := f.symm.map_vertex x

/-- The inverse of an isomorphism preserves the rotations. -/
@[simp] theorem rot_endEquiv_symm (f : W₁.Iso W₂) (x : W₂.End) :
    W₁.rot (f.endEquiv.symm x) = f.endEquiv.symm (W₂.rot x) := f.symm.map_rot x

/-- The inverse of an isomorphism preserves the inverse rotations. -/
@[simp] theorem rot_symm_endEquiv_symm (f : W₁.Iso W₂) (x : W₂.End) :
    W₁.rot.symm (f.endEquiv.symm x) = f.endEquiv.symm (W₂.rot.symm x) := f.symm.map_rot_symm x

/-- An isomorphism preserves the number of edges finishing at each vertex. -/
@[simp] theorem inDegree_vertexEquiv (f : W₁.Iso W₂) (v : W₁.Vertex) :
    W₂.inDegree (f.vertexEquiv v) = W₁.inDegree v :=
  (Nat.card_congr (f.edgeEquiv.subtypeEquiv fun _ ↦ by simp)).symm

/-- An isomorphism preserves the number of edges starting at each vertex. -/
@[simp] theorem outDegree_vertexEquiv (f : W₁.Iso W₂) (v : W₁.Vertex) :
    W₂.outDegree (f.vertexEquiv v) = W₁.outDegree v :=
  (Nat.card_congr (f.edgeEquiv.subtypeEquiv fun _ ↦ by simp)).symm

/-- An isomorphism maps merge vertices to merge vertices. -/
@[simp] theorem isMerge_vertexEquiv (f : W₁.Iso W₂) (v : W₁.Vertex) :
    W₂.IsMerge (f.vertexEquiv v) ↔ W₁.IsMerge v := by simp [isMerge_iff]

/-- An isomorphism maps split vertices to split vertices. -/
@[simp] theorem isSplit_vertexEquiv (f : W₁.Iso W₂) (v : W₁.Vertex) :
    W₂.IsSplit (f.vertexEquiv v) ↔ W₁.IsSplit v := by simp [isSplit_iff]

/-- Isomorphic webs are nilvalent together. -/
theorem isNilvalent_iff (f : W₁.Iso W₂) : W₁.IsNilvalent ↔ W₂.IsNilvalent :=
  f.vertexEquiv.isEmpty_congr

/-- The inverse of an isomorphism preserves the number of edges finishing at each vertex. -/
@[simp] theorem inDegree_vertexEquiv_symm (f : W₁.Iso W₂) (v : W₂.Vertex) :
    W₁.inDegree (f.vertexEquiv.symm v) = W₂.inDegree v := f.symm.inDegree_vertexEquiv v

/-- The inverse of an isomorphism preserves the number of edges starting at each vertex. -/
@[simp] theorem outDegree_vertexEquiv_symm (f : W₁.Iso W₂) (v : W₂.Vertex) :
    W₁.outDegree (f.vertexEquiv.symm v) = W₂.outDegree v := f.symm.outDegree_vertexEquiv v

/-- The inverse of an isomorphism maps merge vertices to merge vertices. -/
@[simp] theorem isMerge_vertexEquiv_symm (f : W₁.Iso W₂) (v : W₂.Vertex) :
    W₁.IsMerge (f.vertexEquiv.symm v) ↔ W₂.IsMerge v := f.symm.isMerge_vertexEquiv v

/-- The inverse of an isomorphism maps split vertices to split vertices. -/
@[simp] theorem isSplit_vertexEquiv_symm (f : W₁.Iso W₂) (v : W₂.Vertex) :
    W₁.IsSplit (f.vertexEquiv.symm v) ↔ W₂.IsSplit v := f.symm.isSplit_vertexEquiv v

/-- Reversal of an isomorphism: the same bijections are an isomorphism of the reversed webs. -/
@[expose, simps]
def reverse (f : W₁.Iso W₂) : W₁.reverse.Iso W₂.reverse where
  vertexEquiv := f.vertexEquiv
  edgeEquiv := f.edgeEquiv
  endEquiv := f.endEquiv
  circleEquiv := f.circleEquiv
  map_srcEnd := f.map_tgtEnd
  map_tgtEnd := f.map_srcEnd
  map_vertex := f.map_vertex
  map_rot := f.map_rot

/-- Mirror of an isomorphism: the same bijections are an isomorphism of the mirrored webs. -/
@[expose, simps]
def mirror (f : W₁.Iso W₂) : W₁.mirror.Iso W₂.mirror where
  vertexEquiv := f.vertexEquiv
  edgeEquiv := f.edgeEquiv
  endEquiv := f.endEquiv
  circleEquiv := f.circleEquiv
  map_srcEnd := f.map_srcEnd
  map_tgtEnd := f.map_tgtEnd
  map_vertex := f.map_vertex
  map_rot := f.map_rot_symm

/-- The disjoint union of two isomorphisms. -/
@[expose, simps]
def disjointUnion {W₁ W₃ : ClosedWeb.{u}} {W₂ W₄ : ClosedWeb.{v}} (f : W₁.Iso W₂) (g : W₃.Iso W₄) :
    (W₁.disjointUnion W₃).Iso (W₂.disjointUnion W₄) where
  vertexEquiv := f.vertexEquiv.sumCongr g.vertexEquiv
  edgeEquiv := f.edgeEquiv.sumCongr g.edgeEquiv
  endEquiv := f.endEquiv.sumCongr g.endEquiv
  circleEquiv := f.circleEquiv.sumCongr g.circleEquiv
  map_srcEnd
    | .inl e => congrArg Sum.inl (f.map_srcEnd e)
    | .inr e => congrArg Sum.inr (g.map_srcEnd e)
  map_tgtEnd
    | .inl e => congrArg Sum.inl (f.map_tgtEnd e)
    | .inr e => congrArg Sum.inr (g.map_tgtEnd e)
  map_vertex
    | .inl x => congrArg Sum.inl (f.map_vertex x)
    | .inr x => congrArg Sum.inr (g.map_vertex x)
  map_rot
    | .inl x => congrArg Sum.inl (f.map_rot x)
    | .inr x => congrArg Sum.inr (g.map_rot x)

/-- Reversal of the identity is the identity. -/
@[simp] theorem reverse_refl (W : ClosedWeb.{u}) : (refl W).reverse = refl W.reverse := (rfl)

/-- Reversal commutes with inverses. -/
@[simp] theorem reverse_symm (f : W₁.Iso W₂) : f.reverse.symm = f.symm.reverse := (rfl)

/-- Reversal commutes with composition. -/
@[simp] theorem reverse_trans (f : W₁.Iso W₂) (g : W₂.Iso W₃) :
    f.reverse.trans g.reverse = (f.trans g).reverse := (rfl)

/-- The mirror of the identity is the identity. -/
@[simp] theorem mirror_refl (W : ClosedWeb.{u}) : (refl W).mirror = refl W.mirror := (rfl)

/-- Mirroring commutes with inverses. -/
@[simp] theorem mirror_symm (f : W₁.Iso W₂) : f.mirror.symm = f.symm.mirror := (rfl)

/-- Mirroring commutes with composition. -/
@[simp] theorem mirror_trans (f : W₁.Iso W₂) (g : W₂.Iso W₃) :
    f.mirror.trans g.mirror = (f.trans g).mirror := (rfl)

/-- The disjoint union of identities is the identity. -/
@[simp] theorem disjointUnion_refl (W₁ W₂ : ClosedWeb.{u}) :
    (refl W₁).disjointUnion (refl W₂) = refl _ := by ext (e | e) <;> rfl

/-- The inverse of a disjoint union of isomorphisms is the disjoint union of the inverses. -/
@[simp] theorem disjointUnion_symm {W₁ W₃ : ClosedWeb.{u}} {W₂ W₄ : ClosedWeb.{v}} (f : W₁.Iso W₂)
    (g : W₃.Iso W₄) : (f.disjointUnion g).symm = f.symm.disjointUnion g.symm := (rfl)

/-- Disjoint union of isomorphisms commutes with composition. -/
@[simp] theorem disjointUnion_trans {W₁ W₄ : ClosedWeb.{u}} {W₂ W₅ : ClosedWeb.{v}}
    {W₃ W₆ : ClosedWeb.{w}} (f : W₁.Iso W₂) (f' : W₂.Iso W₃) (g : W₄.Iso W₅) (g' : W₅.Iso W₆) :
    (f.disjointUnion g).trans (f'.disjointUnion g') = (f.trans f').disjointUnion (g.trans g') := by
  ext (e | e) <;> rfl

variable (W₁ W₂ W₃ : ClosedWeb.{u})

/-- The empty web is a left unit for disjoint union. -/
@[expose, simps]
def emptyDisjointUnion : ((∅ : ClosedWeb.{u}).disjointUnion W₁).Iso W₁ where
  vertexEquiv := Equiv.emptySum PEmpty W₁.Vertex
  edgeEquiv := Equiv.emptySum PEmpty W₁.Edge
  endEquiv := Equiv.emptySum PEmpty W₁.End
  circleEquiv := Equiv.emptySum PEmpty W₁.Circle
  map_srcEnd := by rintro (e | e); exacts [e.elim, rfl]
  map_tgtEnd := by rintro (e | e); exacts [e.elim, rfl]
  map_vertex := by rintro (x | x); exacts [x.elim, rfl]
  map_rot := by rintro (x | x); exacts [x.elim, rfl]

/-- The empty web is a right unit for disjoint union. -/
@[expose, simps]
def disjointUnionEmpty : (W₁.disjointUnion (∅ : ClosedWeb.{u})).Iso W₁ where
  vertexEquiv := Equiv.sumEmpty W₁.Vertex PEmpty
  edgeEquiv := Equiv.sumEmpty W₁.Edge PEmpty
  endEquiv := Equiv.sumEmpty W₁.End PEmpty
  circleEquiv := Equiv.sumEmpty W₁.Circle PEmpty
  map_srcEnd := by rintro (e | e); exacts [rfl, e.elim]
  map_tgtEnd := by rintro (e | e); exacts [rfl, e.elim]
  map_vertex := by rintro (x | x); exacts [rfl, x.elim]
  map_rot := by rintro (x | x); exacts [rfl, x.elim]

/-- Disjoint union is associative. -/
@[expose, simps]
def disjointUnionAssoc :
    ((W₁.disjointUnion W₂).disjointUnion W₃).Iso (W₁.disjointUnion (W₂.disjointUnion W₃)) where
  vertexEquiv := Equiv.sumAssoc _ _ _
  edgeEquiv := Equiv.sumAssoc _ _ _
  endEquiv := Equiv.sumAssoc _ _ _
  circleEquiv := Equiv.sumAssoc _ _ _
  map_srcEnd := by rintro ((e | e) | e) <;> rfl
  map_tgtEnd := by rintro ((e | e) | e) <;> rfl
  map_vertex := by rintro ((x | x) | x) <;> rfl
  map_rot := by rintro ((x | x) | x) <;> rfl

/-- Disjoint union is commutative. -/
@[expose, simps]
def disjointUnionComm : (W₁.disjointUnion W₂).Iso (W₂.disjointUnion W₁) where
  vertexEquiv := Equiv.sumComm _ _
  edgeEquiv := Equiv.sumComm _ _
  endEquiv := Equiv.sumComm _ _
  circleEquiv := Equiv.sumComm _ _
  map_srcEnd := by rintro (e | e) <;> rfl
  map_tgtEnd := by rintro (e | e) <;> rfl
  map_vertex := by rintro (x | x) <;> rfl
  map_rot := by rintro (x | x) <;> rfl

/-- Swapping the two pieces of a disjoint union twice is the identity. -/
@[simp] theorem disjointUnionComm_trans_disjointUnionComm :
    (disjointUnionComm W₁ W₂).trans (disjointUnionComm W₂ W₁) = refl _ := by ext (e | e) <;> rfl

/-- The inverse of the swap of the two pieces of a disjoint union is the swap back. -/
@[simp]
theorem disjointUnionComm_symm : (disjointUnionComm W₁ W₂).symm = disjointUnionComm W₂ W₁ := by
  ext (e | e) <;> rfl

/-- A bijection of circles is an isomorphism of the corresponding nilvalent webs. -/
@[expose, simps]
def circles {C : Type u} {C' : Type v} [Finite C] [Finite C'] (e : C ≃ C') :
    (ClosedWeb.circles C).Iso (ClosedWeb.circles C') where
  vertexEquiv := Equiv.equivPEmpty PEmpty
  edgeEquiv := Equiv.equivPEmpty PEmpty
  endEquiv := Equiv.equivPEmpty PEmpty
  circleEquiv := e
  map_srcEnd x := x.elim
  map_tgtEnd x := x.elim
  map_vertex x := x.elim
  map_rot x := x.elim

end Iso

/-- A nilvalent web is isomorphic to the web of its circles. -/
@[expose, simps]
def IsNilvalent.isoCircles {W : ClosedWeb.{u}} (h : W.IsNilvalent) : W.Iso (circles W.Circle) :=
  have : IsEmpty W.Vertex := W.isNilvalent_iff.1 h
  have : IsEmpty W.Edge := W.isNilvalent_iff_isEmpty_edge.1 h
  have : IsEmpty W.End := W.isNilvalent_iff_isEmpty_end.1 h
  { vertexEquiv := Equiv.equivPEmpty _
    edgeEquiv := Equiv.equivPEmpty _
    endEquiv := Equiv.equivPEmpty _
    circleEquiv := .refl _
    map_srcEnd := isEmptyElim
    map_tgtEnd := isEmptyElim
    map_vertex := isEmptyElim
    map_rot := isEmptyElim }

/-- Two webs of circles are isomorphic exactly when they have the same number of circles. -/
theorem nonempty_iso_circles_iff {C : Type u} {C' : Type v} [Finite C] [Finite C'] :
    Nonempty ((circles C).Iso (circles C')) ↔ Nat.card C = Nat.card C' :=
  ⟨fun ⟨f⟩ ↦ Nat.card_congr f.circleEquiv, fun h ↦ ⟨Iso.circles (Finite.card_eq.1 h).some⟩⟩

/-- Nilvalent webs are classified up to isomorphism by their number of circles. -/
theorem IsNilvalent.nonempty_iso_iff {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}} (h₁ : W₁.IsNilvalent)
    (h₂ : W₂.IsNilvalent) : Nonempty (W₁.Iso W₂) ↔ Nat.card W₁.Circle = Nat.card W₂.Circle :=
  ⟨fun ⟨f⟩ ↦ Nat.card_congr f.circleEquiv, fun h ↦
    ⟨h₁.isoCircles.trans ((nonempty_iso_circles_iff.2 h).some.trans h₂.isoCircles.symm)⟩⟩

/-- The empty web is not isomorphic to a nonempty web of circles, such as a single circle: both
are nilvalent, but only the second has a circle. -/
theorem not_nonempty_iso_empty_circles {C : Type v} [Finite C] [Nonempty C] :
    ¬Nonempty ((∅ : ClosedWeb.{u}).Iso (circles C)) := by
  rw [empty_eq_circles, nonempty_iso_circles_iff]
  simpa using (Nat.card_pos (α := C)).ne

/-! ### The theta web -/

/-- A theta web: two vertices joined by three interval edges. Edges `0` and `1` run from vertex `0`
to vertex `1` and edge `2` runs back, so vertex `0` is a split and vertex `1` a merge. The source
end of an edge is `Sum.inl` and its target end `Sum.inr`. At each of the two vertices, the
rotation cycles through the ends of edges `0`, `1`, `2` in this order. -/
abbrev theta : ClosedWeb.{0} where
  Vertex := Fin 2
  Edge := Fin 3
  End := Fin 3 ⊕ Fin 3
  Circle := PEmpty
  srcEnd := Sum.inl
  tgtEnd := Sum.inr
  vertex := Sum.elim (fun e ↦ if e = 2 then 1 else 0) (fun e ↦ if e = 2 then 0 else 1)
  rot :=
    letI x : Fin 3 → Fin 3 ⊕ Fin 3 := Sum.inl
    letI y : Fin 3 → Fin 3 ⊕ Fin 3 := Sum.inr
    (Equiv.swap (x 0) (x 1) * Equiv.swap (x 1) (y 2)) *
      (Equiv.swap (y 0) (y 1) * Equiv.swap (y 1) (x 2))
  sumElim_bijective := by rw [Sum.elim_inl_inr]; exact bijective_id
  vertex_eq_vertex_iff {x y} := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.apply_eq_of_apply_eq fun z ↦ by revert z; decide⟩
    rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
      first
      | exact absurd h (by decide)
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
  card_fiber_vertex v := by
    rw [Nat.card_eq_fintype_card]
    revert v
    decide
  exists_vertex_srcEnd_eq v := by revert v; decide
  exists_vertex_tgtEnd_eq v := by revert v; decide
  finite_edge := inferInstanceAs (Finite (Fin 3))
  finite_circle := inferInstanceAs (Finite PEmpty)

/-- The first vertex of the theta web is a split. -/
@[simp] theorem isSplit_theta_zero : theta.IsSplit 0 := by
  rw [isSplit_iff, outDegree_def, Nat.card_eq_fintype_card]
  decide

/-- The second vertex of the theta web is a merge. -/
@[simp] theorem isMerge_theta_one : theta.IsMerge 1 := by
  rw [isMerge_iff, inDegree_def, Nat.card_eq_fintype_card]
  decide

end ClosedWeb

end TauCeti
