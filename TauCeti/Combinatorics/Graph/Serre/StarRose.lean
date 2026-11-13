/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.SpanningTree

/-!
# The star of a rose

For types `ι` and `X`, the Serre graph `SerreGraph.starRose ι X` has a central vertex, one further
vertex for each `i : ι` joined to the center by one edge (a *spoke*), and one loop at the center
for each `x : X` (a *petal*). With the group `Gᵢ` at the tip of the spoke `i` and trivial groups
elsewhere, it is the graph of groups of a free product `G₁ ∗ ⋯ ∗ G_p ∗ F_q` drawn by Guirardel and
Levitt (`ι` has `p` elements and `X` has `q`). The spokes form its only spanning tree and the
petals are the remaining edges; the orientation `starRoseOrientation` chooses the dart of each
spoke leaving the center and one dart of each petal.

## Main definitions

* `TauCeti.SerreGraph.starRose`: the graph, with its vertices `starRose.center`, `starRose.tip i`
  and its darts `starRose.spoke i`, `starRose.petal x`.
* `TauCeti.SerreGraph.starRoseSpokes`: the darts of the spokes.
* `TauCeti.SerreGraph.starRoseTree`: the spanning tree formed by the spokes.
* `TauCeti.SerreGraph.starRoseOrientation`: the orientation by the darts leaving the center along
  a spoke and one dart of each petal.

## Main results

* `TauCeti.SerreGraph.isTree_restrict_starRoseSpokes`: the spokes form a tree on all vertices.
* the instance `Unique (starRose ι X).SpanningTree`: the spokes form the only spanning tree.
* `TauCeti.SerreGraph.isOrientation_starRoseOrientation`: the darts leaving the center along a
  spoke, together with one dart of each petal, form an orientation.

## Implementation notes

The vertices are `Option ι` and the darts `(ι ⊕ X) × Bool`, the dart `(a, true)` being the one
chosen by the orientation, as for `rose`. The graph and its named vertices and darts are exposed,
so that a family indexed by the vertices, such as the vertex groups of a graph of groups, can be
defined by cases and reduces at `starRose.center` and `starRose.tip i`. Vertices should be written
with these names rather than as `none` or `some i`: the type `(starRose ι X).V` is not unfolded
to `Option ι` by instance search or by `simp`.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction,
  Figure 1, and §3.2.
* J.-P. Serre, *Trees*, Chapter I, §2.3.
-/

public section

universe u v

namespace TauCeti.SerreGraph

/-- The star of a rose: a central vertex `none`, a vertex `some i` joined to the center by one
edge for each `i : ι`, and a loop at the center for each `x : X`. The dart `(Sum.inl i, true)`
goes from the center to `some i`. -/
@[expose] def starRose (ι : Type u) (X : Type v) : SerreGraph.{u, max u v} where
  V := Option ι
  E := (ι ⊕ X) × Bool
  src e := match e with
    | (.inl i, false) => some i
    | _ => none
  rev e := (e.1, !e.2)
  rev_rev e := Prod.ext rfl (Bool.not_not e.2)
  rev_ne e h := Bool.not_ne_self e.2 (congrArg Prod.snd h)

variable (ι : Type u) (X : Type v)

/-- The central vertex of the star of a rose. -/
@[expose] def starRose.center : (starRose ι X).V := none

variable {ι} in
/-- The vertex of the star of a rose at the end of the spoke `i`. -/
@[expose] def starRose.tip (i : ι) : (starRose ι X).V := some i

variable {ι} in
/-- The spoke of the star of a rose from the center to the vertex `tip i`. -/
@[expose] def starRose.spoke (i : ι) : (starRose ι X).E := (.inl i, true)

variable {X} in
/-- The dart of the petal `x` of the star of a rose chosen by the orientation. -/
@[expose] def starRose.petal (x : X) : (starRose ι X).E := (.inr x, true)

variable {ι X} in
/-- Every vertex of the star of a rose is the center or a tip. -/
theorem starRose.eq_center_or_eq_tip (a : (starRose ι X).V) :
    a = starRose.center ι X ∨ ∃ i, a = starRose.tip X i :=
  Option.eq_none_or_eq_some a

variable {ι X} in
/-- Distinct elements of `ι` give distinct tips. -/
theorem starRose.tip_injective : Function.Injective (starRose.tip X : ι → (starRose ι X).V) :=
  Option.some_injective ι

variable {ι X} in
@[simp] theorem starRose.tip_ne_center (i : ι) : starRose.tip X i ≠ starRose.center ι X :=
  Option.some_ne_none i

variable {ι X} in
@[simp] theorem starRose.center_ne_tip (i : ι) : starRose.center ι X ≠ starRose.tip X i :=
  (starRose.tip_ne_center i).symm

variable {ι} in
@[simp] theorem starRose_src_spoke (i : ι) :
    (starRose ι X).src (starRose.spoke X i) = starRose.center ι X := (rfl)

variable {ι} in
@[simp] theorem starRose_tgt_spoke (i : ι) :
    (starRose ι X).tgt (starRose.spoke X i) = starRose.tip X i := (rfl)

variable {X} in
@[simp] theorem starRose_src_petal (x : X) :
    (starRose ι X).src (starRose.petal ι x) = starRose.center ι X := (rfl)

variable {X} in
@[simp] theorem starRose_tgt_petal (x : X) :
    (starRose ι X).tgt (starRose.petal ι x) = starRose.center ι X := (rfl)

variable {ι X} in
theorem starRose_rev (e : (starRose ι X).E) : (starRose ι X).rev e = (e.1, !e.2) := (rfl)

/-! The coordinates of the named darts and of reversed darts, with which `simp` decides the
membership of a dart in `starRoseSpokes` and `starRoseOrientation`. -/

variable {ι} in
@[simp] theorem starRose.fst_spoke (i : ι) : (starRose.spoke X i).1 = .inl i := (rfl)

variable {ι} in
@[simp] theorem starRose.snd_spoke (i : ι) : (starRose.spoke X i).2 = true := (rfl)

variable {X} in
@[simp] theorem starRose.fst_petal (x : X) : (starRose.petal ι x).1 = .inr x := (rfl)

variable {X} in
@[simp] theorem starRose.snd_petal (x : X) : (starRose.petal ι x).2 = true := (rfl)

variable {ι X} in
@[simp] theorem starRose.fst_rev (e : (starRose ι X).E) : ((starRose ι X).rev e).1 = e.1 := (rfl)

variable {ι X} in
@[simp] theorem starRose.snd_rev (e : (starRose ι X).E) : ((starRose ι X).rev e).2 = !e.2 := (rfl)

/-- The spokes of the star of a rose: both darts of each edge joining the center to another
vertex. -/
def starRoseSpokes : Set (starRose ι X).E := {e | e.1.isLeft}

variable {ι X} in
@[simp] theorem mem_starRoseSpokes {e : (starRose ι X).E} :
    e ∈ starRoseSpokes ι X ↔ e.1.isLeft := Iff.rfl

variable {ι X} in
/-- The reverse of a dart of a spoke is a dart of the same spoke. -/
theorem rev_mem_starRoseSpokes (e : (starRose ι X).E) (he : e ∈ starRoseSpokes ι X) :
    (starRose ι X).rev e ∈ starRoseSpokes ι X := he

variable {ι X} in
-- A dart of a spoke ending at the tip `i` is the spoke `i`.
private theorem eq_spoke_of_tgt_eq_tip {e : (starRose ι X).E} (he : e ∈ starRoseSpokes ι X) {i : ι}
    (h : (starRose ι X).tgt e = starRose.tip X i) : e = starRose.spoke X i := by
  rw [mem_starRoseSpokes] at he
  rcases e with ⟨j | x, _ | _⟩
  · exact absurd h (starRose.center_ne_tip i)
  · rw [starRose.tip_injective h]
    rfl
  all_goals simp at he

variable {ι X} in
-- A dart of a spoke is not a loop.
private theorem ne_of_mem_starRoseSpokes {a b : (starRose ι X).V} (e : a ⟶ b)
    (he : e.1 ∈ starRoseSpokes ι X) : a ≠ b := by
  obtain ⟨e, rfl, rfl⟩ := e
  rw [mem_starRoseSpokes] at he
  rcases e with ⟨j | x, _ | _⟩
  · exact starRose.tip_ne_center j
  · exact starRose.center_ne_tip j
  all_goals simp at he

variable {ι X} in
-- Two consecutive darts of spokes, the second not reversing the first, meet at the center.
private theorem eq_center_of_mem_starRoseSpokes {a b c : (starRose ι X).V} (e : a ⟶ b) (f : b ⟶ c)
    (he : e.1 ∈ starRoseSpokes ι X) (hf : f.1 ∈ starRoseSpokes ι X)
    (hef : f.1 ≠ (starRose ι X).rev e.1) : b = starRose.center ι X := by
  obtain rfl | ⟨i, rfl⟩ := starRose.eq_center_or_eq_tip b
  · rfl
  · refine absurd ?_ hef
    rw [eq_spoke_of_tgt_eq_tip he e.2.2, ← eq_spoke_of_tgt_eq_tip
      (rev_mem_starRoseSpokes f.1 hf) ((tgt_rev _ _).trans f.2.1), rev_rev]

/-- The spokes of the star of a rose form a tree on all its vertices. -/
theorem isTree_restrict_starRoseSpokes :
    ((starRose ι X).restrict (starRoseSpokes ι X) rev_mem_starRoseSpokes).IsTree := by
  refine (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨⟨starRose.center ι X⟩, ?_⟩, ?_⟩
  · -- Every tip is joined to the center by its spoke.
    refine preconnected_of_forall_nonempty_path _ (starRose.center ι X) fun b => ?_
    obtain rfl | ⟨i, rfl⟩ := starRose.eq_center_or_eq_tip (X := X) b
    · exact ⟨.nil⟩
    · exact ⟨(Quiver.Hom.toPath ⟨⟨starRose.spoke X i, by simp⟩, by simp, by simp⟩)⟩
  · -- In a reduced path of spokes every inner vertex is the center, and spokes are not loops,
    -- so a nonempty reduced closed path of spokes would contain a loop at the center.
    refine (isAcyclic_restrict_iff _ _ _).mpr fun u p hp hpS => ?_
    rcases p with _ | ⟨_ | ⟨_ | ⟨q, d⟩, e⟩, f⟩
    · rfl
    · exact absurd rfl (ne_of_mem_starRoseSpokes f (hpS f.1 (by simp)))
    · have hef := ((Path.isReduced_cons_cons _ _ _ _).mp hp).2
      have he := hpS e.1 (by simp)
      have hf := hpS f.1 (by simp)
      -- Read cyclically, the closed path also turns from `f` to `e` without backtracking.
      have hfe : e.1 ≠ (starRose ι X).rev f.1 := fun h => hef (by rw [h, rev_rev])
      exact absurd ((eq_center_of_mem_starRoseSpokes f e hf he hfe).trans
        (eq_center_of_mem_starRoseSpokes e f he hf hef).symm) (ne_of_mem_starRoseSpokes e he)
    · have hp' := (Path.isReduced_cons_cons _ _ _ _).mp hp
      have hde := ((Path.isReduced_cons_cons _ _ _ _).mp hp'.1).2
      have he := hpS e.1 (by simp)
      exact absurd ((eq_center_of_mem_starRoseSpokes d e (hpS d.1 (by simp)) he hde).trans
        (eq_center_of_mem_starRoseSpokes e f he (hpS f.1 (by simp)) hp'.2).symm)
        (ne_of_mem_starRoseSpokes e he)

/-- The spanning tree of the star of a rose formed by its spokes. -/
def starRoseTree : (starRose ι X).SpanningTree where
  darts := starRoseSpokes ι X
  rev_mem := rev_mem_starRoseSpokes
  isTree := isTree_restrict_starRoseSpokes ι X

@[simp] theorem starRoseTree_darts : (starRoseTree ι X).darts = starRoseSpokes ι X := (rfl)

/-- The spokes form the only spanning tree of the star of a rose. -/
instance : Unique (starRose ι X).SpanningTree where
  default := starRoseTree ι X
  uniq T := by
    -- A spanning tree contains no petal, since a petal is a loop.
    have hT : T.darts ⊆ starRoseSpokes ι X := fun e he => by
      rw [mem_starRoseSpokes]
      rcases e with ⟨i | x, b⟩
      · rfl
      · exact (T.src_ne_tgt he rfl).elim
    -- The last dart of the tree path from the center to the tip `i` is the spoke `i`.
    have hspoke (i : ι) : starRose.spoke X i ∈ T.darts := by
      obtain ⟨p, -, hpT⟩ := T.exists_path (starRose.center ι X) (starRose.tip X i)
      -- The path is not empty, since the center is not a tip.
      obtain _ | ⟨q, f⟩ := p
      rw [← eq_spoke_of_tgt_eq_tip (hT (hpT f.1 (by simp))) f.2.2]
      exact hpT f.1 (by simp)
    ext e
    simp only [starRoseTree_darts]
    refine ⟨fun he => hT he, fun he => ?_⟩
    rw [mem_starRoseSpokes] at he
    rcases e with ⟨i | x, _ | _⟩
    · exact T.rev_mem _ (hspoke i)
    · exact hspoke i
    all_goals simp at he

/-- The orientation of the star of a rose by the darts with second coordinate `true`: the
spokes leaving the center and one dart of each petal. -/
def starRoseOrientation : Set (starRose ι X).E := {e | e.2 = true}

variable {ι X} in
@[simp] theorem mem_starRoseOrientation {e : (starRose ι X).E} :
    e ∈ starRoseOrientation ι X ↔ e.2 = true := Iff.rfl

/-- The darts leaving the center along a spoke and one dart of each petal form an orientation of
the star of a rose. -/
theorem isOrientation_starRoseOrientation :
    (starRose ι X).IsOrientation (starRoseOrientation ι X) :=
  ((starRose ι X).isOrientation_iff _).mpr fun _ => by simp

end TauCeti.SerreGraph
