/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.SpanningTree
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option

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
* `TauCeti.SerreGraph.starRoseGeomEdgeEquiv`: the geometric edges are indexed by `ι ⊕ X`.
* `TauCeti.SerreGraph.starRoseSpokes`: the darts of the spokes.
* `TauCeti.SerreGraph.starRoseTree`: the spanning tree formed by the spokes.
* `TauCeti.SerreGraph.starRoseOrientation`: the orientation by the darts leaving the center along
  a spoke and one dart of each petal.
* `TauCeti.SerreGraph.starRose.petalEquiv`: the petals are the darts of `starRoseOrientation`
  outside the spokes.

## Main results

* `TauCeti.SerreGraph.starRose.dart_cases`: every dart is a spoke, a petal, or the reverse of one.
* `TauCeti.SerreGraph.isTree_restrict_starRoseSpokes`: the spokes form a tree on all vertices.
* the instance `Unique (starRose ι X).SpanningTree`: the spokes form the only spanning tree.
* `TauCeti.SerreGraph.starRose_connected`: the star of a rose is connected.
* `TauCeti.SerreGraph.isOrientation_starRoseOrientation`: the darts leaving the center along a
  spoke, together with one dart of each petal, form an orientation.
* `TauCeti.SerreGraph.starRoseOrientation_diff_starRoseSpokes`: the darts of this orientation
  outside the spokes are the petals.

## Implementation notes

The vertices are `Option ι` and the darts `(ι ⊕ X) × Bool`, the dart `(a, true)` being the one
chosen by the orientation, as for `rose`. The graph and its named vertices and darts are exposed,
so that a family indexed by the vertices, such as the vertex groups of a graph of groups, can be
defined by cases and reduces at `starRose.center` and `starRose.tip i`. Vertices should be written
with these names rather than as `none` or `some i`: the type `(starRose ι X).V` is not unfolded
to `Option ι` by instance search or by `simp`, which is why its instances are declared here.
Darts are likewise handled through their names: `starRose.dart_cases` and the `simp` lemmas on
`starRose.spoke`, `starRose.petal` and their reverses stand in for the coordinates of a dart.

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

/-- The vertices of the star of a rose have decidable equality when `ι` does. -/
instance [DecidableEq ι] : DecidableEq (starRose ι X).V := inferInstanceAs (DecidableEq (Option ι))

/-- The darts of the star of a rose have decidable equality when `ι` and `X` do. -/
instance [DecidableEq ι] [DecidableEq X] : DecidableEq (starRose ι X).E :=
  inferInstanceAs (DecidableEq ((ι ⊕ X) × Bool))

/-- The star of a rose has finitely many vertices when `ι` is finite. -/
instance [Finite ι] : Finite (starRose ι X).V := inferInstanceAs (Finite (Option ι))

/-- The star of a rose has finitely many darts when `ι` and `X` are finite. -/
instance [Finite ι] [Finite X] : Finite (starRose ι X).E :=
  inferInstanceAs (Finite ((ι ⊕ X) × Bool))

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

variable {ι X}

/-- Every vertex of the star of a rose is the center or a tip. -/
theorem starRose.eq_center_or_eq_tip (a : (starRose ι X).V) :
    a = starRose.center ι X ∨ ∃ i, a = starRose.tip X i :=
  Option.eq_none_or_eq_some a

/-- Distinct elements of `ι` give distinct tips. -/
theorem starRose.tip_injective : Function.Injective (starRose.tip X : ι → (starRose ι X).V) :=
  Option.some_injective ι

@[simp] theorem starRose.tip_inj {i j : ι} : starRose.tip X i = starRose.tip X j ↔ i = j :=
  starRose.tip_injective.eq_iff

@[simp] theorem starRose.tip_ne_center (i : ι) : starRose.tip X i ≠ starRose.center ι X :=
  Option.some_ne_none i

@[simp] theorem starRose.center_ne_tip (i : ι) : starRose.center ι X ≠ starRose.tip X i :=
  (starRose.tip_ne_center i).symm

/-- Every dart of the star of a rose is a spoke, a petal, or the reverse of one. -/
@[elab_as_elim] theorem starRose.dart_cases {motive : (starRose ι X).E → Prop}
    (spoke : ∀ i, motive (starRose.spoke X i))
    (rev_spoke : ∀ i, motive ((starRose ι X).rev (starRose.spoke X i)))
    (petal : ∀ x, motive (starRose.petal ι x))
    (rev_petal : ∀ x, motive ((starRose ι X).rev (starRose.petal ι x))) (e : (starRose ι X).E) :
    motive e := by
  obtain ⟨i | x, _ | _⟩ := e
  exacts [rev_spoke i, spoke i, rev_petal x, petal x]

/-- Distinct elements of `ι` give distinct spokes. -/
theorem starRose.spoke_injective :
    Function.Injective (starRose.spoke X : ι → (starRose ι X).E) :=
  fun _ _ h => Sum.inl_injective (congrArg Prod.fst h)

@[simp] theorem starRose.spoke_inj {i j : ι} : starRose.spoke X i = starRose.spoke X j ↔ i = j :=
  starRose.spoke_injective.eq_iff

/-- Distinct elements of `X` give distinct petals. -/
theorem starRose.petal_injective :
    Function.Injective (starRose.petal ι : X → (starRose ι X).E) :=
  fun _ _ h => Sum.inr_injective (congrArg Prod.fst h)

@[simp] theorem starRose.petal_inj {x y : X} : starRose.petal ι x = starRose.petal ι y ↔ x = y :=
  starRose.petal_injective.eq_iff

@[simp] theorem starRose.spoke_ne_petal (i : ι) (x : X) :
    starRose.spoke X i ≠ starRose.petal ι x := nofun

@[simp] theorem starRose.petal_ne_spoke (x : X) (i : ι) :
    starRose.petal ι x ≠ starRose.spoke X i := nofun

@[simp] theorem starRose.spoke_ne_rev_spoke (i j : ι) :
    starRose.spoke X i ≠ (starRose ι X).rev (starRose.spoke X j) := nofun

@[simp] theorem starRose.rev_spoke_ne_spoke (i j : ι) :
    (starRose ι X).rev (starRose.spoke X i) ≠ starRose.spoke X j := nofun

@[simp] theorem starRose.spoke_ne_rev_petal (i : ι) (x : X) :
    starRose.spoke X i ≠ (starRose ι X).rev (starRose.petal ι x) := nofun

@[simp] theorem starRose.rev_petal_ne_spoke (x : X) (i : ι) :
    (starRose ι X).rev (starRose.petal ι x) ≠ starRose.spoke X i := nofun

@[simp] theorem starRose.petal_ne_rev_spoke (x : X) (i : ι) :
    starRose.petal ι x ≠ (starRose ι X).rev (starRose.spoke X i) := nofun

@[simp] theorem starRose.rev_spoke_ne_petal (i : ι) (x : X) :
    (starRose ι X).rev (starRose.spoke X i) ≠ starRose.petal ι x := nofun

@[simp] theorem starRose.petal_ne_rev_petal (x y : X) :
    starRose.petal ι x ≠ (starRose ι X).rev (starRose.petal ι y) := nofun

@[simp] theorem starRose.rev_petal_ne_petal (x y : X) :
    (starRose ι X).rev (starRose.petal ι x) ≠ starRose.petal ι y := nofun

@[simp] theorem starRose_src_spoke (i : ι) :
    (starRose ι X).src (starRose.spoke X i) = starRose.center ι X := (rfl)

@[simp] theorem starRose_tgt_spoke (i : ι) :
    (starRose ι X).tgt (starRose.spoke X i) = starRose.tip X i := (rfl)

@[simp] theorem starRose_src_petal (x : X) :
    (starRose ι X).src (starRose.petal ι x) = starRose.center ι X := (rfl)

@[simp] theorem starRose_tgt_petal (x : X) :
    (starRose ι X).tgt (starRose.petal ι x) = starRose.center ι X := (rfl)

/-- The only dart ending at the tip `i` is the spoke `i`. -/
@[simp] theorem starRose_tgt_eq_tip_iff {e : (starRose ι X).E} {i : ι} :
    (starRose ι X).tgt e = starRose.tip X i ↔ e = starRose.spoke X i := by
  cases e using starRose.dart_cases <;> simp

/-- The only dart starting at the tip `i` is the reverse of the spoke `i`. -/
@[simp] theorem starRose_src_eq_tip_iff {e : (starRose ι X).E} {i : ι} :
    (starRose ι X).src e = starRose.tip X i ↔ e = (starRose ι X).rev (starRose.spoke X i) := by
  cases e using starRose.dart_cases <;> simp [(starRose ι X).rev_injective.eq_iff]

variable (ι X)

/-- The geometric edges of the star of a rose are its spokes and its petals. -/
def starRoseGeomEdgeEquiv : (starRose ι X).GeomEdge ≃ ι ⊕ X where
  toFun := GeomEdge.lift (starRose ι X) (fun e => e.1) fun _ => rfl
  invFun := Sum.elim (fun i => (starRose ι X).toGeomEdge (starRose.spoke X i))
    fun x => (starRose ι X).toGeomEdge (starRose.petal ι x)
  left_inv g := by
    obtain ⟨e, rfl⟩ := (starRose ι X).toGeomEdge_surjective g
    refine (congrArg (Sum.elim _ _) (GeomEdge.lift_toGeomEdge ..)).trans ?_
    cases e using starRose.dart_cases
    exacts [rfl, ((starRose ι X).toGeomEdge_rev _).symm, rfl,
      ((starRose ι X).toGeomEdge_rev _).symm]
  right_inv a := by cases a <;> exact GeomEdge.lift_toGeomEdge ..

variable {ι X}

@[simp] theorem starRoseGeomEdgeEquiv_toGeomEdge_spoke (i : ι) :
    starRoseGeomEdgeEquiv ι X ((starRose ι X).toGeomEdge (starRose.spoke X i)) = .inl i :=
  GeomEdge.lift_toGeomEdge ..

@[simp] theorem starRoseGeomEdgeEquiv_toGeomEdge_petal (x : X) :
    starRoseGeomEdgeEquiv ι X ((starRose ι X).toGeomEdge (starRose.petal ι x)) = .inr x :=
  GeomEdge.lift_toGeomEdge ..

@[simp] theorem starRoseGeomEdgeEquiv_symm_inl (i : ι) :
    (starRoseGeomEdgeEquiv ι X).symm (.inl i) = (starRose ι X).toGeomEdge (starRose.spoke X i) :=
  (rfl)

@[simp] theorem starRoseGeomEdgeEquiv_symm_inr (x : X) :
    (starRoseGeomEdgeEquiv ι X).symm (.inr x) = (starRose ι X).toGeomEdge (starRose.petal ι x) :=
  (rfl)

variable (ι X)

/-- The spokes of the star of a rose: both darts of each edge joining the center to another
vertex. -/
def starRoseSpokes : Set (starRose ι X).E := {e | e.1.isLeft}

variable {ι X}

@[simp] theorem spoke_mem_starRoseSpokes (i : ι) : starRose.spoke X i ∈ starRoseSpokes ι X :=
  (rfl)

@[simp] theorem petal_notMem_starRoseSpokes (x : X) : starRose.petal ι x ∉ starRoseSpokes ι X :=
  nofun

@[simp] theorem rev_mem_starRoseSpokes_iff {e : (starRose ι X).E} :
    (starRose ι X).rev e ∈ starRoseSpokes ι X ↔ e ∈ starRoseSpokes ι X := Iff.rfl

/-- The reverse of a dart of a spoke is a dart of the same spoke. -/
theorem rev_mem_starRoseSpokes (e : (starRose ι X).E) (he : e ∈ starRoseSpokes ι X) :
    (starRose ι X).rev e ∈ starRoseSpokes ι X := he

theorem mem_starRoseSpokes_iff {e : (starRose ι X).E} :
    e ∈ starRoseSpokes ι X ↔
      ∃ i, e = starRose.spoke X i ∨ e = (starRose ι X).rev (starRose.spoke X i) := by
  cases e using starRose.dart_cases <;> simp [(starRose ι X).rev_injective.eq_iff, eq_comm]

-- A dart of a spoke is not a loop.
private theorem ne_of_mem_starRoseSpokes {a b : (starRose ι X).V} (e : a ⟶ b)
    (he : e.1 ∈ starRoseSpokes ι X) : a ≠ b := by
  obtain ⟨e, rfl, rfl⟩ := e
  cases e using starRose.dart_cases <;> simp_all

-- Two consecutive darts, the second not reversing the first, meet at the center.
private theorem eq_center_of_ne_rev {a b c : (starRose ι X).V} (e : a ⟶ b) (f : b ⟶ c)
    (hef : f.1 ≠ (starRose ι X).rev e.1) : b = starRose.center ι X := by
  obtain rfl | ⟨i, rfl⟩ := starRose.eq_center_or_eq_tip b
  · rfl
  · rw [starRose_src_eq_tip_iff.mp f.2.1, starRose_tgt_eq_tip_iff.mp e.2.2] at hef
    exact absurd rfl hef

variable (ι X)

/-- The spokes of the star of a rose form a tree on all its vertices. -/
theorem isTree_restrict_starRoseSpokes :
    ((starRose ι X).restrict (starRoseSpokes ι X) rev_mem_starRoseSpokes).IsTree := by
  refine (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨⟨starRose.center ι X⟩, ?_⟩, ?_⟩
  · -- Every tip is joined to the center by its spoke.
    refine preconnected_of_forall_nonempty_path _ (starRose.center ι X) fun b => ?_
    obtain rfl | ⟨i, rfl⟩ := starRose.eq_center_or_eq_tip (X := X) b
    · exact ⟨.nil⟩
    · exact ⟨(Quiver.Hom.toPath ⟨⟨starRose.spoke X i, by simp⟩, by simp, by simp⟩)⟩
  · -- In a reduced path every inner vertex is the center, and spokes are not loops, so a
    -- nonempty reduced closed path of spokes would contain a loop at the center.
    refine (isAcyclic_restrict_iff _ _ _).mpr fun u p hp hpS => ?_
    rcases p with _ | ⟨_ | ⟨_ | ⟨q, d⟩, e⟩, f⟩
    · rfl
    · exact absurd rfl (ne_of_mem_starRoseSpokes f (hpS f.1 (by simp)))
    · have hef := ((Path.isReduced_cons_cons _ _ _ _).mp hp).2
      -- Read cyclically, the closed path also turns from `f` to `e` without backtracking.
      have hfe : e.1 ≠ (starRose ι X).rev f.1 := fun h => hef (by rw [h, rev_rev])
      exact absurd ((eq_center_of_ne_rev f e hfe).trans (eq_center_of_ne_rev e f hef).symm)
        (ne_of_mem_starRoseSpokes e (hpS e.1 (by simp)))
    · have hp' := (Path.isReduced_cons_cons _ _ _ _).mp hp
      exact absurd ((eq_center_of_ne_rev d e ((Path.isReduced_cons_cons _ _ _ _).mp hp'.1).2).trans
        (eq_center_of_ne_rev e f hp'.2).symm) (ne_of_mem_starRoseSpokes e (hpS e.1 (by simp)))

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
      have := T.src_ne_tgt he
      cases e using starRose.dart_cases <;> simp_all
    -- The last dart of the tree path from the center to the tip `i` is the spoke `i`.
    have hspoke (i : ι) : starRose.spoke X i ∈ T.darts := by
      obtain ⟨p, -, hpT⟩ := T.exists_path (starRose.center ι X) (starRose.tip X i)
      -- The path is not empty, since the center is not a tip.
      obtain _ | ⟨q, f⟩ := p
      exact starRose_tgt_eq_tip_iff.mp f.2.2 ▸ hpT f.1 (by simp)
    ext e
    simp only [starRoseTree_darts]
    refine ⟨fun he => hT he, fun he => ?_⟩
    obtain ⟨i, rfl | rfl⟩ := mem_starRoseSpokes_iff.mp he
    exacts [hspoke i, T.rev_mem _ (hspoke i)]

/-- The star of a rose is connected. -/
theorem starRose_connected : (starRose ι X).Connected :=
  (nonempty_spanningTree_iff _).mp ⟨starRoseTree ι X⟩

/-- The orientation of the star of a rose by the spokes leaving the center and one dart of each
petal. -/
def starRoseOrientation : Set (starRose ι X).E := {e | e.2 = true}

variable {ι X}

@[simp] theorem spoke_mem_starRoseOrientation (i : ι) :
    starRose.spoke X i ∈ starRoseOrientation ι X := (rfl)

@[simp] theorem petal_mem_starRoseOrientation (x : X) :
    starRose.petal ι x ∈ starRoseOrientation ι X := (rfl)

variable (ι X) in
/-- The spokes leaving the center, together with one dart of each petal, form an orientation of
the star of a rose. -/
theorem isOrientation_starRoseOrientation :
    (starRose ι X).IsOrientation (starRoseOrientation ι X) :=
  ((starRose ι X).isOrientation_iff _).mpr fun e => by
    cases e using starRose.dart_cases <;>
      simp only [rev_rev, spoke_mem_starRoseOrientation, petal_mem_starRoseOrientation,
        not_true_eq_false, true_iff, iff_false] <;> exact nofun

@[simp] theorem rev_mem_starRoseOrientation_iff {e : (starRose ι X).E} :
    (starRose ι X).rev e ∈ starRoseOrientation ι X ↔ e ∉ starRoseOrientation ι X :=
  (isOrientation_starRoseOrientation ι X).mem_rev_iff _ e

theorem mem_starRoseOrientation_iff {e : (starRose ι X).E} :
    e ∈ starRoseOrientation ι X ↔
      (∃ i, e = starRose.spoke X i) ∨ ∃ x, e = starRose.petal ι x := by
  cases e using starRose.dart_cases <;> simp [eq_comm]

variable (ι X)

/-- The darts of the orientation outside the spanning tree are the petals. -/
theorem starRoseOrientation_diff_starRoseSpokes :
    starRoseOrientation ι X \ starRoseSpokes ι X = Set.range (starRose.petal ι) := by
  ext e
  cases e using starRose.dart_cases <;> simp

/-- The petals of the star of a rose, as the darts of the orientation outside the spanning tree. -/
noncomputable def starRose.petalEquiv : X ≃ ↥(starRoseOrientation ι X \ starRoseSpokes ι X) :=
  (Equiv.ofInjective _ starRose.petal_injective).trans
    (Equiv.subtypeEquivRight (Set.ext_iff.mp (starRoseOrientation_diff_starRoseSpokes ι X).symm))

variable {ι X}

@[simp] theorem starRose.petalEquiv_apply (x : X) :
    (starRose.petalEquiv ι X x : (starRose ι X).E) = starRose.petal ι x := (rfl)

@[simp] theorem starRose.petalEquiv_symm_apply (x : X)
    (h : starRose.petal ι x ∈ starRoseOrientation ι X \ starRoseSpokes ι X) :
    (starRose.petalEquiv ι X).symm ⟨starRose.petal ι x, h⟩ = x :=
  (starRose.petalEquiv ι X).symm_apply_eq.mpr (Subtype.ext (rfl))

end TauCeti.SerreGraph
