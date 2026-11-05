/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Polygonal complexes and their vertex links

A polygonal complex is a Serre graph, its one-skeleton, together with a family of faces. Each
face is a polygon whose sides are attached, in cyclic order, to a closed sequence of darts of the
one-skeleton: the `i`-th side of a face ends where its `(i + 1)`-st side starts, cyclically. Loops,
parallel edges and repeated darts along a face are all allowed, so the one-vertex polygons
`a b a⁻¹ b⁻¹` (a torus) and `a a` (a projective plane) are polygonal complexes.

Distinct occurrences of the same vertex along the faces are kept apart as *corners*
(`PolygonalComplex.Corner`): the corner `(f, i)` of the face `f` sits at the start of its `i`-th
side, between the incoming side `i - 1` and the outgoing side `i`. A corner has two *germs*, darts
starting at its vertex: the reverse of its incoming side and its outgoing side
(`PolygonalComplex.cornerEnds`).

The *link* of a vertex `v` (`PolygonalComplex.vertexLink`) is the Serre graph whose vertices are
the darts starting at `v` and which has one edge, joining its two germs, for every corner at `v`.
Its degrees are counted with darts (`PolygonalComplex.linkDegree`), so that a corner whose two
germs coincide is a loop of the link contributing two. A neighbourhood of `v` in the realization
of the complex is the cone on this link, so it is a disc or a half-disc exactly when the link is
a finite circle or a finite interval (`PolygonalComplex.HasSurfaceLink`).

The degree of a germ `e` in its link counts the face sides traversing `e` or its reverse
(`PolygonalComplex.linkDegree_eq_sideCount_rev_add_sideCount`): every side through the edge of
`e` contributes exactly one corner at `src e` having `e` as a germ. This turns the local surface
condition into the global statement that every edge lies on one or two face sides.

## Main definitions

* `TauCeti.PolygonalComplex`: a Serre graph with faces attached along closed dart sequences.
* `TauCeti.PolygonalComplex.Corner`, `TauCeti.PolygonalComplex.cornerEnds`: corners of faces and
  their two germs.
* `TauCeti.PolygonalComplex.vertexLink`: the link of a vertex.
* `TauCeti.PolygonalComplex.linkDegree`: the degree of a germ in its link.
* `TauCeti.PolygonalComplex.sideCount`: the number of face sides traversing a dart.
* `TauCeti.PolygonalComplex.HasSurfaceLink`: the link of a vertex is a finite circle or a finite
  interval.
* `TauCeti.PolygonalComplex.eulerChar`: vertices minus geometric edges plus faces.
* `TauCeti.PolygonalComplex.IsOrientable`: the faces can be oriented so that any two distinct
  side occurrences along the same geometric edge traverse it in opposite directions.

## Main results

* `TauCeti.PolygonalComplex.linkDegree_eq_sideCount_rev_add_sideCount`: when finitely many face
  sides traverse `e` or its reverse, the degree of the germ `e` is the number of such sides.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1, 6.2 and 6.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1.
-/

public section

universe u v w

namespace TauCeti

/-- A polygonal complex: a Serre graph, the one-skeleton, with a family of faces. The face `f` is a
polygon with `sides f ≥ 1` sides, and its `i`-th side is attached along the dart `side f i`; the
sides of a face form a closed dart sequence, read cyclically. -/
structure PolygonalComplex where
  /-- The one-skeleton. -/
  graph : SerreGraph.{u, v}
  /-- The faces. -/
  Face : Type w
  /-- The number of sides of a face. -/
  sides : Face → ℕ
  /-- Every face has at least one side. -/
  sides_pos : ∀ f, 0 < sides f
  /-- The dart along which the `i`-th side of the face `f` is attached. -/
  side : (f : Face) → Fin (sides f) → graph.E
  /-- Each side of a face ends where the cyclically next side starts. -/
  tgt_side : ∀ f i, graph.tgt (side f i) = graph.src (side f (finRotate (sides f) i))

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w})

/-! ### Corners and their germs -/

/-- The corners of the faces. The corner `⟨f, i⟩` sits at the start of the `i`-th side of the
face `f`; distinct occurrences of a vertex along the faces are distinct corners. Corners are also
the side occurrences of the faces: `⟨f, i⟩` indexes the `i`-th side of `f`. -/
abbrev Corner : Type w := Σ f : C.Face, Fin (C.sides f)

/-- The outgoing side of a corner: the side of its face starting at the corner. -/
def outgoing (c : C.Corner) : C.graph.E := C.side c.1 c.2

/-- The incoming side of a corner: the side of its face ending at the corner. -/
def incoming (c : C.Corner) : C.graph.E := C.side c.1 ((finRotate (C.sides c.1)).symm c.2)

theorem outgoing_def (c : C.Corner) : C.outgoing c = C.side c.1 c.2 := (rfl)

theorem incoming_def (c : C.Corner) :
    C.incoming c = C.side c.1 ((finRotate (C.sides c.1)).symm c.2) := (rfl)

/-- The corner following `c` along its face. -/
def nextCorner (c : C.Corner) : C.Corner := ⟨c.1, finRotate (C.sides c.1) c.2⟩

/-- The corner preceding `c` along its face. -/
def prevCorner (c : C.Corner) : C.Corner := ⟨c.1, (finRotate (C.sides c.1)).symm c.2⟩

theorem nextCorner_def (c : C.Corner) : C.nextCorner c = ⟨c.1, finRotate (C.sides c.1) c.2⟩ :=
  (rfl)

theorem prevCorner_def (c : C.Corner) :
    C.prevCorner c = ⟨c.1, (finRotate (C.sides c.1)).symm c.2⟩ := (rfl)

/-- The corner following `c` lies on the same face. -/
@[simp] theorem nextCorner_fst (c : C.Corner) : (C.nextCorner c).1 = c.1 := (rfl)

/-- The corner preceding `c` lies on the same face. -/
@[simp] theorem prevCorner_fst (c : C.Corner) : (C.prevCorner c).1 = c.1 := (rfl)

@[simp] theorem prevCorner_nextCorner (c : C.Corner) : C.prevCorner (C.nextCorner c) = c :=
  Sigma.ext rfl (heq_of_eq ((finRotate _).symm_apply_apply c.2))

@[simp] theorem nextCorner_prevCorner (c : C.Corner) : C.nextCorner (C.prevCorner c) = c :=
  Sigma.ext rfl (heq_of_eq ((finRotate _).apply_symm_apply c.2))

/-- The incoming side of a corner is the outgoing side of the preceding corner. -/
theorem incoming_eq_outgoing_prevCorner (c : C.Corner) :
    C.incoming c = C.outgoing (C.prevCorner c) := (rfl)

@[simp] theorem incoming_nextCorner (c : C.Corner) :
    C.incoming (C.nextCorner c) = C.outgoing c := by
  rw [incoming_eq_outgoing_prevCorner, prevCorner_nextCorner]

/-- The vertex at which a corner sits. -/
def cornerVertex (c : C.Corner) : C.graph.V := C.graph.src (C.outgoing c)

@[simp] theorem src_outgoing (c : C.Corner) : C.graph.src (C.outgoing c) = C.cornerVertex c :=
  (rfl)

@[simp] theorem tgt_outgoing (c : C.Corner) :
    C.graph.tgt (C.outgoing c) = C.cornerVertex (C.nextCorner c) :=
  C.tgt_side c.1 c.2

@[simp] theorem tgt_incoming (c : C.Corner) : C.graph.tgt (C.incoming c) = C.cornerVertex c := by
  rw [incoming_eq_outgoing_prevCorner, tgt_outgoing, nextCorner_prevCorner]

/-- The two germs of a corner, both starting at its vertex: the reverse of its incoming side and
its outgoing side. -/
def cornerEnds (c : C.Corner) : C.graph.E × C.graph.E :=
  (C.graph.rev (C.incoming c), C.outgoing c)

@[simp] theorem cornerEnds_fst (c : C.Corner) :
    (C.cornerEnds c).1 = C.graph.rev (C.incoming c) := (rfl)

@[simp] theorem cornerEnds_snd (c : C.Corner) : (C.cornerEnds c).2 = C.outgoing c := (rfl)

/-! ### Vertex links -/

/-- The link of the vertex `v`. Its vertices are the germs at `v`, the darts starting at `v`, and
it has one geometric edge for each corner at `v`, joining the two germs of that corner. The link
dart `(c, true)` starts at the outgoing side of `c` and its reverse `(c, false)` starts at the
reverse of the incoming side. A corner whose two germs coincide is a loop of the link. The
vertex and dart types are exposed, so that germs and corners are vertices and darts of the link. -/
@[expose] def vertexLink (v : C.graph.V) : SerreGraph.{v, w} where
  V := {e : C.graph.E // C.graph.src e = v}
  E := {c : C.Corner // C.cornerVertex c = v} × Bool
  src d := ⟨cond d.2 (C.cornerEnds d.1.1).2 (C.cornerEnds d.1.1).1, by
    rcases d with ⟨⟨c, rfl⟩, _ | _⟩ <;> simp⟩
  rev d := (d.1, !d.2)
  rev_rev d := by simp
  rev_ne d := by simp [Prod.ext_iff]

@[simp] theorem vertexLink_rev {v : C.graph.V} (d : (C.vertexLink v).E) :
    (C.vertexLink v).rev d = (d.1, !d.2) := (rfl)

/-- The link dart `d` ends where its reverse starts. -/
@[simp] theorem vertexLink_tgt {v : C.graph.V} (d : (C.vertexLink v).E) :
    (C.vertexLink v).tgt d = (C.vertexLink v).src (d.1, !d.2) := (rfl)

@[simp] theorem vertexLink_src_true {v : C.graph.V} (c : {c : C.Corner // C.cornerVertex c = v}) :
    ((C.vertexLink v).src (c, true)).1 = C.outgoing c.1 := (rfl)

@[simp] theorem vertexLink_src_false {v : C.graph.V}
    (c : {c : C.Corner // C.cornerVertex c = v}) :
    ((C.vertexLink v).src (c, false)).1 = C.graph.rev (C.incoming c.1) := (rfl)

/-- In a complex with finitely many faces, each vertex link has finitely many darts. -/
instance [Finite C.Face] (v : C.graph.V) : Finite (C.vertexLink v).E :=
  inferInstanceAs (Finite ({c : C.Corner // C.cornerVertex c = v} × Bool))

/-- In the link of `x`, a corner at `x` joins its outgoing side to the reverse of its incoming
side. -/
theorem nonempty_vertexLink_path {x : C.graph.V} (c : {c : C.Corner // C.cornerVertex c = x})
    {a b : (C.vertexLink x).V} (ha : a.1 = C.outgoing c.1)
    (hb : b.1 = C.graph.rev (C.incoming c.1)) : Nonempty ((C.vertexLink x).Path a b) :=
  ⟨Quiver.Hom.toPath (⟨(c, true), Subtype.ext ha.symm, Subtype.ext hb.symm⟩ : Quiver.Hom a b)⟩

/-- The degree of the germ `e` in the link of its source: the `Nat.card` of the link darts
starting at `e`. A corner both of whose germs are `e` contributes two. As with `Nat.card`, this is
`0` when there are infinitely many such darts; it is the ordinary count when `C.Face` is finite. -/
noncomputable def linkDegree (e : C.graph.E) : ℕ :=
  Nat.card {d : (C.vertexLink (C.graph.src e)).E // ((C.vertexLink _).src d).1 = e}

theorem linkDegree_def (e : C.graph.E) :
    C.linkDegree e =
      Nat.card {d : (C.vertexLink (C.graph.src e)).E // ((C.vertexLink _).src d).1 = e} :=
  (rfl)

/-- The number of face sides attached along the dart `e`, as the `Nat.card` of the corners whose
outgoing side is `e`. As with `Nat.card`, this is `0` when there are infinitely many such corners;
it is the ordinary count when `C.Face` is finite. -/
noncomputable def sideCount (e : C.graph.E) : ℕ := Nat.card {c : C.Corner // C.outgoing c = e}

theorem sideCount_def (e : C.graph.E) :
    C.sideCount e = Nat.card {c : C.Corner // C.outgoing c = e} := (rfl)

/-- A dart traversed by finitely many face sides lies on a face side exactly when its side count
is positive. -/
theorem sideCount_pos_iff {e : C.graph.E} [Finite {c : C.Corner // C.outgoing c = e}] :
    0 < C.sideCount e ↔ ∃ c, C.outgoing c = e := by
  rw [sideCount_def, Nat.card_pos_iff]
  simp only [nonempty_subtype, and_iff_left_iff_imp]
  exact fun _ => inferInstance

/-- The link darts starting at the germ `e` are the corners whose outgoing side is `e`, together
with the corners whose incoming side is `rev e`; the latter are the successors of the corners whose
outgoing side is `rev e`. -/
private def linkFiberEquiv (e : C.graph.E) :
    {d : (C.vertexLink (C.graph.src e)).E // ((C.vertexLink _).src d).1 = e} ≃
      {c : C.Corner // C.outgoing c = C.graph.rev e} ⊕ {c : C.Corner // C.outgoing c = e} where
  toFun d := match d with
    | ⟨(c, false), h⟩ => .inl ⟨C.prevCorner c.1, by
        rw [← incoming_eq_outgoing_prevCorner, ← C.graph.rev_rev (C.incoming _)]
        exact congrArg C.graph.rev h⟩
    | ⟨(c, true), h⟩ => .inr ⟨c.1, h⟩
  invFun s := match s with
    | .inl c => ⟨(⟨C.nextCorner c.1, by
        rw [← tgt_outgoing, c.2, SerreGraph.tgt_rev]⟩, false), by
        simp [c.2]⟩
    | .inr c => ⟨(⟨c.1, by rw [← src_outgoing, c.2]⟩, true), c.2⟩
  left_inv d := by
    rcases d with ⟨⟨c, _ | _⟩, h⟩ <;> simp
  right_inv s := by
    rcases s with c | c <;> simp

/-- The degree of a germ `e` in its link is the number of face sides attached along `e` or along
its reverse, when there are finitely many such sides: every such side gives exactly one corner at
`src e` having `e` as a germ. -/
theorem linkDegree_eq_sideCount_rev_add_sideCount (e : C.graph.E)
    [Finite {c : C.Corner // C.outgoing c = C.graph.rev e}]
    [Finite {c : C.Corner // C.outgoing c = e}] :
    C.linkDegree e = C.sideCount (C.graph.rev e) + C.sideCount e := by
  rw [linkDegree_def, sideCount_def, sideCount_def, Nat.card_congr (C.linkFiberEquiv e),
    Nat.card_sum]

/-- A germ and its reverse have the same link degree: both count the face sides along their
common edge. -/
@[simp] theorem linkDegree_rev (e : C.graph.E) :
    C.linkDegree (C.graph.rev e) = C.linkDegree e := by
  rw [linkDegree_def, linkDegree_def, Nat.card_congr (C.linkFiberEquiv _),
    Nat.card_congr (C.linkFiberEquiv e), SerreGraph.rev_rev]
  exact Nat.card_congr (Equiv.sumComm _ _)

/-! ### Surface links -/

/-- The link of `v` is a finite circle or a finite interval: it is finite, nonempty and connected,
and either every germ at `v` has degree two, or exactly two distinct germs have degree one and all
others have degree two. A one-edge circle is a link loop, and a one-edge interval is a single link
edge between two distinct germs. These are exactly the vertices with a disc or half-disc
neighbourhood in the realization; the condition excludes pinched vertices. -/
def HasSurfaceLink (v : C.graph.V) : Prop :=
  Finite (C.vertexLink v).E ∧ (C.vertexLink v).Connected ∧
    ((∀ e, C.graph.src e = v → C.linkDegree e = 2) ∨
      ∃ e₁ e₂, e₁ ≠ e₂ ∧ C.graph.src e₁ = v ∧ C.graph.src e₂ = v ∧ C.linkDegree e₁ = 1 ∧
        C.linkDegree e₂ = 1 ∧ ∀ e, C.graph.src e = v → e ≠ e₁ → e ≠ e₂ → C.linkDegree e = 2)

theorem hasSurfaceLink_iff (v : C.graph.V) :
    C.HasSurfaceLink v ↔ Finite (C.vertexLink v).E ∧ (C.vertexLink v).Connected ∧
      ((∀ e, C.graph.src e = v → C.linkDegree e = 2) ∨
        ∃ e₁ e₂, e₁ ≠ e₂ ∧ C.graph.src e₁ = v ∧ C.graph.src e₂ = v ∧ C.linkDegree e₁ = 1 ∧
          C.linkDegree e₂ = 1 ∧ ∀ e, C.graph.src e = v → e ≠ e₁ → e ≠ e₂ → C.linkDegree e = 2) :=
  Iff.rfl

/-- At a vertex with a surface link every germ has degree one or two. -/
theorem HasSurfaceLink.linkDegree_eq_one_or_two {e : C.graph.E}
    (h : C.HasSurfaceLink (C.graph.src e)) : C.linkDegree e = 1 ∨ C.linkDegree e = 2 := by
  obtain ⟨-, -, hcirc | ⟨e₁, e₂, -, -, -, h₁, h₂, h⟩⟩ := h
  · exact .inr (hcirc e rfl)
  · by_cases he₁ : e = e₁
    · exact .inl (he₁ ▸ h₁)
    by_cases he₂ : e = e₂
    · exact .inl (he₂ ▸ h₂)
    exact .inr (h e rfl he₁ he₂)

/-- At a vertex with a surface link, the germs of degree one are either absent (a circle link) or
exactly two (an interval link). -/
theorem HasSurfaceLink.eq_empty_or_eq_pair {v : C.graph.V} (h : C.HasSurfaceLink v) :
    {e | C.graph.src e = v ∧ C.linkDegree e = 1} = ∅ ∨
      ∃ e₁ e₂, e₁ ≠ e₂ ∧ {e | C.graph.src e = v ∧ C.linkDegree e = 1} = {e₁, e₂} := by
  obtain ⟨-, -, hcirc | ⟨e₁, e₂, hne, hs₁, hs₂, h₁, h₂, h⟩⟩ := h
  · refine .inl (Set.eq_empty_of_forall_notMem fun e ⟨hs, he⟩ => ?_)
    rw [hcirc e hs] at he
    exact absurd he (by decide)
  · refine .inr ⟨e₁, e₂, hne, Set.ext fun e => ⟨fun ⟨hs, he⟩ => ?_, ?_⟩⟩
    · by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      rw [h e hs hmem.1 hmem.2] at he
      exact absurd he (by decide)
    · rintro (rfl | rfl)
      exacts [⟨hs₁, h₁⟩, ⟨hs₂, h₂⟩]

/-! ### Euler characteristic and orientability -/

/-- The Euler characteristic of a polygonal complex: the number of vertices, minus the number of
geometric edges, plus the number of faces. It is meaningful for finite complexes. -/
noncomputable def eulerChar : ℤ := Nat.card C.graph.V - Nat.card C.graph.GeomEdge + Nat.card C.Face

theorem eulerChar_def :
    C.eulerChar = Nat.card C.graph.V - Nat.card C.graph.GeomEdge + Nat.card C.Face := (rfl)

/-- The dart traversed by the side occurrence `c` once the face of `c` is given the orientation
`σ`: the attaching dart if `σ` keeps the face orientation, its reverse otherwise. Reversing a face
reverses each of its sides. -/
def orientedSide (σ : C.Face → Bool) (c : C.Corner) : C.graph.E :=
  cond (σ c.1) (C.outgoing c) (C.graph.rev (C.outgoing c))

@[simp] theorem orientedSide_of_eq_true {σ : C.Face → Bool} {c : C.Corner} (h : σ c.1 = true) :
    C.orientedSide σ c = C.outgoing c := by
  simp [orientedSide, h]

@[simp] theorem orientedSide_of_eq_false {σ : C.Face → Bool} {c : C.Corner} (h : σ c.1 = false) :
    C.orientedSide σ c = C.graph.rev (C.outgoing c) := by
  simp [orientedSide, h]

/-- A polygonal complex is orientable when its faces can be oriented so that any two distinct
side occurrences along the same geometric edge traverse it in opposite directions. -/
def IsOrientable : Prop :=
  ∃ σ : C.Face → Bool, ∀ c c' : C.Corner, c ≠ c' →
    C.graph.toGeomEdge (C.outgoing c) = C.graph.toGeomEdge (C.outgoing c') →
      C.orientedSide σ c' = C.graph.rev (C.orientedSide σ c)

theorem isOrientable_iff : C.IsOrientable ↔ ∃ σ : C.Face → Bool, ∀ c c' : C.Corner, c ≠ c' →
    C.graph.toGeomEdge (C.outgoing c) = C.graph.toGeomEdge (C.outgoing c') →
      C.orientedSide σ c' = C.graph.rev (C.orientedSide σ c) :=
  Iff.rfl

end PolygonalComplex

end TauCeti
