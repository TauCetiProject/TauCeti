/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import TauCeti.RepresentationTheory.Quiver.Symmetrify
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Vertices, oriented edges, and backtracks in a doubled path algebra

The zigzag algebra of a simple graph `G` is a quotient of the path algebra of the doubled quiver
`TauCeti.DoubledQuiver G` by relations among the paths of length at most two. This file names those
short paths and their path-algebra elements, and computes the products among them.

A length-one path is the arrow of an adjacency, and a length-two path from a vertex back to itself
is a *backtrack*: it leaves along an edge and returns along the same edge. The two decomposition
results below show that these are the only short paths, so that the zigzag relations, which are
imposed on length-two paths, can be enumerated by adjacencies.

The last section relabels the doubled path algebra along an orientation of the graph: the
symmetrification of an oriented quiver is the doubled quiver, so their path algebras are
isomorphic, and the isomorphism carries the arrow of a selected dart to the arrow of that dart,
and the two backtracks of an oriented arrow to the backtracks at its two endpoints.

Products are computed in Tau Ceti's *later-factor-first* convention: for a path `a` from `i` to `j`
the vertex idempotents satisfy `e_j * a = a = a * e_i`, and traversing `h : G.Adj i j` and then
returning is the product `ofArrow (arrow G h.symm) * ofArrow (arrow G h)`.

## Main definitions

* `TauCeti.DoubledQuiver.arrowPath`: the length-one path along an adjacency.
* `TauCeti.DoubledQuiver.backtrackPath`: the length-two path leaving along an edge and returning.
* `TauCeti.DoubledQuiver.backtrackElem`: the path-algebra element of a backtrack.
* `TauCeti.DoubledQuiver.orientedPathAlgEquiv`: the isomorphism of path algebras attached to an
  orientation of the graph.

## Main results

* `TauCeti.DoubledQuiver.exists_eq_comp_arrowPath` and
  `TauCeti.DoubledQuiver.exists_eq_backtrackPath`: every length-two path is a composite of two
  arrows, and every length-two path returning to its source is a backtrack.
* `TauCeti.DoubledQuiver.ofArrow_symm_mul_ofArrow`: a backtrack element is the product of an arrow
  with its reverse.
* the corner identities `TauCeti.DoubledQuiver.vertexIdempotent_mul_ofArrow`,
  `TauCeti.DoubledQuiver.ofArrow_mul_vertexIdempotent`,
  `TauCeti.DoubledQuiver.vertexIdempotent_mul_backtrackElem`,
  `TauCeti.DoubledQuiver.backtrackElem_mul_vertexIdempotent`, and their vanishing counterparts.
* `TauCeti.DoubledQuiver.linearIndependent_vertexIdempotent_ofArrow_backtrackElem`: the vertex
  idempotents, the oriented-edge elements, and the backtrack elements are linearly independent.
* `TauCeti.DoubledQuiver.orientedPathAlgEquiv_ofPath` and
  `TauCeti.DoubledQuiver.orientedPathAlgEquiv_vertexIdempotent`, with their inverse counterparts:
  the relabelling on the generators of the path algebra.
* `TauCeti.DoubledQuiver.orientedPathAlgEquiv_ofArrow_of` and
  `TauCeti.DoubledQuiver.orientedPathAlgEquiv_ofArrow_reverse_of`: the relabelling reads an
  oriented arrow and its formal reverse as the two darts over the same edge.
* `TauCeti.DoubledQuiver.orientedPathAlgEquiv_headBacktrackElem` and
  `TauCeti.DoubledQuiver.orientedPathAlgEquiv_tailBacktrackElem`: the relabelling reads the two
  backtracks of an oriented arrow as the backtracks at its head and at its tail.

## References

This is the second clause of Layer 0 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks
for the paths and path-algebra elements attached to vertices, oriented edges, and backtracks
together with their source and target corner identities. See Huerfano--Khovanov, *A category for
the adjoint representation*, Section 3.
-/

public section

namespace TauCeti

namespace DoubledQuiver

open PathAlgebra

universe u w

variable {V : Type u} (G : SimpleGraph V)

/-! ### Short paths in a doubled quiver -/

/-- The length-one path of the doubled quiver along an adjacency. -/
def arrowPath {i j : V} (h : G.Adj i j) : _root_.Quiver.Path (vertex G i) (vertex G j) :=
  (arrow G h).toPath

/-- The length-one path of an adjacency is the path of its arrow. -/
theorem arrowPath_eq_toPath {i j : V} (h : G.Adj i j) :
    arrowPath G h = (arrow G h).toPath := (rfl)

@[simp]
theorem length_arrowPath {i j : V} (h : G.Adj i j) : (arrowPath G h).length = 1 := (rfl)

/-- The backtrack at `i` along an edge to `j`: the length-two path which traverses the edge and
returns along it. -/
def backtrackPath {i j : V} (h : G.Adj i j) : _root_.Quiver.Path (vertex G i) (vertex G i) :=
  (arrowPath G h).comp (arrowPath G h.symm)

/-- A backtrack is the arrow of an adjacency followed by the arrow of the symmetric adjacency. -/
theorem backtrackPath_eq_comp {i j : V} (h : G.Adj i j) :
    backtrackPath G h = (arrowPath G h).comp (arrowPath G h.symm) := (rfl)

/-- A backtrack, written as a path extended by its final arrow. -/
theorem backtrackPath_eq_cons {i j : V} (h : G.Adj i j) :
    backtrackPath G h = (arrowPath G h).cons (arrow G h.symm) := (rfl)

@[simp]
theorem length_backtrackPath {i j : V} (h : G.Adj i j) : (backtrackPath G h).length = 2 := by
  rw [backtrackPath_eq_comp, _root_.Quiver.Path.length_comp, length_arrowPath, length_arrowPath]

/-- A backtrack determines the neighbour it visits. -/
theorem eq_of_backtrackPath_eq {i j j' : V} {h : G.Adj i j} {h' : G.Adj i j'}
    (he : backtrackPath G h = backtrackPath G h') : j = j' := by
  rw [backtrackPath_eq_cons, backtrackPath_eq_cons] at he
  simpa using _root_.Quiver.Path.obj_eq_of_cons_eq_cons he

/-- Every length-one path of a doubled quiver is the arrow of an adjacency. -/
theorem exists_eq_arrowPath {i j : V} (p : _root_.Quiver.Path (vertex G i) (vertex G j))
    (hp : p.length = 1) : ∃ h : G.Adj i j, p = arrowPath G h := by
  obtain ⟨c, f, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := 0) (by simpa using hp)
  obtain rfl := q.eq_of_length_zero hq
  obtain rfl := q.eq_nil_of_length_zero hq
  refine ⟨(nonempty_hom_iff G).mp ⟨f⟩, ?_⟩
  rw [_root_.Quiver.Path.comp_nil, arrowPath_eq_toPath]
  exact congrArg _root_.Quiver.Hom.toPath (Subsingleton.elim _ _)

/-- Every length-two path of a doubled quiver traverses two adjacencies in turn. -/
theorem exists_eq_comp_arrowPath {i l : V} (p : _root_.Quiver.Path (vertex G i) (vertex G l))
    (hp : p.length = 2) :
    ∃ (j : V) (h : G.Adj i j) (h' : G.Adj j l),
      p = (arrowPath G h).comp (arrowPath G h') := by
  obtain ⟨c, f, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := 1) (by simpa using hp)
  obtain ⟨j, rfl⟩ : ∃ j, c = vertex G j :=
    ⟨(vertexEquiv G).symm c, (vertexEquiv_symm_apply G c).symm⟩
  obtain ⟨h', rfl⟩ := exists_eq_arrowPath G q hq
  refine ⟨j, (nonempty_hom_iff G).mp ⟨f⟩, h', ?_⟩
  exact congrArg (fun e : vertex G i ⟶ vertex G j =>
    (_root_.Quiver.Hom.toPath e).comp (arrowPath G h')) (Subsingleton.elim _ _)

/-- Every length-two path of a doubled quiver returning to its source is a backtrack. -/
theorem exists_eq_backtrackPath {i : V} (p : _root_.Quiver.Path (vertex G i) (vertex G i))
    (hp : p.length = 2) : ∃ (j : V) (h : G.Adj i j), p = backtrackPath G h := by
  obtain ⟨j, h, _, rfl⟩ := exists_eq_comp_arrowPath G p hp
  exact ⟨j, h, rfl⟩

/-! ### The path-algebra elements of vertices, oriented edges, and backtracks -/

section Algebra

variable (k : Type w) [CommSemiring k]

/-- The path-algebra element of the backtrack at `i` along an edge to `j`. It descends to the
volume element at `i` in the zigzag algebra, where it no longer depends on the chosen edge. -/
noncomputable def backtrackElem {i j : V} (h : G.Adj i j) : pathAlgebra k (DoubledQuiver G) :=
  ofPath ⟨vertex G i, vertex G i, backtrackPath G h⟩

/-- A backtrack element is the basis element of its backtrack path. -/
theorem backtrackElem_eq_ofPath {i j : V} (h : G.Adj i j) :
    backtrackElem G k h = ofPath ⟨vertex G i, vertex G i, backtrackPath G h⟩ := (rfl)

/-- A backtrack element is nonzero: it is a basis path of the path algebra. -/
theorem backtrackElem_ne_zero [Nontrivial k] {i j : V} (h : G.Adj i j) :
    backtrackElem G k h ≠ 0 := by
  rw [backtrackElem_eq_ofPath]
  simpa using (pathAlgebraBasis k (DoubledQuiver G)).ne_zero
    (⟨vertex G i, vertex G i, backtrackPath G h⟩ : Quiver.TotalPath (DoubledQuiver G))

/-- The vertex idempotent at the base of a backtrack is a left unit for it. -/
@[simp]
theorem vertexIdempotent_mul_backtrackElem {i j : V} (h : G.Adj i j) :
    vertexIdempotent k (vertex G i) * backtrackElem G k h = backtrackElem G k h := by
  rw [backtrackElem_eq_ofPath]
  exact vertexIdempotent_mul_ofPath _

/-- The vertex idempotent at the base of a backtrack is a right unit for it. -/
@[simp]
theorem backtrackElem_mul_vertexIdempotent {i j : V} (h : G.Adj i j) :
    backtrackElem G k h * vertexIdempotent k (vertex G i) = backtrackElem G k h := by
  rw [backtrackElem_eq_ofPath]
  exact ofPath_mul_vertexIdempotent _

/-- A vertex idempotent away from the base of a backtrack annihilates it on the left. -/
@[simp]
theorem vertexIdempotent_mul_backtrackElem_of_ne {i j v : V} (h : G.Adj i j) (hv : v ≠ i) :
    vertexIdempotent k (vertex G v) * backtrackElem G k h = 0 := by
  rw [backtrackElem_eq_ofPath]
  exact vertexIdempotent_mul_ofPath_of_ne _ (by simpa using hv)

/-- A vertex idempotent away from the base of a backtrack annihilates it on the right. -/
@[simp]
theorem backtrackElem_mul_vertexIdempotent_of_ne {i j v : V} (h : G.Adj i j) (hv : v ≠ i) :
    backtrackElem G k h * vertexIdempotent k (vertex G v) = 0 := by
  rw [backtrackElem_eq_ofPath]
  exact ofPath_mul_vertexIdempotent_of_ne _ (by simpa using hv)

/-- Backtracks based at different vertices multiply to zero. -/
@[simp]
theorem backtrackElem_mul_backtrackElem_of_ne {i j i' j' : V} (h : G.Adj i j) (h' : G.Adj i' j')
    (hne : i ≠ i') : backtrackElem G k h * backtrackElem G k h' = 0 := by
  rw [backtrackElem_eq_ofPath, backtrackElem_eq_ofPath]
  exact ofPath_mul_ofPath_of_not_composable (by simpa using hne.symm)

/-- The element of an oriented edge is the element of its length-one path. -/
theorem ofArrow_eq_ofPath_arrowPath {i j : V} (h : G.Adj i j) :
    (ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G))
      = ofPath ⟨vertex G i, vertex G j, arrowPath G h⟩ :=
  ofArrow_eq_ofPath _

/-- Two composable oriented edges multiply to the length-two path traversing the right-hand factor
first. -/
theorem ofArrow_mul_ofArrow {i j l : V} (h : G.Adj i j) (h' : G.Adj j l) :
    (ofArrow (arrow G h') * ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G))
      = ofPath ⟨vertex G i, vertex G l, (arrowPath G h).comp (arrowPath G h')⟩ := by
  rw [ofArrow_eq_ofPath_arrowPath, ofArrow_eq_ofPath_arrowPath, ofPath_mul_ofPath_of_comp]

/-- Traversing an oriented edge and returning along it is the backtrack element. -/
theorem ofArrow_symm_mul_ofArrow {i j : V} (h : G.Adj i j) :
    (ofArrow (arrow G h.symm) * ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G))
      = backtrackElem G k h := by
  rw [ofArrow_mul_ofArrow, backtrackElem_eq_ofPath, backtrackPath_eq_comp]

/-- Oriented edges that do not meet multiply to zero. -/
theorem ofArrow_mul_ofArrow_of_ne {i j a b : V} (h : G.Adj i j) (h' : G.Adj a b) (hne : a ≠ j) :
    (ofArrow (arrow G h') * ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G)) = 0 := by
  rw [ofArrow_eq_ofPath_arrowPath, ofArrow_eq_ofPath_arrowPath]
  exact ofPath_mul_ofPath_of_not_composable (by simpa using hne.symm)

/-- The vertex idempotent at the target of an oriented edge is a left unit for it. -/
theorem vertexIdempotent_mul_ofArrow {i j : V} (h : G.Adj i j) :
    vertexIdempotent k (vertex G j) * ofArrow (arrow G h)
      = (ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G)) := by
  rw [ofArrow_eq_ofPath_arrowPath]
  exact vertexIdempotent_mul_ofPath _

/-- The vertex idempotent at the source of an oriented edge is a right unit for it. -/
theorem ofArrow_mul_vertexIdempotent {i j : V} (h : G.Adj i j) :
    ofArrow (arrow G h) * vertexIdempotent k (vertex G i)
      = (ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G)) := by
  rw [ofArrow_eq_ofPath_arrowPath]
  exact ofPath_mul_vertexIdempotent _

/-- A vertex idempotent away from the target of an oriented edge annihilates it on the left. -/
theorem vertexIdempotent_mul_ofArrow_of_ne {i j v : V} (h : G.Adj i j) (hv : v ≠ j) :
    vertexIdempotent k (vertex G v) * ofArrow (arrow G h)
      = (0 : pathAlgebra k (DoubledQuiver G)) := by
  rw [ofArrow_eq_ofPath_arrowPath]
  exact vertexIdempotent_mul_ofPath_of_ne _ (by simpa using hv)

/-- A vertex idempotent away from the source of an oriented edge annihilates it on the right. -/
theorem ofArrow_mul_vertexIdempotent_of_ne {i j v : V} (h : G.Adj i j) (hv : v ≠ i) :
    ofArrow (arrow G h) * vertexIdempotent k (vertex G v)
      = (0 : pathAlgebra k (DoubledQuiver G)) := by
  rw [ofArrow_eq_ofPath_arrowPath]
  exact ofPath_mul_vertexIdempotent_of_ne _ (by simpa using hv)

end Algebra

/-! ### Linear independence of the short basis paths -/

/-- The paths indexing the vertex idempotents, the oriented-edge elements, and the backtrack
elements: the trivial path at a vertex, the arrow of a dart, and the backtrack along a dart. -/
private def shortPathIndex :
    V ⊕ G.Dart ⊕ G.Dart → Quiver.TotalPath (DoubledQuiver G)
  | .inl v => ⟨vertex G v, vertex G v, _root_.Quiver.Path.nil⟩
  | .inr (.inl d) => ⟨vertex G d.fst, vertex G d.snd, arrowPath G d.adj⟩
  | .inr (.inr d) => ⟨vertex G d.fst, vertex G d.fst, backtrackPath G d.adj⟩

private theorem shortPathIndex_injective : Function.Injective (shortPathIndex G) := by
  have hlen : ∀ x, (shortPathIndex G x).2.2.length =
      Sum.elim (fun _ : V => 0) (Sum.elim (fun _ : G.Dart => 1) fun _ : G.Dart => 2) x := by
    rintro (v | d | d) <;> simp [shortPathIndex]
  rintro x y hxy
  have hl : Sum.elim (fun _ : V => 0) (Sum.elim (fun _ : G.Dart => 1) fun _ : G.Dart => 2) x
      = Sum.elim (fun _ : V => 0) (Sum.elim (fun _ : G.Dart => 1) fun _ : G.Dart => 2) y := by
    rw [← hlen x, ← hlen y, hxy]
  -- The three blocks have paths of lengths `0`, `1` and `2`, so `hl` rules out mixed pairs; the
  -- three remaining cases compare endpoints of equal paths.
  rcases x with v | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩ <;>
    rcases y with v' | ⟨⟨a', b'⟩, ha'b'⟩ | ⟨⟨a', b'⟩, ha'b'⟩ <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hl
  · simp only [shortPathIndex] at hxy
    simpa using congrArg Sigma.fst hxy
  · simp at hl
  · simp at hl
  · simp at hl
  · simp only [shortPathIndex] at hxy
    have h1 : a = a' := by simpa using congrArg Sigma.fst hxy
    have h2 : b = b' := by
      simpa using congrArg (fun z : Quiver.TotalPath (DoubledQuiver G) => z.2.1) hxy
    subst h1
    subst h2
    rfl
  · simp at hl
  · simp at hl
  · simp at hl
  · simp only [shortPathIndex] at hxy
    have h1 : a = a' := by simpa using congrArg Sigma.fst hxy
    subst h1
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hxy
    have h2 : b = b' := eq_of_backtrackPath_eq G hxy
    subst h2
    rfl

/-- The vertex idempotents, the oriented-edge elements, and the backtrack elements are linearly
independent in the path algebra of a doubled quiver: they are distinct basis paths, of lengths
`0`, `1`, and `2` respectively. -/
theorem linearIndependent_vertexIdempotent_ofArrow_backtrackElem
    (k : Type w) [CommSemiring k] :
    LinearIndependent k
      (Sum.elim (fun v : V => (vertexIdempotent k (vertex G v) : pathAlgebra k (DoubledQuiver G)))
        (Sum.elim (fun d : G.Dart => (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G)))
          fun d : G.Dart => backtrackElem G k d.adj)) := by
  have hfam :
      Sum.elim (fun v : V => (vertexIdempotent k (vertex G v) : pathAlgebra k (DoubledQuiver G)))
          (Sum.elim (fun d : G.Dart => (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G)))
            fun d : G.Dart => backtrackElem G k d.adj)
        = ⇑(pathAlgebraBasis k (DoubledQuiver G)) ∘ shortPathIndex G := by
    funext x
    rcases x with v | d | d <;>
      simp [shortPathIndex, vertexIdempotent_eq_single, ofPath_eq_single, arrowPath_eq_toPath,
        backtrackElem_eq_ofPath]
  rw [hfam]
  exact (pathAlgebraBasis k (DoubledQuiver G)).linearIndependent.comp _
    (shortPathIndex_injective G)

/-! ### The path algebra of an orientation -/

section Orientation

variable (k : Type w) [CommSemiring k] [Finite V] {G} (o : Orientation G)

/-- **The isomorphism of path algebras attached to an orientation of a simple graph**: the
symmetrification of the oriented quiver of `o` is the doubled quiver of `G`, so the two path
algebras are relabellings of one another. -/
noncomputable def orientedPathAlgEquiv :
    pathAlgebra k (_root_.Quiver.Symmetrify (OrientedQuiver G o)) ≃ₐ[k]
      pathAlgebra k (DoubledQuiver G) :=
  PathAlgebra.mapAlgEquiv k (symmetrifyMap G o) (unsymmetrifyMap G o)
    (symmetrifyMap_comp_unsymmetrifyMap G o) (unsymmetrifyMap_comp_symmetrifyMap G o)

/-- The relabelling sends the basis element of a path of the symmetrified oriented quiver to the
basis element of the relabelled path of the doubled quiver. -/
@[simp]
theorem orientedPathAlgEquiv_ofPath
    (x : Quiver.TotalPath (_root_.Quiver.Symmetrify (OrientedQuiver G o))) :
    orientedPathAlgEquiv k o (ofPath x) = ofPath ((symmetrifyMap G o).mapTotalPath x) := by
  rw [orientedPathAlgEquiv, PathAlgebra.mapAlgEquiv_apply, PathAlgebra.mapAlgHom_ofPath]

/-- The inverse relabelling sends the basis element of a path of the doubled quiver to the basis
element of the relabelled path of the symmetrified oriented quiver. -/
@[simp]
theorem orientedPathAlgEquiv_symm_ofPath (x : Quiver.TotalPath (DoubledQuiver G)) :
    (orientedPathAlgEquiv k o).symm (ofPath x) = ofPath ((unsymmetrifyMap G o).mapTotalPath x) := by
  rw [orientedPathAlgEquiv, PathAlgebra.mapAlgEquiv_symm_apply, PathAlgebra.mapAlgHom_ofPath]

/-- The inverse relabelling carries the idempotent of a vertex of the doubled quiver to the
idempotent of the same vertex of the oriented quiver. The two vertex types are definitionally
equal, so the symmetrified quiver structure is named explicitly to keep it from being replaced by
that of the oriented quiver. -/
@[simp]
theorem orientedPathAlgEquiv_symm_vertexIdempotent (i : V) :
    (orientedPathAlgEquiv k o).symm (vertexIdempotent k (vertex G i))
      = @vertexIdempotent k (_root_.Quiver.Symmetrify (OrientedQuiver G o)) _
          (_root_.Quiver.symmetrifyQuiver _) (OrientedQuiver.vertex G o i) := by
  rw [orientedPathAlgEquiv, PathAlgebra.mapAlgEquiv_symm_apply,
    PathAlgebra.mapAlgHom_vertexIdempotent, unsymmetrifyMap_obj]

/-- The relabelling carries the idempotent of a vertex of the oriented quiver to the idempotent of
the same vertex of the doubled quiver, with the symmetrified quiver structure named explicitly as
above. -/
@[simp]
theorem orientedPathAlgEquiv_vertexIdempotent (i : V) :
    orientedPathAlgEquiv k o
        (@vertexIdempotent k (_root_.Quiver.Symmetrify (OrientedQuiver G o)) _
          (_root_.Quiver.symmetrifyQuiver _) (OrientedQuiver.vertex G o i))
      = vertexIdempotent k (vertex G i) := by
  rw [← orientedPathAlgEquiv_symm_vertexIdempotent k o i, AlgEquiv.apply_symm_apply]

/-- The relabelling sends the element of an arrow to the element of its image arrow. Deliberately
not a `simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewrites its left-hand side,
and `simpNF` rejects the pair. -/
theorem orientedPathAlgEquiv_ofArrow {x y : _root_.Quiver.Symmetrify (OrientedQuiver G o)}
    (e : x ⟶ y) :
    orientedPathAlgEquiv k o (ofArrow e) = ofArrow ((symmetrifyMap G o).map e) := by
  rw [orientedPathAlgEquiv, PathAlgebra.mapAlgEquiv_apply, PathAlgebra.mapAlgHom_ofArrow]

/-- The relabelling sends the arrow of a dart selected by the orientation to the doubled-quiver
arrow of that dart. -/
theorem orientedPathAlgEquiv_ofArrow_of {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o
        (ofArrow (_root_.Quiver.Symmetrify.of.map (OrientedQuiver.arrow G o h ho)))
      = ofArrow (arrow G h) := by
  have hmap : (symmetrifyMap G o).map
      (_root_.Quiver.Symmetrify.of.map (OrientedQuiver.arrow G o h ho))
      = _root_.Quiver.homOfEq (arrow G h) (symmetrifyMap_obj G o i).symm
          (symmetrifyMap_obj G o j).symm := Subsingleton.elim _ _
  rw [orientedPathAlgEquiv_ofArrow, hmap]
  exact ofArrow_homOfEq _ _ _

/-- The relabelling sends the formal reverse of the arrow of a selected dart to the doubled-quiver
arrow of the reversed dart. -/
theorem orientedPathAlgEquiv_ofArrow_reverse_of {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o
        (ofArrow (_root_.Quiver.reverse
          (_root_.Quiver.Symmetrify.of.map (OrientedQuiver.arrow G o h ho))))
      = ofArrow (arrow G h.symm) := by
  have hmap : (symmetrifyMap G o).map
      (_root_.Quiver.reverse (_root_.Quiver.Symmetrify.of.map (OrientedQuiver.arrow G o h ho)))
        = _root_.Quiver.homOfEq (arrow G h.symm) (symmetrifyMap_obj G o j).symm
            (symmetrifyMap_obj G o i).symm := Subsingleton.elim _ _
  rw [orientedPathAlgEquiv_ofArrow, hmap]
  exact ofArrow_homOfEq _ _ _

/-- **The head backtrack of an oriented arrow is the backtrack at its head.** The arrow
`a : i ⟶ j` of the orientation traverses the edge `ij`; the word `a a*` leaves `j` along that edge
and returns, so it becomes the backtrack at `j`. -/
theorem orientedPathAlgEquiv_headBacktrackElem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o (headBacktrackElem k (OrientedQuiver.arrow G o h ho))
      = backtrackElem G k h.symm := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem, map_mul,
    orientedPathAlgEquiv_ofArrow_of k o h ho, orientedPathAlgEquiv_ofArrow_reverse_of k o h ho]
  exact ofArrow_symm_mul_ofArrow G k h.symm

/-- **The tail backtrack of an oriented arrow is the backtrack at its tail.** The word `a* a`
leaves the tail `i` of `a : i ⟶ j` along the edge `ij` and returns. -/
theorem orientedPathAlgEquiv_tailBacktrackElem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o (tailBacktrackElem k (OrientedQuiver.arrow G o h ho))
      = backtrackElem G k h := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_mul,
    orientedPathAlgEquiv_ofArrow_reverse_of k o h ho, orientedPathAlgEquiv_ofArrow_of k o h ho]
  exact ofArrow_symm_mul_ofArrow G k h

end Orientation

end DoubledQuiver

end TauCeti
