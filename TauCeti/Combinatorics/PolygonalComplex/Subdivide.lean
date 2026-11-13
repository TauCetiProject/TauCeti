/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Subdivide
public import TauCeti.Combinatorics.PolygonalComplex.Examples
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Fin

/-!
# Subdividing an edge of a polygonal complex

Subdividing the geometric edge of a dart `a` of a polygonal complex inserts a new vertex in the
middle of that edge and replaces, along every face, each side attached along `a` by two
consecutive sides attached along the two halves of `a`, and each side attached along the reverse
of `a` by the two reversed halves in the opposite order. This is the first of the two elementary
subdivisions of Gallier and Xu, the operation (P1) replacing `a` and `a⁻¹` by `b c` and
`c⁻¹ b⁻¹` in all boundaries.

The one-skeleton of `C.subdivide a` is `C.graph.subdivide a`, and its faces are those of `C`.
Every corner `c` of `C` gives a first corner `C.subdivideFirstCorner a c` and a last corner
`C.subdivideLastCorner a c` of the subdivision: the starts of the first and of the last of the
sides replacing the side of `c`. They coincide unless the side of `c` is attached along `a` or
its reverse, and every corner of the subdivision is the first or the last corner of the corner
`C.subdivideOriginCorner a c` of `C` on whose side it lies.

The move does not change the surface. The link of an old vertex is unchanged: the subdivision
maps it isomorphically onto the new link, and its germs keep their degrees. The link of the new
vertex has two germs, joined by one corner for every side attached along the subdivided edge. So
a surface model stays a surface model (`SurfaceModel.subdivide`), with the same Euler
characteristic, the same orientability and the corresponding boundary darts. Subdividing an edge
of the torus gives again a closed orientable model with Euler characteristic `0`.

## Main definitions

* `TauCeti.PolygonalComplex.subdivide`: the complex obtained by subdividing an edge.
* `TauCeti.PolygonalComplex.subdivideFirstCorner`, `TauCeti.PolygonalComplex.subdivideLastCorner`,
  `TauCeti.PolygonalComplex.subdivideOriginCorner`: the correspondence of corners.
* `TauCeti.PolygonalComplex.subdivideLinkHom`: the map from the link of a vertex to its link in
  the subdivision.
* `TauCeti.SurfaceModel.subdivide`: the surface model obtained by subdividing an edge.

## Main results

* `TauCeti.PolygonalComplex.ofFn_subdivideSide`: the word along a subdivided face.
* `TauCeti.PolygonalComplex.sideCount_subdivide`, `TauCeti.PolygonalComplex.linkDegree_subdivide`:
  the side counts and link degrees of the subdivision.
* `TauCeti.PolygonalComplex.subdivideLinkHom_mapV_bijective`,
  `TauCeti.PolygonalComplex.subdivideLinkHom_mapE_bijective`: the link of an old vertex is
  unchanged.
* `TauCeti.PolygonalComplex.hasSurfaceLink_subdivide_some_iff`,
  `TauCeti.PolygonalComplex.hasSurfaceLink_subdivide_none_iff`: the surface-link condition at the
  old vertices and at the new vertex.
* `TauCeti.PolygonalComplex.eulerChar_subdivide`: the Euler characteristic is unchanged.
* `TauCeti.PolygonalComplex.isOrientable_subdivide_iff`: orientability is unchanged.
* `TauCeti.SurfaceModel.boundaryDarts_subdivide`: the boundary darts of the subdivision.
* `TauCeti.SurfaceModel.eulerChar_torus_subdivide`,
  `TauCeti.SurfaceModel.linkDegree_torus_subdivide_inr`,
  `TauCeti.SurfaceModel.isOrientable_torus_subdivide`: a subdivided torus has Euler characteristic
  `0`, a circle link at its new vertex, and is orientable.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P1).
* H. Seifert, W. Threlfall, *A Textbook of Topology*, Academic Press, 1980, Chapter VI, §37.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w}) [DecidableEq C.graph.E] (a : C.graph.E)

/-! ### The subdivided complex -/

/-- The number of sides replacing a face side attached along `e`: two when `e` is `a` or its
reverse, and one otherwise. -/
private def subdivideLen (e : C.graph.E) : ℕ := if e = a ∨ e = C.graph.rev a then 2 else 1

private theorem subdivideLen_of_eq_or_eq {e : C.graph.E} (h : e = a ∨ e = C.graph.rev a) :
    C.subdivideLen a e = 2 := by
  simp [subdivideLen, h]

private theorem subdivideLen_of_not {e : C.graph.E} (h : ¬(e = a ∨ e = C.graph.rev a)) :
    C.subdivideLen a e = 1 := by
  simp [subdivideLen, h]

private theorem subdivideLen_pos (e : C.graph.E) : 0 < C.subdivideLen a e := by
  by_cases h : e = a ∨ e = C.graph.rev a
  · simp [C.subdivideLen_of_eq_or_eq a h]
  · simp [C.subdivideLen_of_not a h]

/-- The number of sides of the face `f` once the edge of `a` is subdivided: each side of `f`
attached along `a` or its reverse counts twice. -/
def subdivideSides (f : C.Face) : ℕ := ∑ i : Fin (C.sides f), C.subdivideLen a (C.side f i)

/-- The dart of the `x.2`-th of the sides replacing the `x.1`-th side of `f`. -/
private def subdivideBlock (f : C.Face)
    (x : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i))) : (C.graph.subdivide a).E :=
  if (x.2 : ℕ) = 0 then .inl (C.side f x.1) else C.graph.subdivideLast a (C.side f x.1)

/-- The darts along which the sides of the face `f` are attached once the edge of `a` is
subdivided: each side of `f` attached along a dart `e` is replaced by the path replacing `e`. -/
def subdivideSide (f : C.Face) (k : Fin (C.subdivideSides a f)) : (C.graph.subdivide a).E :=
  C.subdivideBlock a f (finSigmaFinEquiv.symm k)

/-- The number of sides of a subdivided face is the number of its sides plus the number of its
sides attached along the subdivided edge. -/
theorem subdivideSides_eq (f : C.Face) :
    C.subdivideSides a f = C.sides f +
      (Finset.univ.filter fun i => C.side f i = a ∨ C.side f i = C.graph.rev a).card := by
  have h : ∀ i, C.subdivideLen a (C.side f i) =
      1 + if C.side f i = a ∨ C.side f i = C.graph.rev a then 1 else 0 := fun i => by
    unfold subdivideLen
    split_ifs <;> rfl
  simp [subdivideSides, h, Finset.sum_add_distrib]

private theorem subdivideSide_apply (f : C.Face)
    (x : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i))) :
    C.subdivideSide a f (finSigmaFinEquiv x) = C.subdivideBlock a f x :=
  congrArg (C.subdivideBlock a f) (Equiv.symm_apply_apply _ x)

private theorem subdivideBlock_zero (f : C.Face) (i : Fin (C.sides f))
    (j : Fin (C.subdivideLen a (C.side f i))) (hj : (j : ℕ) = 0) :
    C.subdivideBlock a f ⟨i, j⟩ = .inl (C.side f i) := by
  simp [subdivideBlock, hj]

/-- The last of the sides replacing a side is attached along the last dart of the path replacing
its dart. -/
private theorem subdivideBlock_of_add_one_eq (f : C.Face) (i : Fin (C.sides f))
    (j : Fin (C.subdivideLen a (C.side f i))) (hj : (j : ℕ) + 1 = C.subdivideLen a (C.side f i)) :
    C.subdivideBlock a f ⟨i, j⟩ = C.graph.subdivideLast a (C.side f i) := by
  by_cases h : C.side f i = a ∨ C.side f i = C.graph.rev a
  · have := C.subdivideLen_of_eq_or_eq a h
    simp [subdivideBlock, show (j : ℕ) ≠ 0 by omega]
  · have := C.subdivideLen_of_not a h
    rw [not_or] at h
    simp [subdivideBlock, show (j : ℕ) = 0 by omega, SerreGraph.subdivideLast_of_ne h.1 h.2]

/-- The word along a face of the subdivision: each letter `e` of the word along that face in `C`
is replaced by the path replacing `e`, which has a second letter when `e` is `a` or its reverse. -/
theorem ofFn_subdivideSide (f : C.Face) :
    List.ofFn (C.subdivideSide a f) = (List.ofFn (C.side f)).flatMap fun e =>
      if e = a ∨ e = C.graph.rev a then [.inl e, C.graph.subdivideLast a e] else [.inl e] := by
  refine (List.ofFn_sum (m := fun i => C.subdivideLen a (C.side f i)) _).trans ?_
  rw [List.flatMap_def, List.map_ofFn]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  simp only [subdivideSide_apply, subdivideBlock]
  by_cases h : C.side f i = a ∨ C.side f i = C.graph.rev a
  · simp [subdivideLen, h, List.ofFn_succ]
  · simp [subdivideLen, h]

private theorem finRotate_subdivideSides_of_lt (f : C.Face) (i : Fin (C.sides f))
    (j : Fin (C.subdivideLen a (C.side f i))) (hj : (j : ℕ) + 1 < C.subdivideLen a (C.side f i)) :
    finRotate (C.subdivideSides a f) (finSigmaFinEquiv ⟨i, j⟩) =
      finSigmaFinEquiv ⟨i, ⟨j + 1, hj⟩⟩ :=
  Fin.finRotate_finSigmaFinEquiv_of_lt (m := fun i => C.subdivideLen a (C.side f i)) i j hj

private theorem finRotate_subdivideSides_of_eq (f : C.Face) (i : Fin (C.sides f))
    (j : Fin (C.subdivideLen a (C.side f i))) (hj : (j : ℕ) + 1 = C.subdivideLen a (C.side f i)) :
    finRotate (C.subdivideSides a f) (finSigmaFinEquiv ⟨i, j⟩) =
      finSigmaFinEquiv ⟨finRotate _ i, ⟨0, C.subdivideLen_pos a _⟩⟩ :=
  Fin.finRotate_finSigmaFinEquiv_of_eq (m := fun i => C.subdivideLen a (C.side f i)) i j hj _ rfl

/-- The sides of a subdivided face form a closed dart sequence. -/
theorem tgt_subdivideSide (f : C.Face) (k : Fin (C.subdivideSides a f)) :
    (C.graph.subdivide a).tgt (C.subdivideSide a f k) =
      (C.graph.subdivide a).src (C.subdivideSide a f (finRotate _ k)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (finSigmaFinEquiv
    (n := fun i => C.subdivideLen a (C.side f i))).surjective k
  by_cases hj : (j : ℕ) + 1 < C.subdivideLen a (C.side f i)
  · have h : C.side f i = a ∨ C.side f i = C.graph.rev a := by
      by_contra h
      have := C.subdivideLen_of_not a h
      omega
    have hlen := C.subdivideLen_of_eq_or_eq a h
    rw [finRotate_subdivideSides_of_lt _ _ _ _ _ hj, subdivideSide_apply, subdivideSide_apply,
      subdivideBlock_zero _ _ _ _ _ (by omega),
      subdivideBlock_of_add_one_eq _ _ _ _ _ (by simp only; omega),
      SerreGraph.subdivide_tgt_inl_of_eq_or_eq a h, SerreGraph.subdivideLast_of_eq_or_eq h,
      SerreGraph.subdivide_src_inr]
  · have hj' : (j : ℕ) + 1 = C.subdivideLen a (C.side f i) := by
      have := j.is_lt
      omega
    rw [finRotate_subdivideSides_of_eq _ _ _ _ _ hj', subdivideSide_apply, subdivideSide_apply,
      subdivideBlock_of_add_one_eq _ _ _ _ _ hj', subdivideBlock_zero _ _ _ _ _ rfl,
      SerreGraph.subdivide_tgt_subdivideLast, SerreGraph.subdivide_src_inl, C.tgt_side]

/-- The polygonal complex obtained from `C` by subdividing the geometric edge of the dart `a`.
Its one-skeleton is `C.graph.subdivide a` and its faces are those of `C`; along every face, each
side attached along `a` is replaced by two sides attached along the two halves of `a`, and each
side attached along the reverse of `a` by two sides attached along the reversed halves. It is
reducible, so that its one-skeleton and its faces are seen to be these. -/
abbrev subdivide : PolygonalComplex.{u, v, w} where
  graph := C.graph.subdivide a
  Face := C.Face
  sides := C.subdivideSides a
  sides_pos f := (C.sides_pos f).trans_le (by rw [subdivideSides_eq]; exact Nat.le_add_right _ _)
  side := C.subdivideSide a
  tgt_side := C.tgt_subdivideSide a

/-! ### Corners of the subdivided complex -/

/-- The corner of the subdivision at the start of the `x.2`-th of the sides replacing the
`x.1`-th side of `f`. -/
private def subdivideCorner (f : C.Face)
    (x : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i))) : (C.subdivide a).Corner :=
  ⟨f, finSigmaFinEquiv x⟩

/-- The first corner of the subdivision on the side of the corner `c`: it sits at the vertex of
`c`, at the start of the first of the sides replacing the side of `c`. -/
def subdivideFirstCorner (c : C.Corner) : (C.subdivide a).Corner :=
  C.subdivideCorner a c.1 ⟨c.2, ⟨0, C.subdivideLen_pos a _⟩⟩

/-- The last corner of the subdivision on the side of the corner `c`: it sits at the start of the
last of the sides replacing the side of `c`. This is the new vertex when that side is attached
along `a` or its reverse, and otherwise it is the first corner. -/
def subdivideLastCorner (c : C.Corner) : (C.subdivide a).Corner :=
  C.subdivideCorner a c.1
    ⟨c.2, ⟨C.subdivideLen a (C.side c.1 c.2) - 1, Nat.sub_lt (C.subdivideLen_pos a _) one_pos⟩⟩

/-- The corner of `C` on whose side a corner of the subdivision lies. -/
def subdivideOriginCorner (c : (C.subdivide a).Corner) : C.Corner :=
  ⟨c.1, (finSigmaFinEquiv (n := fun i => C.subdivideLen a (C.side c.1 i)).symm c.2).1⟩

private theorem subdivideOriginCorner_subdivideCorner (f : C.Face)
    (x : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i))) :
    C.subdivideOriginCorner a (C.subdivideCorner a f x) = ⟨f, x.1⟩ :=
  congrArg (fun y : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i)) =>
    (⟨f, y.1⟩ : C.Corner)) (Equiv.symm_apply_apply _ x)

private theorem exists_eq_subdivideCorner (c : (C.subdivide a).Corner) :
    ∃ x, c = C.subdivideCorner a c.1 x := by
  obtain ⟨f, k⟩ := c
  obtain ⟨x, rfl⟩ := (finSigmaFinEquiv
    (n := fun i => C.subdivideLen a (C.side f i))).surjective k
  exact ⟨x, rfl⟩

private theorem outgoing_subdivideCorner (f : C.Face)
    (x : (i : Fin (C.sides f)) × Fin (C.subdivideLen a (C.side f i))) :
    (C.subdivide a).outgoing (C.subdivideCorner a f x) = C.subdivideBlock a f x :=
  (outgoing_def _ _).trans (C.subdivideSide_apply a f x)

@[simp] theorem subdivideFirstCorner_fst (c : C.Corner) : (C.subdivideFirstCorner a c).1 = c.1 :=
  (rfl)

@[simp] theorem subdivideLastCorner_fst (c : C.Corner) : (C.subdivideLastCorner a c).1 = c.1 :=
  (rfl)

@[simp] theorem subdivideOriginCorner_fst (c : (C.subdivide a).Corner) :
    (C.subdivideOriginCorner a c).1 = c.1 := (rfl)

-- Not `@[simp]`: `simp` would rewrite `C.subdivideFirstCorner a ⟨f, ⟨0, h⟩⟩` to a corner on which
-- the simp lemmas `outgoing_subdivideFirstCorner`, `prevCorner_subdivideFirstCorner`, ... no
-- longer fire.
/-- The corner `0` of a face of `C` gives the corner `0` of that face in the subdivision. -/
theorem subdivideFirstCorner_zero (f : C.Face) (h : 0 < C.sides f) :
    C.subdivideFirstCorner a ⟨f, ⟨0, h⟩⟩ = ⟨f, ⟨0, (C.subdivide a).sides_pos f⟩⟩ :=
  Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [subdivideFirstCorner, subdivideCorner])))

@[simp] theorem subdivideOriginCorner_subdivideFirstCorner (c : C.Corner) :
    C.subdivideOriginCorner a (C.subdivideFirstCorner a c) = c :=
  C.subdivideOriginCorner_subdivideCorner a _ _

@[simp] theorem subdivideOriginCorner_subdivideLastCorner (c : C.Corner) :
    C.subdivideOriginCorner a (C.subdivideLastCorner a c) = c :=
  C.subdivideOriginCorner_subdivideCorner a _ _

theorem subdivideFirstCorner_injective : Function.Injective (C.subdivideFirstCorner a) :=
  Function.LeftInverse.injective (C.subdivideOriginCorner_subdivideFirstCorner a)

theorem subdivideLastCorner_injective : Function.Injective (C.subdivideLastCorner a) :=
  Function.LeftInverse.injective (C.subdivideOriginCorner_subdivideLastCorner a)

variable {C a} in
/-- The first and the last corner on a side not attached along the subdivided edge coincide. -/
theorem subdivideLastCorner_eq_subdivideFirstCorner_of_ne {c : C.Corner} (h : C.outgoing c ≠ a)
    (h' : C.outgoing c ≠ C.graph.rev a) :
    C.subdivideLastCorner a c = C.subdivideFirstCorner a c := by
  rw [outgoing_def] at h h'
  simp [subdivideLastCorner, subdivideFirstCorner, C.subdivideLen_of_not a (not_or.2 ⟨h, h'⟩)]

/-- Every corner of the subdivision is the first or the last corner on the side on which it
lies. -/
theorem eq_subdivideFirstCorner_or_eq_subdivideLastCorner (c : (C.subdivide a).Corner) :
    c = C.subdivideFirstCorner a (C.subdivideOriginCorner a c) ∨
      c = C.subdivideLastCorner a (C.subdivideOriginCorner a c) := by
  obtain ⟨⟨i, j⟩, hc⟩ := C.exists_eq_subdivideCorner a c
  have hj := j.is_lt
  have ho : C.subdivideOriginCorner a c = ⟨c.1, i⟩ :=
    (congrArg _ hc).trans (C.subdivideOriginCorner_subdivideCorner a _ _)
  rw [ho]
  by_cases h0 : (j : ℕ) = 0
  · exact .inl (hc.trans (congrArg (fun j => C.subdivideCorner a c.1 ⟨i, j⟩) (Fin.ext h0)))
  · refine .inr (hc.trans (congrArg (fun j => C.subdivideCorner a c.1 ⟨i, j⟩) (Fin.ext ?_)))
    by_cases h : C.side c.1 i = a ∨ C.side c.1 i = C.graph.rev a
    · have := C.subdivideLen_of_eq_or_eq a h
      simp only
      omega
    · have := C.subdivideLen_of_not a h
      omega

/-- The side starting at the first corner on the side of `c` is attached along the initial half
of the dart of `c`. -/
@[simp] theorem outgoing_subdivideFirstCorner (c : C.Corner) :
    (C.subdivide a).outgoing (C.subdivideFirstCorner a c) = .inl (C.outgoing c) := by
  rw [C.outgoing_def]
  exact (C.outgoing_subdivideCorner a _ _).trans
    (C.subdivideBlock_zero a c.1 c.2 ⟨0, C.subdivideLen_pos a _⟩ rfl)

/-- The side starting at the last corner on the side of `c` is attached along the last dart of
the path replacing the dart of `c`. -/
@[simp] theorem outgoing_subdivideLastCorner (c : C.Corner) :
    (C.subdivide a).outgoing (C.subdivideLastCorner a c) =
      C.graph.subdivideLast a (C.outgoing c) := by
  rw [C.outgoing_def]
  exact (C.outgoing_subdivideCorner a _ _).trans
    (C.subdivideBlock_of_add_one_eq a c.1 c.2
      ⟨C.subdivideLen a (C.side c.1 c.2) - 1, Nat.sub_lt (C.subdivideLen_pos a _) one_pos⟩
      (Nat.sub_add_cancel (C.subdivideLen_pos a _)))

/-- A side of the subdivision lies on the side of the corner of `C` on whose side it starts. -/
@[simp] theorem subdivideOrigin_outgoing (c : (C.subdivide a).Corner) :
    C.graph.subdivideOrigin a ((C.subdivide a).outgoing c) =
      C.outgoing (C.subdivideOriginCorner a c) := by
  rcases C.eq_subdivideFirstCorner_or_eq_subdivideLastCorner a c with h | h <;>
    · conv_lhs => rw [h]
      simp

variable {C a} in
/-- A corner of the subdivision whose side is attached along an initial half is a first
corner. -/
theorem eq_subdivideFirstCorner_of_outgoing_eq_inl {c : (C.subdivide a).Corner} {e : C.graph.E}
    (h : (C.subdivide a).outgoing c = .inl e) :
    c = C.subdivideFirstCorner a (C.subdivideOriginCorner a c) := by
  rcases C.eq_subdivideFirstCorner_or_eq_subdivideLastCorner a c with hc | hc
  · exact hc
  · by_cases hc' : C.outgoing (C.subdivideOriginCorner a c) = a ∨
        C.outgoing (C.subdivideOriginCorner a c) = C.graph.rev a
    · rw [hc, outgoing_subdivideLastCorner, SerreGraph.subdivideLast_of_eq_or_eq hc'] at h
      exact absurd h (by simp)
    · obtain ⟨h₁, h₂⟩ := not_or.1 hc'
      exact hc.trans (subdivideLastCorner_eq_subdivideFirstCorner_of_ne h₁ h₂)

variable {C a} in
/-- A corner of the subdivision whose side starts at the new vertex is a last corner. -/
theorem eq_subdivideLastCorner_of_outgoing_eq_inr {c : (C.subdivide a).Corner} {b : Bool}
    (h : (C.subdivide a).outgoing c = .inr b) :
    c = C.subdivideLastCorner a (C.subdivideOriginCorner a c) := by
  rcases C.eq_subdivideFirstCorner_or_eq_subdivideLastCorner a c with hc | hc
  · rw [hc, outgoing_subdivideFirstCorner] at h
    exact absurd h (by simp)
  · exact hc

variable {C a} in
/-- A corner of the subdivision is determined by the side of `C` on which it lies and by the dart
of its side. -/
theorem eq_of_subdivideOriginCorner_eq_of_outgoing_eq {c c' : (C.subdivide a).Corner}
    (h : C.subdivideOriginCorner a c = C.subdivideOriginCorner a c')
    (h' : (C.subdivide a).outgoing c = (C.subdivide a).outgoing c') : c = c' := by
  rcases hc : (C.subdivide a).outgoing c with e | b
  · exact (eq_subdivideFirstCorner_of_outgoing_eq_inl hc).trans <| (congrArg _ h).trans
      (eq_subdivideFirstCorner_of_outgoing_eq_inl (h' ▸ hc)).symm
  · exact (eq_subdivideLastCorner_of_outgoing_eq_inr hc).trans <| (congrArg _ h).trans
      (eq_subdivideLastCorner_of_outgoing_eq_inr (h' ▸ hc)).symm

/-- The corner following the last corner on a side is the first corner on the next side. -/
@[simp] theorem nextCorner_subdivideLastCorner (c : C.Corner) :
    (C.subdivide a).nextCorner (C.subdivideLastCorner a c) =
      C.subdivideFirstCorner a (C.nextCorner c) := by
  rw [nextCorner_def, nextCorner_def]
  exact congrArg (Sigma.mk c.1) (C.finRotate_subdivideSides_of_eq a _ _ _
    (Nat.sub_add_cancel (C.subdivideLen_pos a _)))

/-- The corner preceding the first corner on a side is the last corner on the previous side. -/
@[simp] theorem prevCorner_subdivideFirstCorner (c : C.Corner) :
    (C.subdivide a).prevCorner (C.subdivideFirstCorner a c) =
      C.subdivideLastCorner a (C.prevCorner c) := by
  rw [← (C.subdivide a).prevCorner_nextCorner (C.subdivideLastCorner a _),
    nextCorner_subdivideLastCorner, nextCorner_prevCorner]

variable {C a} in
/-- On a side attached along the subdivided edge, the corner following the first corner is the
last corner. -/
theorem nextCorner_subdivideFirstCorner_of_eq_or_eq {c : C.Corner}
    (h : C.outgoing c = a ∨ C.outgoing c = C.graph.rev a) :
    (C.subdivide a).nextCorner (C.subdivideFirstCorner a c) = C.subdivideLastCorner a c := by
  rw [outgoing_def] at h
  have hlen := C.subdivideLen_of_eq_or_eq a h
  refine (((C.subdivide a).nextCorner_def _).trans (congrArg (Sigma.mk c.1)
    (C.finRotate_subdivideSides_of_lt a c.1 c.2 ⟨0, C.subdivideLen_pos a _⟩
      (by simp only [hlen]; omega)))).trans ?_
  exact congrArg (fun j => C.subdivideCorner a c.1 ⟨c.2, j⟩) (Fin.ext (by simp only; omega))

/-- The side ending at the first corner on the side of `c` is attached along the last dart of the
path replacing the incoming dart of `c`. -/
@[simp] theorem incoming_subdivideFirstCorner (c : C.Corner) :
    (C.subdivide a).incoming (C.subdivideFirstCorner a c) =
      C.graph.subdivideLast a (C.incoming c) := by
  rw [← C.nextCorner_prevCorner c, ← nextCorner_subdivideLastCorner, incoming_nextCorner,
    outgoing_subdivideLastCorner, incoming_nextCorner]

variable {C a} in
/-- On a side attached along the subdivided edge, the side ending at the last corner is attached
along the initial half of its dart. -/
theorem incoming_subdivideLastCorner_of_eq_or_eq {c : C.Corner}
    (h : C.outgoing c = a ∨ C.outgoing c = C.graph.rev a) :
    (C.subdivide a).incoming (C.subdivideLastCorner a c) = .inl (C.outgoing c) := by
  rw [← nextCorner_subdivideFirstCorner_of_eq_or_eq h, incoming_nextCorner,
    outgoing_subdivideFirstCorner]

/-- The first corner on the side of `c` sits at the vertex of `c`. -/
@[simp] theorem cornerVertex_subdivideFirstCorner (c : C.Corner) :
    (C.subdivide a).cornerVertex (C.subdivideFirstCorner a c) = some (C.cornerVertex c) := by
  rw [← src_outgoing, outgoing_subdivideFirstCorner, SerreGraph.subdivide_src_inl, src_outgoing]

variable {C a} in
/-- On a side attached along the subdivided edge, the last corner sits at the new vertex. -/
theorem cornerVertex_subdivideLastCorner_of_eq_or_eq {c : C.Corner}
    (h : C.outgoing c = a ∨ C.outgoing c = C.graph.rev a) :
    (C.subdivide a).cornerVertex (C.subdivideLastCorner a c) = none := by
  rw [← src_outgoing, outgoing_subdivideLastCorner, SerreGraph.subdivideLast_of_eq_or_eq h,
    SerreGraph.subdivide_src_inr]

/-! ### Side counts and link degrees -/

/-- The sides of the subdivision attached along the initial half of `e` are the first sides
replacing the sides of `C` attached along `e`. -/
private def subdivideSideInlEquiv (e : C.graph.E) :
    {c : (C.subdivide a).Corner // (C.subdivide a).outgoing c = .inl e} ≃
      {c : C.Corner // C.outgoing c = e} where
  toFun c := ⟨C.subdivideOriginCorner a c.1, by
    rw [← subdivideOrigin_outgoing, c.2, SerreGraph.subdivideOrigin_inl]⟩
  invFun c := ⟨C.subdivideFirstCorner a c.1, by rw [outgoing_subdivideFirstCorner, c.2]⟩
  left_inv c := Subtype.ext (eq_subdivideFirstCorner_of_outgoing_eq_inl c.2).symm
  right_inv c := Subtype.ext (C.subdivideOriginCorner_subdivideFirstCorner a c.1)

/-- The sides of the subdivision attached along a dart starting at the new vertex are the last
sides replacing the sides of `C` attached along the dart on which it lies. -/
private def subdivideSideInrEquiv (b : Bool) :
    {c : (C.subdivide a).Corner // (C.subdivide a).outgoing c = .inr b} ≃
      {c : C.Corner // C.outgoing c = cond b a (C.graph.rev a)} where
  toFun c := ⟨C.subdivideOriginCorner a c.1, by
    rw [← subdivideOrigin_outgoing, c.2, SerreGraph.subdivideOrigin_inr]⟩
  invFun c := ⟨C.subdivideLastCorner a c.1, by
    rw [outgoing_subdivideLastCorner, c.2]
    cases b <;> simp⟩
  left_inv c := Subtype.ext (eq_subdivideLastCorner_of_outgoing_eq_inr c.2).symm
  right_inv c := Subtype.ext (C.subdivideOriginCorner_subdivideLastCorner a c.1)

/-- The sides of the subdivision attached along a dart `x` correspond to the sides of `C` attached
along the dart on which `x` lies. -/
private def subdivideSideEquiv : (x : (C.subdivide a).graph.E) →
    {c : (C.subdivide a).Corner // (C.subdivide a).outgoing c = x} ≃
      {c : C.Corner // C.outgoing c = C.graph.subdivideOrigin a x}
  | .inl e => (C.subdivideSideInlEquiv a e).trans
      (Equiv.subtypeEquivRight fun _ => by rw [SerreGraph.subdivideOrigin_inl])
  | .inr b => (C.subdivideSideInrEquiv a b).trans
      (Equiv.subtypeEquivRight fun _ => by rw [SerreGraph.subdivideOrigin_inr])

/-- The number of sides of the subdivision attached along a dart `x` is the number of sides of
`C` attached along the dart on which `x` lies. -/
theorem sideCount_subdivide (x : (C.subdivide a).graph.E) :
    (C.subdivide a).sideCount x = C.sideCount (C.graph.subdivideOrigin a x) := by
  rw [sideCount_def, sideCount_def]
  exact Nat.card_congr (C.subdivideSideEquiv a x)

/-- The initial half of a dart `e` lies on as many sides of the subdivision as `e` lies on sides
of `C`. -/
@[simp] theorem sideCount_subdivide_inl (e : C.graph.E) :
    (C.subdivide a).sideCount (.inl e) = C.sideCount e := by
  rw [sideCount_subdivide, SerreGraph.subdivideOrigin_inl]

/-- The dart from the new vertex to the target of `a` lies on as many sides of the subdivision as
`a` lies on sides of `C`, and the dart to the source of `a` on as many as the reverse of `a`. -/
@[simp] theorem sideCount_subdivide_inr (b : Bool) :
    (C.subdivide a).sideCount (.inr b) = C.sideCount (cond b a (C.graph.rev a)) := by
  rw [sideCount_subdivide, SerreGraph.subdivideOrigin_inr]

/-- A dart of the subdivision has the link degree of the dart of `C` on which it lies. -/
theorem linkDegree_subdivide (x : (C.subdivide a).graph.E) :
    (C.subdivide a).linkDegree x = C.linkDegree (C.graph.subdivideOrigin a x) := by
  rw [linkDegree_eq_natCard_sum, linkDegree_eq_natCard_sum,
    ← SerreGraph.subdivideOrigin_subdivideRev, ← SerreGraph.subdivide_rev]
  exact Nat.card_congr ((C.subdivideSideEquiv a _).sumCongr (C.subdivideSideEquiv a x))

/-- A germ at an old vertex keeps its link degree. -/
@[simp] theorem linkDegree_subdivide_inl (e : C.graph.E) :
    (C.subdivide a).linkDegree (.inl e) = C.linkDegree e := by
  rw [linkDegree_subdivide, SerreGraph.subdivideOrigin_inl]

/-- Both germs at the new vertex have the link degree of the subdivided dart. -/
@[simp] theorem linkDegree_subdivide_inr (b : Bool) :
    (C.subdivide a).linkDegree (.inr b) = C.linkDegree a := by
  rw [linkDegree_subdivide]
  cases b <;> simp

/-! ### Links -/

/-- The map from the link of a vertex `v` of `C` to its link in the subdivision: a germ `e` is sent
to its initial half, and the link edge of a corner at `v` to the link edge of the first corner on
its side. -/
def subdivideLinkHom (v : C.graph.V) :
    (C.vertexLink v).Hom ((C.subdivide a).vertexLink (some v)) where
  mapV g := ⟨.inl g.1, congrArg some g.2⟩
  mapE d := (⟨C.subdivideFirstCorner a d.1.1, by
    rw [cornerVertex_subdivideFirstCorner, d.1.2]⟩, d.2)
  map_src := by
    rintro ⟨c, _ | _⟩
    · refine Subtype.ext ?_
      rw [vertexLink_src_false, incoming_subdivideFirstCorner]
      exact (SerreGraph.subdivideRev_subdivideLast a _).trans
        (congrArg Sum.inl (C.vertexLink_src_false c).symm)
    · refine Subtype.ext ?_
      rw [vertexLink_src_true, outgoing_subdivideFirstCorner]
      exact congrArg Sum.inl (C.vertexLink_src_true c).symm
  map_rev _ := rfl

@[simp] theorem subdivideLinkHom_mapV_val (v : C.graph.V) (g : (C.vertexLink v).V) :
    ((C.subdivideLinkHom a v).mapV g).1 = .inl g.1 := (rfl)

@[simp] theorem subdivideLinkHom_mapE_fst_val (v : C.graph.V) (d : (C.vertexLink v).E) :
    ((C.subdivideLinkHom a v).mapE d).1.1 = C.subdivideFirstCorner a d.1.1 := (rfl)

@[simp] theorem subdivideLinkHom_mapE_snd (v : C.graph.V) (d : (C.vertexLink v).E) :
    ((C.subdivideLinkHom a v).mapE d).2 = d.2 := (rfl)

variable {C a} in
/-- A corner of the subdivision at an old vertex is the first corner on its side. -/
private theorem eq_subdivideFirstCorner_of_cornerVertex_eq_some {c : (C.subdivide a).Corner}
    {v : C.graph.V} (h : (C.subdivide a).cornerVertex c = some v) :
    c = C.subdivideFirstCorner a (C.subdivideOriginCorner a c) := by
  rw [← src_outgoing] at h
  rcases hc : (C.subdivide a).outgoing c with e | b
  · exact eq_subdivideFirstCorner_of_outgoing_eq_inl hc
  · rw [hc] at h
    exact absurd h (by simp)

variable {C a} in
private theorem cornerVertex_subdivideOriginCorner_of_eq_some {c : (C.subdivide a).Corner}
    {v : C.graph.V} (h : (C.subdivide a).cornerVertex c = some v) :
    C.cornerVertex (C.subdivideOriginCorner a c) = v :=
  Option.some_injective _ <| by
    rw [← cornerVertex_subdivideFirstCorner, ← eq_subdivideFirstCorner_of_cornerVertex_eq_some h, h]

variable {C a} in
private theorem src_subdivideOrigin_of_src_eq_some {x : (C.subdivide a).graph.E} {v : C.graph.V}
    (h : (C.subdivide a).graph.src x = some v) : C.graph.src (C.graph.subdivideOrigin a x) = v := by
  obtain e | b := x
  · rw [SerreGraph.subdivideOrigin_inl]
    exact Option.some_injective _ h
  · exact absurd h (by simp)

/-- The germs of the subdivision at an old vertex are the initial halves of the germs of `C`. -/
theorem subdivideLinkHom_mapV_bijective (v : C.graph.V) :
    Function.Bijective (C.subdivideLinkHom a v).mapV := by
  refine ⟨fun g g' h => Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)), ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨e, rfl⟩ : ∃ e, x = .inl e := by
    obtain e | b := x
    exacts [⟨e, rfl⟩, absurd hx (by simp)]
  exact ⟨⟨e, Option.some_injective _ hx⟩, rfl⟩

/-- The corners of the subdivision at an old vertex are the first corners on the sides of the
corners of `C` at that vertex. -/
theorem subdivideLinkHom_mapE_bijective (v : C.graph.V) :
    Function.Bijective (C.subdivideLinkHom a v).mapE := by
  refine ⟨fun d d' h => Prod.ext (Subtype.ext (C.subdivideFirstCorner_injective a
    (congrArg (fun d => d.1.1) h))) (congrArg (fun d => d.2) h :), ?_⟩
  rintro ⟨⟨c, hc⟩, b⟩
  exact ⟨(⟨C.subdivideOriginCorner a c, cornerVertex_subdivideOriginCorner_of_eq_some hc⟩, b),
    Prod.ext (Subtype.ext (eq_subdivideFirstCorner_of_cornerVertex_eq_some hc).symm) rfl⟩

/-- The inverse of `C.subdivideLinkHom a v`: a germ of the subdivision at `v` is sent to the dart
of `C` on which it lies, and the link edge of a corner to that of the corner of `C` on whose side
it lies. -/
private def subdivideLinkInv (v : C.graph.V) :
    ((C.subdivide a).vertexLink (some v)).Hom (C.vertexLink v) where
  mapV x := ⟨C.graph.subdivideOrigin a x.1, src_subdivideOrigin_of_src_eq_some x.2⟩
  mapE d := (⟨C.subdivideOriginCorner a d.1.1,
    cornerVertex_subdivideOriginCorner_of_eq_some d.1.2⟩, d.2)
  map_src := by
    rintro ⟨⟨c, hc⟩, b⟩
    obtain ⟨c, rfl⟩ : ∃ c₀, c = C.subdivideFirstCorner a c₀ :=
      ⟨_, eq_subdivideFirstCorner_of_cornerVertex_eq_some hc⟩
    refine Subtype.ext ?_
    cases b <;> simp
  map_rev _ := rfl

variable {a} in
/-- An old vertex has a surface link in the subdivision exactly when it has one in `C`: its link
is unchanged, and its germs keep their degrees. -/
@[simp] theorem hasSurfaceLink_subdivide_some_iff {v : C.graph.V} :
    (C.subdivide a).HasSurfaceLink (some v) ↔ C.HasSurfaceLink v := by
  rw [hasSurfaceLink_iff, hasSurfaceLink_iff]
  refine and_congr (Equiv.ofBijective _ (C.subdivideLinkHom_mapE_bijective a v)).finite_iff.symm
    (and_congr ⟨(C.subdivideLinkInv a v).connected_of_surjective fun g =>
      ⟨(C.subdivideLinkHom a v).mapV g, Subtype.ext (SerreGraph.subdivideOrigin_inl a g.1)⟩,
      (C.subdivideLinkHom a v).connected_of_surjective
        (C.subdivideLinkHom_mapV_bijective a v).2⟩ ?_)
  simp [Sum.forall, Sum.exists]

variable {C} in
/-- A vertex with a surface link keeps a surface link when an edge is subdivided. -/
theorem HasSurfaceLink.subdivide {v : C.graph.V} (h : C.HasSurfaceLink v) :
    (C.subdivide a).HasSurfaceLink (some v) :=
  C.hasSurfaceLink_subdivide_some_iff.2 h

/-- The two germs at the new vertex are joined in its link as soon as a side is attached along
the subdivided edge. -/
theorem nonempty_vertexLink_subdivide_path {c : C.Corner}
    (h : C.outgoing c = a ∨ C.outgoing c = C.graph.rev a) :
    Nonempty (((C.subdivide a).vertexLink none).Path ⟨.inr true, rfl⟩ ⟨.inr false, rfl⟩) := by
  have hin := incoming_subdivideLastCorner_of_eq_or_eq h
  rcases h with h | h
  · exact (C.subdivide a).nonempty_vertexLink_path_of_corner (C.subdivideLastCorner a c)
      (a := ⟨.inr true, rfl⟩) (b := ⟨.inr false, rfl⟩) (by simp [h]) (by simp [hin, h])
  · obtain ⟨p⟩ := (C.subdivide a).nonempty_vertexLink_path_of_corner (C.subdivideLastCorner a c)
      (a := ⟨.inr false, rfl⟩) (b := ⟨.inr true, rfl⟩) (by simp [h]) (by simp [hin, h])
    exact ⟨p.reverse⟩

/-- The new vertex of a subdivision has a surface link as soon as the subdivided edge lies on one
or two face sides: its link has two germs, joined by one corner for each such side. -/
theorem hasSurfaceLink_subdivide_none (h : C.linkDegree a = 1 ∨ C.linkDegree a = 2) :
    (C.subdivide a).HasSurfaceLink none := by
  have hsrc : ∀ x : (C.subdivide a).graph.E, (C.subdivide a).graph.src x = none →
      x = .inr true ∨ x = .inr false := by
    rintro (e | _ | _) hx
    · exact absurd hx (by simp)
    · exact .inr rfl
    · exact .inl rfl
  -- Each of the two germs at the new vertex has nonzero degree, so finitely many link darts.
  have hfin (b : Bool) : Finite {d : ((C.subdivide a).vertexLink none).E //
      (((C.subdivide a).vertexLink none).src d).1 = .inr b} := by
    have hb := (C.subdivide a).linkDegree_def (.inr b)
    rw [linkDegree_subdivide_inr] at hb
    exact (Nat.card_ne_zero.1 (hb ▸ by omega)).2
  obtain ⟨c, hc⟩ := C.exists_outgoing_of_linkDegree_ne_zero (e := a) (by omega)
  refine ((C.subdivide a).hasSurfaceLink_iff _).2 ⟨Finite.of_surjective
    (fun p : (b : Bool) × {d : ((C.subdivide a).vertexLink none).E //
      (((C.subdivide a).vertexLink none).src d).1 = .inr b} => p.2.1) fun d => ?_,
    (SerreGraph.connected_iff _).2 ⟨⟨⟨.inr true, rfl⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨.inr true, rfl⟩ ?_⟩, ?_⟩
  · rcases hsrc _ (((C.subdivide a).vertexLink none).src d).2 with hd | hd
    exacts [⟨⟨true, d, hd⟩, rfl⟩, ⟨⟨false, d, hd⟩, rfl⟩]
  · rintro ⟨x, hx⟩
    rcases hsrc x hx with rfl | rfl
    · exact ⟨.nil⟩
    · exact C.nonempty_vertexLink_subdivide_path a hc
  · rcases h with h | h
    · refine .inr ⟨.inr true, .inr false, by simp, rfl, rfl, by simp [h], by simp [h],
        fun x hx hx₁ hx₂ => ?_⟩
      rcases hsrc x hx with rfl | rfl
      · exact absurd rfl hx₁
      · exact absurd rfl hx₂
    · refine .inl fun x hx => ?_
      rcases hsrc x hx with rfl | rfl <;> simp [h]

/-- The new vertex of a subdivision has a surface link exactly when the subdivided edge lies on
one or two face sides. -/
@[simp] theorem hasSurfaceLink_subdivide_none_iff :
    (C.subdivide a).HasSurfaceLink none ↔ C.linkDegree a = 1 ∨ C.linkDegree a = 2 := by
  refine ⟨fun h => ?_, C.hasSurfaceLink_subdivide_none a⟩
  rw [← C.linkDegree_subdivide_inr a true]
  exact HasSurfaceLink.linkDegree_eq_one_or_two (C.subdivide a) (e := .inr true) h

/-! ### Euler characteristic and orientability -/

/-- Subdividing an edge of a finite complex does not change its Euler characteristic: there is
one more vertex and one more edge. -/
@[simp] theorem eulerChar_subdivide [Finite C.graph.V] [Finite C.graph.GeomEdge] :
    (C.subdivide a).eulerChar = C.eulerChar := by
  rw [eulerChar_def, eulerChar_def, SerreGraph.card_subdivide_V,
    SerreGraph.card_subdivide_geomEdge]
  push_cast
  ring

/-- Subdividing an edge does not change orientability. -/
@[simp] theorem isOrientable_subdivide_iff : (C.subdivide a).IsOrientable ↔ C.IsOrientable := by
  rw [isOrientable_iff_forall_outgoing, isOrientable_iff_forall_outgoing]
  refine exists_congr fun σ => ⟨fun H c c' hne => ⟨fun h => ?_, fun h => ?_⟩,
    fun H c c' hne => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (H _ _ ((C.subdivideFirstCorner_injective a).ne hne)).1 (by simp [h])
  · exact (H (C.subdivideLastCorner a c) (C.subdivideFirstCorner a c')
      fun hc => hne (by simpa using congrArg (C.subdivideOriginCorner a) hc)).2 (by
        rw [outgoing_subdivideFirstCorner, outgoing_subdivideLastCorner, h]
        exact (SerreGraph.subdivideRev_subdivideLast a _).symm)
  · exact (H _ _ fun hc => hne (eq_of_subdivideOriginCorner_eq_of_outgoing_eq hc h.symm)).1
      (by rw [← subdivideOrigin_outgoing, ← subdivideOrigin_outgoing, h])
  · have h' : C.outgoing (C.subdivideOriginCorner a c') =
        C.graph.rev (C.outgoing (C.subdivideOriginCorner a c)) := by
      rw [← subdivideOrigin_outgoing, ← subdivideOrigin_outgoing, h,
        SerreGraph.subdivide_rev, SerreGraph.subdivideOrigin_subdivideRev]
    exact (H _ _ fun hc => C.graph.rev_ne _ (h'.symm.trans (congrArg C.outgoing hc.symm))).2 h'

end PolygonalComplex

/-! ### Surface models -/

namespace SurfaceModel

open PolygonalComplex

variable (S : SurfaceModel.{u, v, w}) [DecidableEq S.graph.E] (a : S.graph.E)

/-- The surface model obtained by subdividing the geometric edge of the dart `a`. It is reducible,
so that its underlying complex is seen to be the subdivided complex. -/
abbrev subdivide : SurfaceModel.{u, v, w} where
  toPolygonalComplex := S.toPolygonalComplex.subdivide a
  connected := S.connected.subdivide a
  hasSurfaceLink := by
    rintro (_ | v)
    · exact S.hasSurfaceLink_subdivide_none a (S.linkDegree_eq_one_or_two a)
    · exact (S.hasSurfaceLink v).subdivide a

variable {S a} in
/-- A dart of the subdivision is a boundary dart exactly when the dart of `S` on which it lies is
a boundary dart. -/
theorem mem_boundaryDarts_subdivide_iff {x : (S.subdivide a).graph.E} :
    x ∈ (S.subdivide a).boundaryDarts ↔ S.graph.subdivideOrigin a x ∈ S.boundaryDarts := by
  rw [← linkDegree_eq_one_iff_mem_boundaryDarts, ← linkDegree_eq_one_iff_mem_boundaryDarts,
    linkDegree_subdivide]

/-- The boundary darts of the subdivision are the darts lying on boundary darts of `S`. -/
theorem boundaryDarts_subdivide :
    (S.subdivide a).boundaryDarts = S.graph.subdivideOrigin a ⁻¹' S.boundaryDarts :=
  Set.ext fun _ => mem_boundaryDarts_subdivide_iff

variable {S a} in
/-- The initial half of a dart is a boundary dart of the subdivision exactly when the dart is a
boundary dart. -/
@[simp] theorem inl_mem_boundaryDarts_subdivide_iff {e : S.graph.E} :
    -- Membership is stated in `Set (S.graph.E ⊕ Bool)`, the form to which `simp` reduces
    -- `Set (S.subdivide a).graph.E`: stated in the latter form, the lemma is not found by `simp`.
    @Membership.mem (S.graph.E ⊕ Bool) (Set (S.graph.E ⊕ Bool)) _ (S.subdivide a).boundaryDarts
      (.inl e) ↔ e ∈ S.boundaryDarts := by
  rw [← linkDegree_eq_one_iff_mem_boundaryDarts, ← linkDegree_eq_one_iff_mem_boundaryDarts,
    linkDegree_subdivide_inl]

variable {S a} in
/-- The darts at the new vertex are boundary darts of the subdivision exactly when the subdivided
dart is a boundary dart. -/
@[simp] theorem inr_mem_boundaryDarts_subdivide_iff {b : Bool} :
    -- Stated in `Set (S.graph.E ⊕ Bool)` for the same reason as the lemma above.
    @Membership.mem (S.graph.E ⊕ Bool) (Set (S.graph.E ⊕ Bool)) _ (S.subdivide a).boundaryDarts
      (.inr b) ↔ a ∈ S.boundaryDarts := by
  rw [← linkDegree_eq_one_iff_mem_boundaryDarts, ← linkDegree_eq_one_iff_mem_boundaryDarts,
    linkDegree_subdivide_inr]

/-! ### The subdivided torus -/

/-- Subdividing an edge of the torus keeps the Euler characteristic `0`. -/
theorem eulerChar_torus_subdivide (a : torus.graph.E) : (torus.subdivide a).eulerChar = 0 :=
  (PolygonalComplex.eulerChar_subdivide _ a).trans eulerChar_torus

/-- Subdividing an edge of the torus creates no boundary. -/
theorem boundaryDarts_torus_subdivide (a : torus.graph.E) :
    (torus.subdivide a).boundaryDarts = ∅ := by
  rw [boundaryDarts_subdivide, boundaryDarts_torus, Set.preimage_empty]

/-- The link of the new vertex of a subdivided torus is a circle: both of its germs have degree
two. -/
theorem linkDegree_torus_subdivide_inr (a : torus.graph.E) (b : Bool) :
    (torus.subdivide a).linkDegree (.inr b) = 2 :=
  linkDegree_eq_two_iff_notMem_boundaryDarts.2 (by
    rw [boundaryDarts_torus_subdivide]
    exact Set.notMem_empty _)

/-- Subdividing an edge of the torus keeps it orientable. -/
theorem isOrientable_torus_subdivide (a : torus.graph.E) : (torus.subdivide a).IsOrientable :=
  (isOrientable_subdivide_iff _ a).2 isOrientable_torus

end SurfaceModel

end TauCeti
