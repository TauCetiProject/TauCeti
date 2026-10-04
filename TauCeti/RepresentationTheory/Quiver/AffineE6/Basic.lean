/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sum
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph

/-!
# The extended Dynkin quiver of type `E₆~`

The quiver `TauCeti.Quiver.AffineE6` has a *centre* and three arms of two vertices each: for
`i : Fin 3` an *outer* vertex `outer i` with one arrow into the *inner* vertex `inner i`, which has
one arrow into the centre. Its underlying graph is the extended Dynkin diagram `E₆~`, the star with
three arms of length two, on seven vertices, here with every arrow pointing towards the centre.
On the root-system side this is the star `TauCeti.starCartanMatrix ![2, 2, 2]`, whose Cartan
matrix is not of finite type (`TauCeti.not_isFiniteType_affineE₆`).

This file carries the vertex and arrow data, and the shape of the underlying graph: it is a tree,
with at most one arrow between any two vertices, because every vertex is the source of at most one
arrow and every arrow points towards the centre. The representation theory, that the quiver has
infinite representation type, is in `TauCeti.RepresentationTheory.Quiver.AffineE6.FiniteRepType`.

## Main definitions

* `TauCeti.Quiver.AffineE6`: the vertex type, with constructors `center`, `inner` and `outer`, and
  a `Quiver` instance.
* `TauCeti.Quiver.AffineE6.vertexEquiv`: the vertices as `Unit ⊕ Fin 3 ⊕ Fin 3`, so that there are
  seven of them (`TauCeti.Quiver.AffineE6.card_eq`).
* `TauCeti.Quiver.AffineE6.outerArrow` and `TauCeti.Quiver.AffineE6.innerArrow`: the arrow from an
  outer vertex to the inner vertex of its arm, and the arrow from an inner vertex into the centre.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

namespace Quiver

/-- The extended Dynkin quiver `E₆~`: a centre and three arms, each an outer vertex with an arrow
into an inner vertex, which has an arrow into the centre. -/
inductive AffineE6 : Type
  | /-- The centre, the head of the three inner arrows. -/
    center : AffineE6
  | /-- The inner vertex of the arm indexed by `i`, adjacent to the centre. -/
    inner (i : Fin 3) : AffineE6
  | /-- The outer vertex of the arm indexed by `i`, the tail of a single arrow. -/
    outer (i : Fin 3) : AffineE6
  deriving DecidableEq

namespace AffineE6

/-! ### The seven vertices -/

/-- The vertices of `TauCeti.Quiver.AffineE6` as `Unit ⊕ Fin 3 ⊕ Fin 3`: the centre, then the
inner vertices, then the outer vertices. -/
def vertexEquiv : AffineE6 ≃ Unit ⊕ Fin 3 ⊕ Fin 3 where
  toFun
    | .center => .inl ()
    | .inner i => .inr (.inl i)
    | .outer i => .inr (.inr i)
  invFun
    | .inl _ => center
    | .inr (.inl i) => inner i
    | .inr (.inr i) => outer i
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with _ | _ | _ <;> rfl

@[simp]
theorem vertexEquiv_center : vertexEquiv center = Sum.inl () :=
  -- Parentheses keep the proof from exporting definitional equality, so the body stays hidden.
  (rfl)

@[simp]
theorem vertexEquiv_inner (i : Fin 3) : vertexEquiv (inner i) = Sum.inr (Sum.inl i) :=
  (rfl)

@[simp]
theorem vertexEquiv_outer (i : Fin 3) : vertexEquiv (outer i) = Sum.inr (Sum.inr i) :=
  (rfl)

@[simp]
theorem vertexEquiv_symm_inl (u : Unit) : vertexEquiv.symm (Sum.inl u) = center :=
  (rfl)

@[simp]
theorem vertexEquiv_symm_inr_inl (i : Fin 3) :
    vertexEquiv.symm (Sum.inr (Sum.inl i)) = inner i := (rfl)

@[simp]
theorem vertexEquiv_symm_inr_inr (i : Fin 3) :
    vertexEquiv.symm (Sum.inr (Sum.inr i)) = outer i := (rfl)

instance : Fintype AffineE6 := Fintype.ofEquiv _ vertexEquiv.symm

/-- `TauCeti.Quiver.AffineE6` has seven vertices, as the extended Dynkin diagram `E₆~` should. -/
@[simp]
theorem card_eq : Fintype.card AffineE6 = 7 := by
  rw [Fintype.card_congr vertexEquiv]
  simp

/-! ### The arrows -/

instance : _root_.Quiver.{0} AffineE6 where
  Hom a b :=
    match a, b with
    | .outer i, .inner j => PLift (i = j)
    | .inner _, .center => PUnit.{1}
    | _, _ => PEmpty.{1}

/-- The arrow from the outer vertex of the arm indexed by `i` to the inner vertex of that arm. -/
def outerArrow (i : Fin 3) : outer i ⟶ inner i := PLift.up rfl

/-- The arrow from the inner vertex of the arm indexed by `i` into the centre. -/
def innerArrow (i : Fin 3) : inner i ⟶ center := PUnit.unit

instance instUniqueHomInnerCenter (i : Fin 3) : Unique (inner i ⟶ center) :=
  inferInstanceAs (Unique PUnit)

/-- No arrow leaves the centre. -/
instance instIsEmptyHomCenter : ∀ v : AffineE6, IsEmpty (center ⟶ v)
  | .center => inferInstanceAs (IsEmpty PEmpty)
  | .inner _ => inferInstanceAs (IsEmpty PEmpty)
  | .outer _ => inferInstanceAs (IsEmpty PEmpty)

instance (i j : Fin 3) : IsEmpty (inner i ⟶ inner j) := inferInstanceAs (IsEmpty PEmpty)

instance (i j : Fin 3) : IsEmpty (inner i ⟶ outer j) := inferInstanceAs (IsEmpty PEmpty)

instance (i : Fin 3) : IsEmpty (outer i ⟶ center) := inferInstanceAs (IsEmpty PEmpty)

instance (i j : Fin 3) : IsEmpty (outer i ⟶ outer j) := inferInstanceAs (IsEmpty PEmpty)

/-- Between any two vertices of `TauCeti.Quiver.AffineE6` there is at most one arrow. -/
instance instSubsingletonHom : ∀ a b : AffineE6, Subsingleton (a ⟶ b)
  | .outer _, .inner _ => inferInstanceAs (Subsingleton (PLift _))
  | .inner _, .center => inferInstance
  | .center, .center => inferInstance
  | .center, .inner _ => inferInstance
  | .center, .outer _ => inferInstance
  | .inner _, .inner _ => inferInstance
  | .inner _, .outer _ => inferInstance
  | .outer _, .center => inferInstance
  | .outer _, .outer _ => inferInstance


/-! ### The underlying graph -/

/-- The distance to the centre, which every arrow lowers. -/
private def height : AffineE6 → ℕ
  | .center => 0
  | .inner _ => 1
  | .outer _ => 2

private theorem height_lt : ∀ ⦃a b : AffineE6⦄, (a ⟶ b) → height b < height a
  | .outer _, .inner _, _ => by simp [height]
  | .inner _, .center, _ => by simp [height]
  | .center, _, e => isEmptyElim e
  | .inner _, .inner _, e => isEmptyElim e
  | .inner _, .outer _, e => isEmptyElim e
  | .outer _, .center, e => isEmptyElim e
  | .outer _, .outer _, e => isEmptyElim e

/-- The arrows out of a vertex of `TauCeti.Quiver.AffineE6` all share their target. -/
private theorem eq_of_hom_of_hom ⦃a b b' : AffineE6⦄ (e : a ⟶ b) (e' : a ⟶ b') : b = b' := by
  cases a <;> cases b <;> cases b' <;> first
    | rfl
    | exact isEmptyElim e
    | exact isEmptyElim e'
    | exact congrArg inner (e.down.symm.trans e'.down)

/-- **The underlying graph of `TauCeti.Quiver.AffineE6` is acyclic**, so it is the tree `E₆~`. -/
theorem isAcyclic_underlyingGraph : (underlyingGraph AffineE6).IsAcyclic :=
  isAcyclic_underlyingGraph_of_lt height height_lt eq_of_hom_of_hom

/-- Two vertices of `TauCeti.Quiver.AffineE6` are joined by at most one arrow, counted in both
directions. -/
theorem subsingleton_hom_sum (a b : AffineE6) : Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)) :=
  subsingleton_hom_sum_of_lt height a b (height_lt (a := a) (b := b))
    (height_lt (a := b) (b := a))

end AffineE6

end Quiver

end TauCeti
