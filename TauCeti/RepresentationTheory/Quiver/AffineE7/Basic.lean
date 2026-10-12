/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph

/-!
# The extended Dynkin quiver of type `E₇~`

The quiver `TauCeti.Quiver.AffineE7` has a *centre*, a *short* arm consisting of one vertex, and
two long arms of three vertices each: for `i : Fin 2` an *outer* vertex `outer i` with one arrow
into the *middle* vertex `middle i`, which has one arrow into the *inner* vertex `inner i`, which
has one arrow into the centre; the short vertex has one arrow into the centre. Its underlying graph
is the extended Dynkin diagram `E₇~`, the star with arms of lengths one, three and three, on eight
vertices, here with every arrow pointing towards the centre. On the root-system side this is the
star `TauCeti.starCartanMatrix ![1, 3, 3]`, which is the generalized Cartan matrix of
`TauCeti.AffineDynkinType.E7` up to relabelling
(`TauCeti.AffineDynkinType.starCartanMatrix_one_three_three_eq_submatrix_E7`).

The arrows form the inductive family `TauCeti.Quiver.AffineE7.Arrow`, with one constructor for
each kind of arrow, so that a definition by cases on an arrow lists exactly the arrows of `E₇~`.

This file carries the vertex and arrow data, and the shape of the underlying graph: it is a tree,
with at most one arrow between any two vertices, because every vertex is the source of at most one
arrow and every arrow points towards the centre.

## Main definitions

* `TauCeti.Quiver.AffineE7`: the vertex type, with constructors `center`, `short`, `inner`,
  `middle` and `outer`, and a `Quiver` instance; it has eight vertices
  (`TauCeti.Quiver.AffineE7.card_eq`).
* `TauCeti.Quiver.AffineE7.Arrow`: the arrows `outer i ⟶ middle i`, `middle i ⟶ inner i`,
  `inner i ⟶ center` and `short ⟶ center`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

namespace Quiver

/-- The extended Dynkin quiver `E₇~`: a centre, a short arm of one vertex with an arrow into the
centre, and two long arms, each an outer vertex with an arrow into a middle vertex, which has an
arrow into an inner vertex, which has an arrow into the centre. -/
inductive AffineE7 : Type
  | /-- The centre, the head of the arrows from the inner vertices and the short vertex. -/
    center : AffineE7
  | /-- The vertex of the short arm, adjacent to the centre. -/
    short : AffineE7
  | /-- The inner vertex of the long arm indexed by `i`, adjacent to the centre. -/
    inner (i : Fin 2) : AffineE7
  | /-- The middle vertex of the long arm indexed by `i`. -/
    middle (i : Fin 2) : AffineE7
  | /-- The outer vertex of the long arm indexed by `i`, the tail of a single arrow. -/
    outer (i : Fin 2) : AffineE7
  deriving DecidableEq, Fintype

namespace AffineE7

/-- `TauCeti.Quiver.AffineE7` has eight vertices, as the extended Dynkin diagram `E₇~` should. -/
@[simp]
theorem card_eq : Fintype.card AffineE7 = 8 :=
  (rfl)

/-- The arrows of the extended Dynkin quiver `E₇~`, all pointing towards the centre. -/
inductive Arrow : AffineE7 → AffineE7 → Type
  | /-- The arrow from the outer vertex of the long arm `i` to its middle vertex. -/
    outerMiddle (i : Fin 2) : Arrow (outer i) (middle i)
  | /-- The arrow from the middle vertex of the long arm `i` to its inner vertex. -/
    middleInner (i : Fin 2) : Arrow (middle i) (inner i)
  | /-- The arrow from the inner vertex of the long arm `i` into the centre. -/
    innerCenter (i : Fin 2) : Arrow (inner i) center
  | /-- The arrow from the vertex of the short arm into the centre. -/
    shortCenter : Arrow short center

instance : _root_.Quiver.{0} AffineE7 where
  Hom := Arrow

/-- Between any two vertices of `TauCeti.Quiver.AffineE7` there is at most one arrow. -/
instance instSubsingletonHom (a b : AffineE7) : Subsingleton (a ⟶ b) :=
  ⟨fun e e' ↦ by cases e <;> cases e' <;> rfl⟩

/-- Each arrow space of `TauCeti.Quiver.AffineE7` is finite, having at most one arrow. -/
noncomputable instance instFintypeHom (a b : AffineE7) : Fintype (a ⟶ b) :=
  Fintype.ofFinite _


/-! ### The underlying graph -/

/-- The distance to the centre, which every arrow lowers. -/
private def height : AffineE7 → ℕ
  | .center => 0
  | .short => 1
  | .inner _ => 1
  | .middle _ => 2
  | .outer _ => 3

private theorem height_lt ⦃a b : AffineE7⦄ (e : a ⟶ b) : height b < height a := by
  cases e <;> simp [height]

/-- The arrows out of a vertex of `TauCeti.Quiver.AffineE7` all share their target. -/
private theorem eq_of_hom_of_hom ⦃a b b' : AffineE7⦄ (e : a ⟶ b) (e' : a ⟶ b') : b = b' := by
  cases e <;> cases e' <;> rfl

/-- **The underlying graph of `TauCeti.Quiver.AffineE7` is acyclic**, so it is the tree `E₇~`. -/
theorem isAcyclic_underlyingGraph : (underlyingGraph AffineE7).IsAcyclic :=
  isAcyclic_underlyingGraph_of_lt height height_lt eq_of_hom_of_hom

/-- Two vertices of `TauCeti.Quiver.AffineE7` are joined by at most one arrow, counted in both
directions. -/
theorem subsingleton_hom_sum (a b : AffineE7) : Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)) :=
  subsingleton_hom_sum_of_lt height a b (height_lt (a := a) (b := b))
    (height_lt (a := b) (b := a))

end AffineE7

end Quiver

end TauCeti
