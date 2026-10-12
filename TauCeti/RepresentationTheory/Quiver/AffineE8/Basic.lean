/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph

/-!
# The extended Dynkin quiver of type `E₈~`

`TauCeti.Quiver.AffineE8` is the star with arms of lengths one, two and five, with all
arrows pointing towards the centre. Representations with injective arrows are configurations
of a subspace, a two-step flag and a five-step flag in the centre space. This is the
extended Dynkin diagram `T₂,₃,₆`; its infinite representation type is proved in
`TauCeti.RepresentationTheory.Quiver.AffineE8.FiniteRepType`. The underlying graph is a tree,
with at most one arrow between any two vertices, because every vertex is the source of at most one
arrow and every arrow points towards the centre.

## References

* Assem–Simson–Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  Chapter VII.
-/

public section

namespace TauCeti.Quiver

/-- The inward orientation of the extended Dynkin diagram `E₈~`. The subscripts on the
long and medium arms record the coefficients of the minimal imaginary root. -/
inductive AffineE8
  | center | short | medium2 | medium4 | long1 | long2 | long3 | long4 | long5
  deriving DecidableEq

namespace AffineE8

instance : Fintype AffineE8 where
  elems := {center, short, medium2, medium4, long1, long2, long3, long4, long5}
  complete v := by cases v <;> simp

/-- The eight arrows, directed towards the centre along the three arms. -/
inductive Arrow : AffineE8 → AffineE8 → Type
  | short : Arrow short center
  | medium2 : Arrow medium2 medium4
  | medium4 : Arrow medium4 center
  | long1 : Arrow long1 long2
  | long2 : Arrow long2 long3
  | long3 : Arrow long3 long4
  | long4 : Arrow long4 long5
  | long5 : Arrow long5 center
  deriving DecidableEq

instance : _root_.Quiver AffineE8 := ⟨Arrow⟩

/-- There is at most one arrow between any two vertices. -/
instance (a b : AffineE8) : Subsingleton (a ⟶ b) := by
  constructor
  intro e f
  cases e <;> cases f <;> rfl

noncomputable instance (a b : AffineE8) : Fintype (a ⟶ b) := Fintype.ofFinite _

/-- The minimal imaginary-root multiplicities, used as the numbers of coordinates in the
flag construction. -/
abbrev coordinateCount : AffineE8 → ℕ
  | center => 6
  | short => 3
  | medium2 => 2
  | medium4 => 4
  | long1 => 1
  | long2 => 2
  | long3 => 3
  | long4 => 4
  | long5 => 5

/-- The extended diagram has nine vertices. -/
@[simp] theorem card_eq : Fintype.card AffineE8 = 9 := by decide


/-! ### The underlying graph -/

/-- The distance to the centre, which every arrow lowers. -/
private def height : AffineE8 → ℕ
  | center => 0
  | short => 1
  | medium2 => 2
  | medium4 => 1
  | long1 => 5
  | long2 => 4
  | long3 => 3
  | long4 => 2
  | long5 => 1

private theorem height_lt ⦃a b : AffineE8⦄ (e : a ⟶ b) : height b < height a := by
  cases e <;> simp [height]

/-- The arrows out of a vertex of `TauCeti.Quiver.AffineE8` all share their target. -/
private theorem eq_of_hom_of_hom ⦃a b b' : AffineE8⦄ (e : a ⟶ b) (e' : a ⟶ b') : b = b' := by
  cases e <;> cases e' <;> rfl

/-- **The underlying graph of `TauCeti.Quiver.AffineE8` is acyclic**, so it is the tree `E₈~`. -/
theorem isAcyclic_underlyingGraph : (underlyingGraph AffineE8).IsAcyclic :=
  isAcyclic_underlyingGraph_of_lt height height_lt eq_of_hom_of_hom

/-- Two vertices of `TauCeti.Quiver.AffineE8` are joined by at most one arrow, counted in both
directions. -/
theorem subsingleton_hom_sum (a b : AffineE8) : Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)) :=
  subsingleton_hom_sum_of_lt height a b (height_lt (a := a) (b := b))
    (height_lt (a := b) (b := a))

end AffineE8
end TauCeti.Quiver
