/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Finsupp.LSum
import TauCeti.KnotTheory.Grid.Complex
import TauCeti.KnotTheory.Grid.Rotation

/-!
# The half-turn rotation symmetry of the fully blocked grid differential

The grid-combinatorial lane already carries the half-turn rotation of grid states and diagrams
(`Rotation.lean`) and the resulting invariance of the Maslov and Alexander gradings
(`Gradings.lean`, `GradingInteger.lean`). It also carries the *diagonal-reflection* and
*marking-swap* symmetries of the rectangle calculus and the fully blocked differential all the
way up (`Rectangle.lean`, `BlockedRectangle.lean`, `DifferentialSymmetry.lean`). This file
supplies the missing third symmetry: it lifts the half-turn rotation through the rectangle
calculus to the fully blocked grid complex, matching what the diagonal reflection already has.

The half-turn rotation reverses both grid coordinates, `(c, r) ↦ (cᵒ, rᵒ)` with `·ᵒ = Fin.rev`.
On an oriented rectangle from `x` to `y` it reverses and exchanges the two side columns, giving an
oriented rectangle from `x.rotate` to `y.rotate` whose interior is the half-turn rotation of the
original interior. Reversal is an involution only up to `Fin.rev_rev`, not definitionally, so —
unlike `GridRectangleBetween.transpose`, whose involution comes from `Equiv.symm` — the inverse
rotation is given its own construction `GridRectangleBetween.rotateSymm` rather than reusing
`rotate`, and the two assemble into the equivalence `GridRectangleBetween.rotateEquiv`.

## Main definitions

* `TauCeti.GridRectangle.rotate`: the half-turn rotation of a toroidal rectangle.
* `TauCeti.GridRectangleBetween.rotate`: the half-turn rotation of an oriented rectangle, from
  `x.rotate` to `y.rotate`.
* `TauCeti.GridRectangleBetween.rotateEquiv`: the rotation packaged as an equivalence with
  oriented rectangles from `x.rotate` to `y.rotate`.
* `TauCeti.GridChain.rotateEquiv`: the chain-module relabeling induced by `GridState.rotate`.

## Main results

* `TauCeti.Grid.cIoo_image_rev`: a clockwise cyclic interval reversed by `Fin.rev` is the
  clockwise cyclic interval with reversed, exchanged endpoints.
* `TauCeti.GridRectangleBetween.isEmpty_rotate`,
  `TauCeti.GridRectangleBetween.avoidsMarkings_rotate`: rotation preserves emptiness and marking
  avoidance.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_rotate`: the fully blocked rectangle count is
  invariant under the half-turn rotation of a grid diagram and its two states.
* `TauCeti.GridDiagram.fullyBlockedDifferential_rotate`: the fully blocked differential commutes
  with the rotation chain relabeling, intertwining the differentials of `G` and `G.rotate`; this
  is the chain-level form of the statement that the half-turn rotation is a symmetry of the fully
  blocked grid complex.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8 ("Symmetries
and the genus bound"), together with that roadmap's standing convention to "state invariance
naturality-ready": these are the chain-level symmetries of the fully blocked grid complex on which
an invariance statement is later built. The half-turn rotation is one of the standard grid
symmetries of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace Grid

variable {n : ℕ}

/-- A clockwise open cyclic interval reversed by `Fin.rev` is the clockwise open cyclic interval
with the two endpoints reversed and exchanged.

Coordinate reversal reverses the cyclic order, so it turns the clockwise arc from `a` to `b` into
the clockwise arc from `bᵒ` to `aᵒ`. -/
theorem cIoo_image_rev (a b : Fin n) :
    (cIoo a b).image Fin.rev = cIoo b.rev a.rev := by
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cIoo] at hx ⊢
    obtain ⟨hne, hc⟩ := hx
    refine ⟨fun h => hne (Fin.rev_injective h).symm, ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hx' := x.isLt
    simp only [Fin.val_rev]
    split_ifs at hc ⊢ <;> omega
  · intro hy
    refine ⟨Fin.rev y, ?_, Fin.rev_rev y⟩
    rw [mem_cIoo] at hy ⊢
    obtain ⟨hne, hc⟩ := hy
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hy' := y.isLt
    simp only [Fin.val_rev] at hc ⊢
    split_ifs at hc ⊢ <;> omega

end Grid

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The half-turn rotation of a toroidal rectangle.

Reversing both coordinates reverses the cyclic order in each direction, so the two vertical sides
are reversed and exchanged, and likewise the two horizontal sides. -/
def rotate : GridRectangle n where
  left := R.right.rev
  right := R.left.rev
  bottom := R.top.rev
  top := R.bottom.rev

/-- The rotated rectangle's left side is the reversed original right side. -/
@[simp]
theorem rotate_left : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated rectangle's right side is the reversed original left side. -/
@[simp]
theorem rotate_right : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated rectangle's bottom side is the reversed original top side. -/
@[simp]
theorem rotate_bottom : R.rotate.bottom = R.top.rev :=
  rfl

/-- The rotated rectangle's top side is the reversed original bottom side. -/
@[simp]
theorem rotate_top : R.rotate.top = R.bottom.rev :=
  rfl

/-- The interior columns of the rotated rectangle are the reversed original interior columns. -/
theorem columnInterior_rotate : R.rotate.columnInterior = R.columnInterior.image Fin.rev := by
  simp only [columnInterior, rotate_left, rotate_right, Grid.cIoo_image_rev]

/-- The interior rows of the rotated rectangle are the reversed original interior rows. -/
theorem rowInterior_rotate : R.rotate.rowInterior = R.rowInterior.image Fin.rev := by
  simp only [rowInterior, rotate_bottom, rotate_top, Grid.cIoo_image_rev]

/-- The interior of the rotated rectangle is the half-turn rotation of the original interior. -/
theorem interior_rotate :
    R.rotate.interior = R.interior.image (Prod.map Fin.rev Fin.rev) := by
  simp only [interior, Finset.prodMap_image_product, columnInterior_rotate, rowInterior_rotate]

end GridRectangle

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- Two oriented rectangles between the same states with equal side columns are equal. -/
private theorem eq_of_sides {R S : GridRectangleBetween x y} (hleft : R.left = S.left)
    (hright : R.right = S.right) : R = S := by
  obtain ⟨_, _, _, _, _, _⟩ := R
  obtain ⟨_, _, _, _, _, _⟩ := S
  obtain rfl : _ = _ := hleft
  obtain rfl : _ = _ := hright
  rfl

/-- The half-turn rotation of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.rotate` to `y.rotate`.

Reversing both coordinates reverses and exchanges the two side columns: the new initial side is
the reversed terminal column `R.rightᵒ` and the new terminal side is the reversed initial column
`R.leftᵒ`. -/
def rotate (R : GridRectangleBetween x y) : GridRectangleBetween x.rotate y.rotate where
  left := R.right.rev
  right := R.left.rev
  left_ne_right := fun h => R.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    simp only [GridState.rotate_apply, Fin.rev_rev, R.map_right]
  map_right := by
    simp only [GridState.rotate_apply, Fin.rev_rev, R.map_left]
  map_of_ne c hl hr := by
    have h1 : Fin.rev c ≠ R.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have h2 : Fin.rev c ≠ R.right := fun h => hl (Fin.rev_eq_iff.mp h)
    simp only [GridState.rotate_apply, R.map_of_ne (Fin.rev c) h1 h2]

/-- The rotated oriented rectangle's initial side column is the reversed terminal side column. -/
@[simp]
theorem rotate_left (R : GridRectangleBetween x y) : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated oriented rectangle's terminal side column is the reversed initial side column. -/
@[simp]
theorem rotate_right (R : GridRectangleBetween x y) : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated oriented rectangle's initial side row is the reversed terminal side row. -/
@[simp]
theorem rotate_bottom (R : GridRectangleBetween x y) : R.rotate.bottom = R.top.rev := by
  simp only [GridRectangleBetween.bottom, GridRectangleBetween.top, rotate_left,
    GridState.rotate_apply, Fin.rev_rev]

/-- The rotated oriented rectangle's terminal side row is the reversed initial side row. -/
@[simp]
theorem rotate_top (R : GridRectangleBetween x y) : R.rotate.top = R.bottom.rev := by
  simp only [GridRectangleBetween.top, GridRectangleBetween.bottom, rotate_right,
    GridState.rotate_apply, Fin.rev_rev]

/-- The toroidal rectangle of the rotated oriented rectangle is the rotation of the toroidal
rectangle. -/
theorem rotate_toGridRectangle (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle = R.toGridRectangle.rotate := by
  change GridRectangle.mk R.rotate.left R.rotate.right R.rotate.bottom R.rotate.top =
    GridRectangle.mk R.right.rev R.left.rev R.top.rev R.bottom.rev
  rw [rotate_left, rotate_right, rotate_bottom, rotate_top]

/-- The interior of the rotated oriented rectangle is the half-turn rotation of the interior of
the original oriented rectangle. -/
theorem interior_rotate (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle.interior =
      R.toGridRectangle.interior.image (Prod.map Fin.rev Fin.rev) := by
  rw [rotate_toGridRectangle, GridRectangle.interior_rotate]

/-- The inverse half-turn rotation, an oriented rectangle from `x` to `y` built from one between
the rotated states. It reverses and exchanges the side columns by the same recipe as `rotate`,
but lands in `GridRectangleBetween x y` directly; reversal is only an involution up to
`Fin.rev_rev`, so this avoids transporting along the (non-definitional) state involution. -/
def rotateSymm (S : GridRectangleBetween x.rotate y.rotate) : GridRectangleBetween x y where
  left := S.right.rev
  right := S.left.rev
  left_ne_right := fun h => S.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    have h := S.map_right
    rw [GridState.rotate_apply, GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_right := by
    have h := S.map_left
    rw [GridState.rotate_apply, GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_of_ne c hl hr := by
    have h1 : Fin.rev c ≠ S.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have h2 : Fin.rev c ≠ S.right := fun h => hl (Fin.rev_eq_iff.mp h)
    have h := S.map_of_ne (Fin.rev c) h1 h2
    rw [GridState.rotate_apply, GridState.rotate_apply, Fin.rev_rev] at h
    exact Fin.rev_injective h

/-- The inverse rotation's initial side column is the reversed terminal side column. -/
@[simp]
theorem rotateSymm_left (S : GridRectangleBetween x.rotate y.rotate) :
    (rotateSymm S).left = S.right.rev :=
  rfl

/-- The inverse rotation's terminal side column is the reversed initial side column. -/
@[simp]
theorem rotateSymm_right (S : GridRectangleBetween x.rotate y.rotate) :
    (rotateSymm S).right = S.left.rev :=
  rfl

/-- The half-turn rotation as an equivalence between oriented rectangles from `x` to `y` and
oriented rectangles from `x.rotate` to `y.rotate`. -/
def rotateEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween x.rotate y.rotate where
  toFun := rotate
  invFun := rotateSymm
  left_inv R := eq_of_sides (by simp) (by simp)
  right_inv S := eq_of_sides (by simp) (by simp)

/-- The rotation equivalence applies a rectangle by rotating it. -/
@[simp]
theorem rotateEquiv_apply (R : GridRectangleBetween x y) :
    rotateEquiv x y R = R.rotate :=
  rfl

/-- The half-turn rotation preserves emptiness of a rectangle between grid states. -/
theorem isEmpty_rotate (R : GridRectangleBetween x y) :
    R.rotate.IsEmpty ↔ R.IsEmpty := by
  unfold GridRectangleBetween.IsEmpty GridRectangle.IsEmptyFor
  rw [interior_rotate, GridState.rotate_pointSet,
    Finset.disjoint_image (Fin.rev_injective.prodMap Fin.rev_injective)]

/-- The half-turn rotation preserves marking avoidance of a rectangle between grid states. -/
theorem avoidsMarkings_rotate (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.rotate.AvoidsMarkings G.rotate ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings GridRectangle.AvoidsMarkings
  rw [interior_rotate, G.rotate_OSet, G.rotate_XSet, ← Finset.image_union,
    Finset.disjoint_image (Fin.rev_injective.prodMap Fin.rev_injective)]

end GridRectangleBetween

namespace GridChain

/-- The linear automorphism of grid chains induced by the half-turn rotation of grid states.

Because `GridState.rotate` is an involution, relabeling each generator `x` by `x.rotate` gives a
linear automorphism of the chain module `GridChain R n`. -/
noncomputable def rotateEquiv (R : Type*) [Semiring R] (n : ℕ) :
    GridChain R n ≃ₗ[R] GridChain R n :=
  Finsupp.domLCongr
    { toFun := GridState.rotate
      invFun := GridState.rotate
      left_inv := GridState.rotate_rotate
      right_inv := GridState.rotate_rotate }

/-- The rotation relabeling sends the generator `x` to the generator `x.rotate`. -/
@[simp]
theorem rotateEquiv_single {R : Type*} [Semiring R] {n : ℕ} (x : GridState n) (a : R) :
    rotateEquiv R n (Finsupp.single x a) = Finsupp.single x.rotate a := by
  unfold rotateEquiv
  rw [Finsupp.domLCongr_single]
  rfl

/-- The `y`-coefficient of a relabeled chain is the `y.rotate`-coefficient of the original
chain. -/
@[simp]
theorem rotateEquiv_apply {R : Type*} [Semiring R] {n : ℕ} (f : GridChain R n)
    (y : GridState n) : rotateEquiv R n f y = f y.rotate := by
  unfold rotateEquiv
  rw [Finsupp.domLCongr_apply]
  exact Finsupp.equivMapDomain_apply _ _ _

end GridChain

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The half-turn rotation of a fully blocked rectangle is a fully blocked rectangle for the
rotated diagram and rotated states. -/
theorem mem_fullyBlockedRectangles_rotate (x y : GridState n) (R : GridRectangleBetween x y) :
    R.rotate ∈ G.rotate.fullyBlockedRectangles x.rotate y.rotate ↔
      R ∈ G.fullyBlockedRectangles x y := by
  simp only [mem_fullyBlockedRectangles, GridRectangleBetween.isEmpty_rotate,
    GridRectangleBetween.avoidsMarkings_rotate]

/-- The fully blocked rectangle count is invariant under the half-turn rotation of a grid diagram
and its two states. This is the matrix-coefficient form of the statement that the half-turn
rotation is a chain symmetry of the fully blocked grid complex. -/
theorem fullyBlockedRectangleCount_rotate (x y : GridState n) :
    G.rotate.fullyBlockedRectangleCount x.rotate y.rotate =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def]
  congr 1
  exact (Finset.card_equiv (GridRectangleBetween.rotateEquiv x y) fun R =>
    (G.mem_fullyBlockedRectangles_rotate x y R).symm).symm

/-- The generator row of the fully blocked differential intertwines the half-turn rotation: the
rotated diagram's row on `x.rotate` is the rotation relabeling of the original row on `x`. -/
theorem fullyBlockedDifferentialOnGenerator_rotate (x : GridState n) :
    G.rotate.fullyBlockedDifferentialOnGenerator x.rotate =
      GridChain.rotateEquiv (ZMod 2) n (G.fullyBlockedDifferentialOnGenerator x) := by
  refine Finsupp.ext fun y => ?_
  rw [GridChain.rotateEquiv_apply, fullyBlockedDifferentialOnGenerator_apply,
    fullyBlockedDifferentialOnGenerator_apply,
    ← G.fullyBlockedRectangleCount_rotate x y.rotate, GridState.rotate_rotate]

/-- The fully blocked grid differential commutes with the rotation chain relabeling, intertwining
the differentials of `G` and `G.rotate`. This is the chain-level form of the statement that the
half-turn rotation is a symmetry of the fully blocked grid complex. -/
theorem fullyBlockedDifferential_rotate :
    G.rotate.fullyBlockedDifferential ∘ₗ (GridChain.rotateEquiv (ZMod 2) n).toLinearMap =
      (GridChain.rotateEquiv (ZMod 2) n).toLinearMap ∘ₗ G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.rotateEquiv_single, fullyBlockedDifferential_single]
  exact G.fullyBlockedDifferentialOnGenerator_rotate x

end GridDiagram

end TauCeti
