/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Complex
import TauCeti.KnotTheory.Grid.Rotation

/-!
# The half-turn rotation symmetry of the fully blocked grid differential

The grid-combinatorial lane already records the half-turn rotation of grid states and diagrams
(`Rotation.lean`) and proves it leaves the Maslov and Alexander gradings unchanged
(`Gradings.lean`, `GradingInteger.lean`). The diagonal reflection has been carried one level
further, to the chain complex itself (`DifferentialSymmetry.lean`). This file does the same for
the half-turn rotation: it lifts rotation from grid squares to oriented rectangles, shows the
rotation of a rectangle preserves emptiness and marking avoidance, and concludes that rotation
is a chain symmetry of the fully blocked grid complex.

The geometric subtlety is that the `180°` rotation reverses the toroidal cyclic order. A
clockwise rectangle from `x` to `y`, rotated, is the rectangle whose two side columns are the
two original side columns reversed *and swapped*: `GridRectangle.rotate` sends the sides
`(left, right, bottom, top)` to `(rightᵒ, leftᵒ, topᵒ, bottomᵒ)` with `·ᵒ = Fin.rev`. The
underlying one-dimensional fact is `Grid.image_rev_cIoo`, that reversing a clockwise open arc
gives the opposite clockwise arc with reversed endpoints.

Unlike the diagonal reflection, the rotation of a grid state is not definitionally involutive,
so the rotation of oriented rectangles is packaged as an explicit pair of mutually inverse maps
`GridRectangleBetween.rotate` and `GridRectangleBetween.rotateInv` rather than a single
`transpose`-style self-inverse. The rectangle-count symmetry is then a `Finset.card_nbij'`
bijection, and the chain relabeling `GridChain.rotateEquiv` reuses the (provable) involution of
`GridState.rotate`.

## Main definitions

* `TauCeti.GridRectangle.rotate`: the half-turn rotation of a toroidal rectangle.
* `TauCeti.GridRectangleBetween.rotate`, `TauCeti.GridRectangleBetween.rotateInv`: the half-turn
  rotation of an oriented rectangle and its inverse.
* `TauCeti.GridChain.rotateEquiv`: the linear automorphism of grid chains relabeling each
  generator by the half-turn rotation of grid states.

## Main results

* `TauCeti.GridDiagram.fullyBlockedRectangleCount_rotate`: the fully blocked rectangle count is
  invariant under the half-turn rotation of a grid diagram and its two states.
* `TauCeti.GridDiagram.fullyBlockedDifferential_rotate`: the fully blocked grid differential
  commutes with the rotation chain relabeling, intertwining the differentials of `G` and
  `G.rotate`; this is the chain symmetry of the half-turn rotation.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8
("Symmetries and the genus bound"), together with that roadmap's standing convention to "state
invariance naturality-ready". It is the rotation counterpart of the diagonal-reflection chain
symmetry in `DifferentialSymmetry.lean`. The grid symmetries follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

variable {n : ℕ}

namespace Grid

/-- Reversing every point of a clockwise open cyclic interval turns it into the opposite
clockwise open interval with the endpoints reversed: the coordinate reversal `Fin.rev` flips the
toroidal cyclic order. -/
theorem mem_cIoo_rev (a b x : Fin n) :
    x.rev ∈ Grid.cIoo b.rev a.rev ↔ x ∈ Grid.cIoo a b := by
  have ha := a.isLt
  have hb := b.isLt
  have hx := x.isLt
  simp only [Grid.mem_cIoo, Fin.val_rev, ne_eq, Fin.rev_inj]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun hh => hne hh.symm, by split_ifs at h ⊢ <;> omega⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun hh => hne hh.symm, by split_ifs at h ⊢ <;> omega⟩

/-- Reversing a clockwise open cyclic interval gives the opposite interval with reversed
endpoints. -/
theorem image_rev_cIoo (a b : Fin n) :
    (Grid.cIoo a b).image Fin.rev = Grid.cIoo b.rev a.rev := by
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_cIoo_rev a b x).mpr hx
  · intro hy
    exact ⟨y.rev, (mem_cIoo_rev a b y.rev).mp (by rwa [Fin.rev_rev]), Fin.rev_rev y⟩

end Grid

/-- The half-turn rotation of `Prod.map Fin.rev Fin.rev` is injective. -/
private theorem prodMapRev_injective :
    Function.Injective (Prod.map (Fin.rev : Fin n → Fin n) (Fin.rev : Fin n → Fin n)) :=
  Fin.rev_injective.prodMap Fin.rev_injective

namespace GridRectangle

variable (R : GridRectangle n)

/-- The half-turn rotation of a toroidal rectangle, reversing both coordinates.

Because the `180°` rotation reverses the cyclic order, the new side columns are the two original
side columns reversed *and swapped*, and likewise for the rows. -/
def rotate : GridRectangle n where
  left := R.right.rev
  right := R.left.rev
  bottom := R.top.rev
  top := R.bottom.rev

/-- The rotated rectangle's left side is the original right side reversed. -/
@[simp]
theorem rotate_left : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated rectangle's right side is the original left side reversed. -/
@[simp]
theorem rotate_right : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated rectangle's bottom side is the original top side reversed. -/
@[simp]
theorem rotate_bottom : R.rotate.bottom = R.top.rev :=
  rfl

/-- The rotated rectangle's top side is the original bottom side reversed. -/
@[simp]
theorem rotate_top : R.rotate.top = R.bottom.rev :=
  rfl

/-- The interior of the rotated rectangle is the half-turn rotation of the original interior. -/
theorem interior_rotate :
    R.rotate.interior = R.interior.image (Prod.map Fin.rev Fin.rev) := by
  have hcol : R.rotate.columnInterior = R.columnInterior.image Fin.rev := by
    simp only [GridRectangle.columnInterior, rotate_left, rotate_right]
    exact (Grid.image_rev_cIoo R.left R.right).symm
  have hrow : R.rotate.rowInterior = R.rowInterior.image Fin.rev := by
    simp only [GridRectangle.rowInterior, rotate_bottom, rotate_top]
    exact (Grid.image_rev_cIoo R.bottom R.top).symm
  simp only [GridRectangle.interior, hcol, hrow, Finset.prodMap_image_product]

end GridRectangle

namespace GridRectangleBetween

variable {x y : GridState n}

/-- The half-turn rotation of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.rotate` to `y.rotate`.

The `180°` rotation reverses the cyclic order, so the new side columns are the two original side
columns reversed and swapped: `R.left` and `R.right` become `R.right.rev` and `R.left.rev`. -/
def rotate (R : GridRectangleBetween x y) :
    GridRectangleBetween x.rotate y.rotate where
  left := R.right.rev
  right := R.left.rev
  left_ne_right := fun h => R.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    simp only [GridState.rotate_apply, Fin.rev_rev]
    exact congrArg Fin.rev R.map_right
  map_right := by
    simp only [GridState.rotate_apply, Fin.rev_rev]
    exact congrArg Fin.rev R.map_left
  map_of_ne c hl hr := by
    have hcl : c.rev ≠ R.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have hcr : c.rev ≠ R.right := fun h => hl (Fin.rev_eq_iff.mp h)
    simp only [GridState.rotate_apply]
    exact congrArg Fin.rev (R.map_of_ne c.rev hcl hcr)

/-- The rotated oriented rectangle's left side is the original right side reversed. -/
@[simp]
theorem rotate_left (R : GridRectangleBetween x y) : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated oriented rectangle's right side is the original left side reversed. -/
@[simp]
theorem rotate_right (R : GridRectangleBetween x y) : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated oriented rectangle's bottom side is the original top side reversed. -/
@[simp]
theorem rotate_bottom (R : GridRectangleBetween x y) : R.rotate.bottom = R.top.rev := by
  simp only [GridRectangleBetween.bottom, GridRectangleBetween.top, rotate_left,
    GridState.rotate_apply, Fin.rev_rev]

/-- The rotated oriented rectangle's top side is the original bottom side reversed. -/
@[simp]
theorem rotate_top (R : GridRectangleBetween x y) : R.rotate.top = R.bottom.rev := by
  simp only [GridRectangleBetween.top, GridRectangleBetween.bottom, rotate_right,
    GridState.rotate_apply, Fin.rev_rev]

/-- The toroidal rectangle of the rotated oriented rectangle is the rotation of the toroidal
rectangle of the original. -/
theorem rotate_toGridRectangle (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle = R.toGridRectangle.rotate := by
  change (⟨R.rotate.left, R.rotate.right, R.rotate.bottom, R.rotate.top⟩ : GridRectangle n) = _
  rw [rotate_bottom, rotate_top]
  rfl

/-- The interior of the rotated rectangle is the half-turn rotation of the original interior. -/
theorem interior_rotate (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle.interior =
      R.toGridRectangle.interior.image (Prod.map Fin.rev Fin.rev) := by
  rw [rotate_toGridRectangle, GridRectangle.interior_rotate]

/-- Two oriented rectangles between the same states with equal side columns are equal. Adapted
from the private `GridRectangleBetween.eq_of_sides` in `Rectangle.lean`. -/
private theorem eq_of_sides {R S : GridRectangleBetween x y} (hleft : R.left = S.left)
    (hright : R.right = S.right) : R = S := by
  obtain ⟨_, _, _, _, _, _⟩ := R
  obtain ⟨_, _, _, _, _, _⟩ := S
  obtain rfl : _ = _ := hleft
  obtain rfl : _ = _ := hright
  rfl

/-- The inverse of the half-turn rotation: an oriented rectangle from `x.rotate` to `y.rotate`
becomes an oriented rectangle from `x` to `y`. It applies the same reverse-and-swap rule to the
side columns. -/
def rotateInv (S : GridRectangleBetween x.rotate y.rotate) : GridRectangleBetween x y where
  left := S.right.rev
  right := S.left.rev
  left_ne_right := fun h => S.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    have h := S.map_right
    simp only [GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_right := by
    have h := S.map_left
    simp only [GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_of_ne c hl hr := by
    have hcl : c.rev ≠ S.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have hcr : c.rev ≠ S.right := fun h => hl (Fin.rev_eq_iff.mp h)
    have h := S.map_of_ne c.rev hcl hcr
    simp only [GridState.rotate_apply, Fin.rev_rev] at h
    exact Fin.rev_injective h

/-- The inverse rotation undoes the rotation of an oriented rectangle. -/
@[simp]
theorem rotateInv_rotate (R : GridRectangleBetween x y) : R.rotate.rotateInv = R := by
  apply eq_of_sides <;> exact Fin.rev_rev _

/-- The rotation undoes the inverse rotation of an oriented rectangle. -/
@[simp]
theorem rotate_rotateInv (S : GridRectangleBetween x.rotate y.rotate) :
    S.rotateInv.rotate = S := by
  apply eq_of_sides <;> exact Fin.rev_rev _

/-- The half-turn rotation preserves emptiness of a rectangle between grid states. -/
theorem isEmpty_rotate (R : GridRectangleBetween x y) :
    R.rotate.IsEmpty ↔ R.IsEmpty := by
  unfold GridRectangleBetween.IsEmpty GridRectangle.IsEmptyFor
  rw [interior_rotate, GridState.rotate_pointSet, Finset.disjoint_image prodMapRev_injective]

/-- The half-turn rotation preserves marking avoidance of a rectangle between grid states. -/
theorem avoidsMarkings_rotate (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.rotate.AvoidsMarkings G.rotate ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings GridRectangle.AvoidsMarkings
  rw [interior_rotate, G.rotate_OSet, G.rotate_XSet, ← Finset.image_union,
    Finset.disjoint_image prodMapRev_injective]

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

/-- The `y`-coefficient of a rotated chain is the `y.rotate`-coefficient of the original chain. -/
@[simp]
theorem rotateEquiv_apply {R : Type*} [Semiring R] {n : ℕ} (f : GridChain R n)
    (y : GridState n) : rotateEquiv R n f y = f y.rotate := by
  unfold rotateEquiv
  rw [Finsupp.domLCongr_apply]
  exact Finsupp.equivMapDomain_apply _ _ _

end GridChain

namespace GridDiagram

variable (G : GridDiagram n)

/-- The fully blocked rectangle count is invariant under the half-turn rotation of a grid diagram
and its two states. This is the matrix-coefficient form of the statement that the half-turn
rotation is a chain symmetry of the fully blocked grid complex.

The bijection sends each fully blocked rectangle to its half-turn rotation, which is again empty
and marking-avoiding for the rotated diagram. -/
theorem fullyBlockedRectangleCount_rotate (x y : GridState n) :
    G.rotate.fullyBlockedRectangleCount x.rotate y.rotate =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def]
  congr 1
  refine (Finset.card_nbij' GridRectangleBetween.rotate GridRectangleBetween.rotateInv
    ?_ ?_ ?_ ?_).symm
  · intro R hR
    simp only [Finset.mem_coe, mem_fullyBlockedRectangles] at hR ⊢
    exact ⟨(GridRectangleBetween.isEmpty_rotate R).mpr hR.1,
      (GridRectangleBetween.avoidsMarkings_rotate G R).mpr hR.2⟩
  · intro S hS
    simp only [Finset.mem_coe, mem_fullyBlockedRectangles] at hS ⊢
    refine ⟨?_, ?_⟩
    · rw [← GridRectangleBetween.isEmpty_rotate S.rotateInv,
        GridRectangleBetween.rotate_rotateInv]
      exact hS.1
    · rw [← GridRectangleBetween.avoidsMarkings_rotate G S.rotateInv,
        GridRectangleBetween.rotate_rotateInv]
      exact hS.2
  · intro R _
    exact GridRectangleBetween.rotateInv_rotate R
  · intro S _
    exact GridRectangleBetween.rotate_rotateInv S

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
