/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.GradingInteger

/-!
# The half-turn rotation symmetry of grid states and diagrams

This file adds the `180°` rotation of the toroidal grid to the grid-combinatorial lane of the
Heegaard Floer roadmap, alongside the already-developed diagonal reflection (`transpose`) and
marking swap (`swapMarkings`). Rotation reverses both the column and the row coordinate, so on
grid squares it is the map `(c, r) ↦ (cᵒ, rᵒ)` with `·ᵒ = Fin.rev`. It carries a grid state to a
grid state, a grid diagram to a grid diagram, and -- crucially -- it preserves all of the Maslov
and Alexander gradings.

The reason rotation preserves the gradings while a single-axis reflection does not is exactly
that it reverses *both* coordinates at once: the strict southwest relation underlying the
`J`-function is sent to itself with its two endpoints exchanged, so the symmetrized point-pair
counts `I`, `JNum`, `J`, and their formal-difference extension `JDiff` are all unchanged. This is
the structural analogue of `GridPoint.I_image_swap` for the diagonal reflection, where reflection
across the main diagonal exchanges the two coordinates instead of reversing them.

## Main definitions

* `TauCeti.GridState.rotate`: the half-turn rotation of a grid state.
* `TauCeti.GridDiagram.rotate`: the half-turn rotation of a grid diagram.

## Main results

* `TauCeti.GridPoint.I_image_rev`, `TauCeti.GridPoint.J_image_rev`,
  `TauCeti.GridPoint.JDiff_image_rev`: the southwest counts and the `J`-function are invariant
  under reversing both coordinates of the point sets.
* `TauCeti.GridState.rotate_rotate`, `TauCeti.GridDiagram.rotate_rotate`: rotation is an
  involution on grid states and grid diagrams.
* `TauCeti.GridDiagram.maslovO_rotate`, `TauCeti.GridDiagram.maslovX_rotate`,
  `TauCeti.GridDiagram.alexander_rotate`: the Maslov and Alexander gradings are invariant under
  the half-turn rotation.
* `TauCeti.GridDiagram.maslovOℤ_rotate`, `TauCeti.GridDiagram.maslovXℤ_rotate`,
  `TauCeti.GridDiagram.alexanderTwoℤ_rotate`: the integer-valued gradings are likewise invariant.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a
rectangle", supplying a grading-preserving symmetry of the kind anticipated by the "Symmetries
and the genus bound" milestone (Lane G item 8). The half-turn rotation of a grid diagram is one
of the standard grid symmetries of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- Reversing both coordinates of both points of a pair exchanges the two endpoints of the strict
southwest relation: it sends the column and row comparisons to their reverses. -/
@[simp]
theorem isSouthWest_rev (p q : Fin n × Fin n) :
    IsSouthWest (Prod.map Fin.rev Fin.rev p) (Prod.map Fin.rev Fin.rev q) ↔ IsSouthWest q p := by
  simp only [IsSouthWest, Prod.map_fst, Prod.map_snd]
  have h1 := p.1.isLt
  have h2 := q.1.isLt
  have h3 := p.2.isLt
  have h4 := q.2.isLt
  rw [Fin.val_rev, Fin.val_rev, Fin.val_rev, Fin.val_rev]
  omega

/-- The coordinate-reversal map on grid squares is injective. -/
private theorem prodMap_rev_injective :
    Function.Injective (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n))) :=
  Fin.rev_injective.prodMap Fin.rev_injective

/-- The coordinate-reversal map on pairs of grid squares is injective. -/
private theorem prodMap_prodMap_rev_injective :
    Function.Injective
      (Prod.map (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n)))
        (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n)))) :=
  prodMap_rev_injective.prodMap prodMap_rev_injective

/-- The ordered southwest count is invariant, up to exchanging the two point sets, under reversing
both coordinates of both point sets. The reversal turns each southwest comparison into the
opposite comparison, so the count of southwest pairs from `s` to `t` becomes the count from `t`
to `s`. -/
theorem I_image_rev (s t : Finset (Fin n × Fin n)) :
    I (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev)) = I t s := by
  classical
  rw [I_def, ← Finset.prodMap_image_product (Prod.map Fin.rev Fin.rev)
      (Prod.map Fin.rev Fin.rev) s t, Finset.filter_image,
    Finset.card_image_of_injective _ prodMap_prodMap_rev_injective]
  rw [I_def, ← Finset.image_swap_product t s, Finset.filter_image,
    Finset.card_image_of_injective _ Prod.swap_injective]
  refine congrArg Finset.card (Finset.filter_congr fun pq _ => ?_)
  simpa using isSouthWest_rev pq.1 pq.2

/-- The numerator of the `J`-function is invariant under reversing both coordinates of both point
sets. The two ordered counts are exchanged by the reversal, and their sum is symmetric. -/
theorem JNum_image_rev (s t : Finset (Fin n × Fin n)) :
    JNum (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev)) = JNum s t := by
  rw [JNum_def, JNum_def, I_image_rev, I_image_rev, Nat.add_comm]

/-- The symmetrized grid `J`-function is invariant under reversing both coordinates of both point
sets. -/
theorem J_image_rev (s t : Finset (Fin n × Fin n)) :
    GridPoint.J (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev))
      = GridPoint.J s t := by
  rw [J_def, J_def, JNum_image_rev]

/-- The bilinear `J`-function on formal differences is invariant under reversing both coordinates
of all four point sets. -/
theorem JDiff_image_rev (s a t b : Finset (Fin n × Fin n)) :
    JDiff (s.image (Prod.map Fin.rev Fin.rev)) (a.image (Prod.map Fin.rev Fin.rev))
        (t.image (Prod.map Fin.rev Fin.rev)) (b.image (Prod.map Fin.rev Fin.rev))
      = JDiff s a t b := by
  rw [JDiff_def, JDiff_def, J_image_rev, J_image_rev, J_image_rev, J_image_rev]

end GridPoint

namespace GridState

variable {n : ℕ}

/-- Reversing both coordinates of a grid square twice returns the original square. -/
private theorem rev2_rev2 (p : Fin n × Fin n) :
    Prod.map Fin.rev Fin.rev (Prod.map Fin.rev Fin.rev p) = p := by
  obtain ⟨a, b⟩ := p
  change (Fin.rev (Fin.rev a), Fin.rev (Fin.rev b)) = (a, b)
  rw [Fin.rev_rev, Fin.rev_rev]

/-- The half-turn rotation of a grid state.

Rotating the occupied squares by `180°` reverses both the column and the row coordinate, so the
new permutation graph conjugates the old one by the coordinate reversal `Fin.revPerm`. -/
def rotate (x : GridState n) : GridState n where
  toPerm := Fin.revPerm.trans (x.toPerm.trans Fin.revPerm)

/-- The rotated state reads off a column by reversing it, applying the original state, and
reversing the resulting row. -/
@[simp]
theorem rotate_apply (x : GridState n) (c : Fin n) :
    x.rotate c = (x (Fin.rev c)).rev := by
  simp [rotate, Equiv.trans_apply]

/-- A square lies in the rotated state exactly when its half-turn rotation lies in the original
state. -/
@[simp]
theorem mem_pointSet_rotate (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.rotate.pointSet ↔ Prod.map Fin.rev Fin.rev p ∈ x.pointSet := by
  simp only [mem_pointSet, rotate_apply, Prod.map_fst, Prod.map_snd, Fin.rev_eq_iff]

/-- The point set of the rotated state is the half-turn rotation of the original point set. -/
theorem rotate_pointSet (x : GridState n) :
    x.rotate.pointSet = x.pointSet.image (Prod.map Fin.rev Fin.rev) := by
  ext p
  rw [mem_pointSet_rotate, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨Prod.map Fin.rev Fin.rev p, hp, rev2_rev2 p⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [rev2_rev2 q]

/-- The half-turn rotation is an involution on grid states. -/
@[simp]
theorem rotate_rotate (x : GridState n) : x.rotate.rotate = x := by
  ext c
  simp [Fin.rev_rev]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The half-turn rotation of a grid diagram, rotating both marking states.

The rotation is injective on squares, so it preserves the condition that no square carries both an
`O` and an `X` marking. -/
def rotate (G : GridDiagram n) : GridDiagram n where
  O := G.O.rotate
  X := G.X.rotate
  disjoint c := by
    simp only [GridState.rotate_apply]
    exact fun h => G.disjoint (Fin.rev c) (Fin.rev_injective h)

/-- The `O`-marking state of the rotated diagram is the rotation of the original `O`-state. -/
@[simp]
theorem rotate_O : G.rotate.O = G.O.rotate :=
  rfl

/-- The `X`-marking state of the rotated diagram is the rotation of the original `X`-state. -/
@[simp]
theorem rotate_X : G.rotate.X = G.X.rotate :=
  rfl

/-- The `O`-markings of the rotated diagram are the half-turn rotation of the original
`O`-markings. -/
theorem rotate_OSet : G.rotate.OSet = G.OSet.image (Prod.map Fin.rev Fin.rev) :=
  GridState.rotate_pointSet G.O

/-- The `X`-markings of the rotated diagram are the half-turn rotation of the original
`X`-markings. -/
theorem rotate_XSet : G.rotate.XSet = G.XSet.image (Prod.map Fin.rev Fin.rev) :=
  GridState.rotate_pointSet G.X

/-- The half-turn rotation is an involution on grid diagrams. -/
@[simp]
theorem rotate_rotate : G.rotate.rotate = G := by
  cases G
  simp only [rotate, GridState.rotate_rotate]

/-- The `O`-Maslov grading is invariant under the half-turn rotation. -/
@[simp]
theorem maslovO_rotate (x : GridState n) :
    G.rotate.maslovO x.rotate = G.maslovO x := by
  rw [maslovO_def, maslovO_def, GridState.rotate_pointSet, rotate_OSet, GridPoint.JDiff_image_rev]

/-- The `X`-Maslov grading is invariant under the half-turn rotation. -/
@[simp]
theorem maslovX_rotate (x : GridState n) :
    G.rotate.maslovX x.rotate = G.maslovX x := by
  rw [maslovX_def, maslovX_def, GridState.rotate_pointSet, rotate_XSet, GridPoint.JDiff_image_rev]

/-- The Alexander grading is invariant under the half-turn rotation. The normalization shift
depends only on the common grid size, so it is untouched. -/
@[simp]
theorem alexander_rotate (x : GridState n) :
    G.rotate.alexander x.rotate = G.alexander x := by
  rw [alexander_def, alexander_def, maslovO_rotate, maslovX_rotate]

/-- The integer-valued `O`-Maslov grading is invariant under the half-turn rotation. -/
@[simp]
theorem maslovOℤ_rotate (x : GridState n) :
    G.rotate.maslovOℤ x.rotate = G.maslovOℤ x := by
  rw [maslovOℤ_def, maslovOℤ_def, GridState.rotate_pointSet, rotate_OSet,
    GridPoint.I_image_rev, GridPoint.JNum_image_rev, GridPoint.I_image_rev]

/-- The integer-valued `X`-Maslov grading is invariant under the half-turn rotation. -/
@[simp]
theorem maslovXℤ_rotate (x : GridState n) :
    G.rotate.maslovXℤ x.rotate = G.maslovXℤ x := by
  rw [maslovXℤ_def, maslovXℤ_def, GridState.rotate_pointSet, rotate_XSet,
    GridPoint.I_image_rev, GridPoint.JNum_image_rev, GridPoint.I_image_rev]

/-- The integer numerator of twice the Alexander grading is invariant under the half-turn
rotation. -/
@[simp]
theorem alexanderTwoℤ_rotate (x : GridState n) :
    G.rotate.alexanderTwoℤ x.rotate = G.alexanderTwoℤ x := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_rotate, maslovXℤ_rotate]

end GridDiagram

end TauCeti
