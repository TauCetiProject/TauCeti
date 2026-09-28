/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.TurnRow

/-!
# Terminal-side overlap promotion for the grid commutation map

This file constructs the pentagon--rectangle (and rectangle--pentagon) promotions for the
common-terminal-side overlap orientation, complementing the common-initial-side promotion
`TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft` in
`TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic`.

When the rectangle and pentagon share their terminal side, the generic recut places the
original pentagon's terminal side on exactly one of its two new rectangles
(`recut_first_or_second_right_eq_pentagon_right`). Whichever rectangle inherits that side
promotes to a pentagon via `GridPentagonBetween.ofRightEq`, once the turn row is transported
to its row interval.

The two subcases give different decomposition shapes:
* if the first recut rectangle inherits the terminal side, promoting it yields a
  pentagon--rectangle decomposition (`recutRightEqRightFirst`);
* if the second recut rectangle inherits the terminal side, promoting it yields a
  rectangle--pentagon decomposition (`recutRightEqRightSecond`).

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRightFirst`: promote the
  terminal-side recut to a pentagon--rectangle decomposition when the first new rectangle
  carries the original pentagon's terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRightSecond`: promote the
  terminal-side recut to a rectangle--pentagon decomposition when the second new rectangle
  carries the original pentagon's terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRightFirst_middle`,
  `..._rectangle_left`, `..._rectangle_right`, `..._rectangle_bottom`, `..._rectangle_top`,
  `..._pentagon_left`, `..._pentagon_right`, `..._pentagon_bottom`, `..._pentagon_top`,
  `..._pentagon_toGridRectangle`
  (and the `...Second` analogues): the promoted components in terms of
  the underlying recut, so consumers never unfold the definitions. The
  `..._pentagon_toGridRectangle` lemmas give the promoted pentagon's underlying
  rectangle geometry for region and avoidance arguments.
* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutRightEqRightFirst`
  (and the `...Second` analogue): both promotions retain the recut relation after
  forgetting the pentagon turn row.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_union_recutRightEqRightFirst`
  (and the `...Second` analogue): both promotions cover the original region.
* `TauCeti.GridRectanglePentagonDecomposition.OMonomial_mul_OMonomial_recutRightEqRightFirst`
  (and the `...Second` analogue): both promotions preserve the product of the underlying
  rectangle `O`-monomials.

The juxtaposition argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1. The monomial identities concern the underlying rectangles; pentagon
weights also account for the two columns next to the commuted grid line.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recut a rectangle followed by a pentagon when their unique common side is terminal for
both, then promote the first new rectangle to a pentagon. This applies when the first recut
rectangle inherits the original pentagon's terminal side; the turn-row membership is derived
from the common-terminal-side geometry via `turn_mem_recut_first_of_right_eq_right`.

The result is a `GridPentagonRectangleDecomposition` with:
* `middle`: the middle grid state of the underlying recut (the intermediate state where
  the two domains meet)
* `pentagon`: the first recut rectangle promoted to a pentagon via `GridPentagonBetween.ofRightEq`
* `rectangle`: the second recut rectangle

Use the characterization lemmas below (for example `.middle`) to access the components in
terms of the underlying recut. -/
noncomputable def recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    GridPentagonRectangleDecomposition a s x z :=
  { middle := (D.recutOfIsEmpty hone hrectangle hpentagon).middle
    pentagon := GridPentagonBetween.ofRightEq
      (D.recutOfIsEmpty hone hrectangle hpentagon).first
      (hfirst.trans D.pentagon.right_eq)
      (D.turn_mem_recut_first_of_right_eq_right hcommon hone hrectangle hpentagon hfirst)
    rectangle := (D.recutOfIsEmpty hone hrectangle hpentagon).second }

/-- Unfolding of `recutRightEqRightFirst`. This is the private `rfl` core of the
characterization lemmas below: since the definition is not `@[expose]`d, an exported proof
may not unfold its body, so the exported characterizations rewrite with this private
unfolding instead. -/
private theorem recutRightEqRightFirst_unfold
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst =
      { middle := (D.recutOfIsEmpty hone hrectangle hpentagon).middle
        pentagon := GridPentagonBetween.ofRightEq
          (D.recutOfIsEmpty hone hrectangle hpentagon).first
          (hfirst.trans D.pentagon.right_eq)
          (D.turn_mem_recut_first_of_right_eq_right hcommon hone hrectangle hpentagon
            hfirst)
        rectangle := (D.recutOfIsEmpty hone hrectangle hpentagon).second } := rfl

/-- The middle grid state of the first promotion is the middle grid state of the underlying
recut. -/
@[simp]
theorem recutRightEqRightFirst_middle
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).middle =
      (D.recutOfIsEmpty hone hrectangle hpentagon).middle := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]

/-- The initial side of the first promotion's rectangle is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_rectangle_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).rectangle.left =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.left := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]

/-- The terminal side of the first promotion's rectangle is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_rectangle_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).rectangle.right =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.right := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]

/-- The promoted pentagon's initial side is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_pentagon_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.left =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.left := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]
  exact GridPentagonBetween.ofRightEq_left _ _ _

/-- The promoted pentagon's bottom row is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_pentagon_bottom
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.bottom =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]
  exact GridPentagonBetween.ofRightEq_bottom _ _ _

/-- The promoted pentagon's top row is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_pentagon_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.top =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.top := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]
  exact GridPentagonBetween.ofRightEq_top _ _ _

/-- The bottom row of the first promotion's rectangle is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_rectangle_bottom
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).rectangle.bottom =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.bottom := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]

/-- The top row of the first promotion's rectangle is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightFirst_rectangle_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).rectangle.top =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.top := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]

/-- The promoted pentagon's terminal side is the grid line replaced by `γ`. -/
@[simp]
theorem recutRightEqRightFirst_pentagon_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.right =
      finRotate n a := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]
  exact GridPentagonBetween.ofRightEq_right _ _ _

/-- The rectangle underlying the promoted pentagon of the first promotion is the first
recut rectangle. This is the promoted pentagon's underlying rectangle geometry, for use in
region and avoidance arguments. -/
@[simp]
theorem recutRightEqRightFirst_pentagon_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.toGridRectangle =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.toGridRectangle := by
  rw [D.recutRightEqRightFirst_unfold hcommon hone hrectangle hpentagon hfirst]
  exact congrArg GridRectangleBetween.toGridRectangle
    (GridPentagonBetween.ofRightEq_toGridRectangleBetween _ _ _)

/-- Recut a rectangle followed by a pentagon when their unique common side is terminal for
both, then promote the second new rectangle to a pentagon. This applies when the second recut
rectangle inherits the original pentagon's terminal side; the turn-row membership is derived
from the common-terminal-side geometry via `turn_mem_recut_second_of_right_eq_right`.
The result is a rectangle--pentagon decomposition.

The result is a `GridRectanglePentagonDecomposition` with:
* `middle`: the middle grid state of the underlying recut (the intermediate state where
  the two domains meet)
* `rectangle`: the first recut rectangle
* `pentagon`: the second recut rectangle promoted to a pentagon via `GridPentagonBetween.ofRightEq`

Use the characterization lemmas below (for example `.middle`) to access the components in
terms of the underlying recut. -/
noncomputable def recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    GridRectanglePentagonDecomposition a s x z :=
  { middle := (D.recutOfIsEmpty hone hrectangle hpentagon).middle
    rectangle := (D.recutOfIsEmpty hone hrectangle hpentagon).first
    pentagon := GridPentagonBetween.ofRightEq
      (D.recutOfIsEmpty hone hrectangle hpentagon).second
      (hsecond.trans D.pentagon.right_eq)
      (D.turn_mem_recut_second_of_right_eq_right hcommon hone hrectangle hpentagon hsecond) }

/-- Unfolding of `recutRightEqRightSecond`. This is the private `rfl` core of the
characterization lemmas below: since the definition is not `@[expose]`d, an exported proof
may not unfold its body, so the exported characterizations rewrite with this private
unfolding instead. -/
private theorem recutRightEqRightSecond_unfold
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond =
      { middle := (D.recutOfIsEmpty hone hrectangle hpentagon).middle
        rectangle := (D.recutOfIsEmpty hone hrectangle hpentagon).first
        pentagon := GridPentagonBetween.ofRightEq
          (D.recutOfIsEmpty hone hrectangle hpentagon).second
          (hsecond.trans D.pentagon.right_eq)
          (D.turn_mem_recut_second_of_right_eq_right hcommon hone hrectangle hpentagon
            hsecond) } := rfl

/-- The middle grid state of the second promotion is the middle grid state of the underlying
recut. -/
@[simp]
theorem recutRightEqRightSecond_middle
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).middle =
      (D.recutOfIsEmpty hone hrectangle hpentagon).middle := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]

/-- The initial side of the second promotion's rectangle is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_rectangle_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).rectangle.left =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.left := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]

/-- The terminal side of the second promotion's rectangle is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_rectangle_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).rectangle.right =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.right := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]

/-- The promoted pentagon's initial side is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_pentagon_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.left =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.left := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]
  exact GridPentagonBetween.ofRightEq_left _ _ _

/-- The promoted pentagon's bottom row is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_pentagon_bottom
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.bottom =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.bottom := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]
  exact GridPentagonBetween.ofRightEq_bottom _ _ _

/-- The promoted pentagon's top row is the second recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_pentagon_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.top =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.top := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]
  exact GridPentagonBetween.ofRightEq_top _ _ _

/-- The bottom row of the second promotion's rectangle is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_rectangle_bottom
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).rectangle.bottom =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]

/-- The top row of the second promotion's rectangle is the first recut rectangle's. -/
@[simp]
theorem recutRightEqRightSecond_rectangle_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).rectangle.top =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.top := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]

/-- The promoted pentagon's terminal side is the grid line replaced by `γ`. -/
@[simp]
theorem recutRightEqRightSecond_pentagon_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.right =
      finRotate n a := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]
  exact GridPentagonBetween.ofRightEq_right _ _ _

/-- The rectangle underlying the promoted pentagon of the second promotion is the second
recut rectangle. This is the promoted pentagon's underlying rectangle geometry, for use in
region and avoidance arguments. -/
@[simp]
theorem recutRightEqRightSecond_pentagon_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.toGridRectangle =
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.toGridRectangle := by
  rw [D.recutRightEqRightSecond_unfold hcommon hone hrectangle hpentagon hsecond]
  exact congrArg GridRectangleBetween.toGridRectangle
    (GridPentagonBetween.ofRightEq_toGridRectangleBetween _ _ _)

/-- Forgetting the turn row after the first terminal-side promotion gives the ordinary recut. -/
@[simp]
theorem recutRightEqRightFirst_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).toRectangleDecomposition =
      D.recutOfIsEmpty hone hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp
  · simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      recutRightEqRightFirst_pentagon_right] using
      (hfirst.trans D.pentagon.right_eq).symm
  · simp
  · simp

/-- The promoted first-branch decomposition is a genuine recut of the original two rectangles. -/
theorem isRecut_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    D.toRectangleDecomposition.IsRecut
      (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).toRectangleDecomposition := by
  rw [D.recutRightEqRightFirst_toRectangleDecomposition hcommon hone hrectangle hpentagon hfirst]
  exact D.isRecut_recutOfIsEmpty hone hrectangle hpentagon

/-- The pentagon promoted from the first recut rectangle remains empty. -/
@[simp]
theorem isEmpty_pentagon_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.IsEmpty := by
  have h := D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  exact
    (D.recutRightEqRightFirst hcommon hone
      hrectangle hpentagon hfirst).isEmpty_pentagon_of_isRecut
      h

/-- The rectangle left after promoting the first recut rectangle remains empty. -/
@[simp]
theorem isEmpty_rectangle_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.IsEmpty := by
  have h := D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  exact
    (D.recutRightEqRightFirst hcommon hone
      hrectangle hpentagon hfirst).isEmpty_rectangle_of_isRecut
      h

/-- The two underlying rectangles of the first promotion cover precisely the original region. -/
theorem coveredSquares_union_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.toGridRectangle.coveredSquares ∪
      (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.toGridRectangle.coveredSquares =
        D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  exact
    (D.recutRightEqRightFirst hcommon hone
      hrectangle hpentagon hfirst).coveredSquares_union_of_isRepartition D
      h.isRepartition

/-- Repartition preserves the product of the `O`-monomials of the underlying rectangles. -/
theorem OMonomial_mul_OMonomial_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
        (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.toGridRectangle *
      G.OMonomial R
        (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.toGridRectangle =
        G.OMonomial R D.rectangle.toGridRectangle *
          G.OMonomial R D.pentagon.toGridRectangle := by
  have h := D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  exact
    (D.recutRightEqRightFirst hcommon hone
      hrectangle hpentagon hfirst).OMonomial_mul_OMonomial_of_isRepartition D
      h.isRepartition G R

/-- Forgetting the turn row after the second terminal-side promotion gives the ordinary recut. -/
@[simp]
theorem recutRightEqRightSecond_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).toRectangleDecomposition =
      D.recutOfIsEmpty hone hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp
  · simp
  · simp
  · simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      recutRightEqRightSecond_pentagon_right] using
      (hsecond.trans D.pentagon.right_eq).symm

/-- The promoted second-branch decomposition is a genuine recut of the original rectangles. -/
theorem isRecut_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    D.toRectangleDecomposition.IsRecut
      (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).toRectangleDecomposition := by
  rw [D.recutRightEqRightSecond_toRectangleDecomposition hcommon hone hrectangle hpentagon hsecond]
  exact D.isRecut_recutOfIsEmpty hone hrectangle hpentagon

/-- The first rectangle in the second-branch promotion remains empty. -/
@[simp]
theorem isEmpty_rectangle_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.IsEmpty := by
  have h := D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  exact
    (D.recutRightEqRightSecond hcommon hone
      hrectangle hpentagon hsecond).isEmpty_rectangle_of_isRecut
      h

/-- The pentagon promoted from the second recut rectangle remains empty. -/
@[simp]
theorem isEmpty_pentagon_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.IsEmpty := by
  have h := D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  exact
    (D.recutRightEqRightSecond hcommon hone
      hrectangle hpentagon hsecond).isEmpty_pentagon_of_isRecut
      h

/-- The two underlying rectangles of the second promotion cover precisely the original region. -/
theorem coveredSquares_union_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.toGridRectangle.coveredSquares ∪
      (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.toGridRectangle.coveredSquares =
        D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  exact
    (D.recutRightEqRightSecond hcommon hone
      hrectangle hpentagon hsecond).coveredSquares_union_of_isRepartition D
      h.isRepartition

/-- Repartition preserves the product of the `O`-monomials of the underlying rectangles. -/
theorem OMonomial_mul_OMonomial_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
        (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.toGridRectangle *
      G.OMonomial R
        (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.toGridRectangle =
        G.OMonomial R D.rectangle.toGridRectangle *
          G.OMonomial R D.pentagon.toGridRectangle := by
  have h := D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  exact
    (D.recutRightEqRightSecond hcommon hone
      hrectangle hpentagon hsecond).OMonomial_mul_OMonomial_of_isRepartition D
      h.isRepartition G R

end GridRectanglePentagonDecomposition

end TauCeti
