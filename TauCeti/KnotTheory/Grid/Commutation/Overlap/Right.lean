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
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRightSecond_inj`: the
  second promotion determines the original decomposition.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_union_recutRightEqRightFirst`
  (and the `...Second` analogue): both promotions cover the original region.
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRightFirst_rectangle_geometry`
  (and the `...Second` analogue): the remaining rectangle's sides, rows, and column subinterval.
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
    first := GridPentagonBetween.ofRightEq
      (D.recutOfIsEmpty hone hrectangle hpentagon).first
      (hfirst.trans D.pentagon.right_eq)
      (D.turn_mem_recut_first_of_right_eq_right hcommon hone hrectangle hpentagon hfirst)
    second := (D.recutOfIsEmpty hone hrectangle hpentagon).second }

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
        first := GridPentagonBetween.ofRightEq
          (D.recutOfIsEmpty hone hrectangle hpentagon).first
          (hfirst.trans D.pentagon.right_eq)
          (D.turn_mem_recut_first_of_right_eq_right hcommon hone hrectangle hpentagon
            hfirst)
        second := (D.recutOfIsEmpty hone hrectangle hpentagon).second } := rfl

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
    first := (D.recutOfIsEmpty hone hrectangle hpentagon).first
    second := GridPentagonBetween.ofRightEq
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
        first := (D.recutOfIsEmpty hone hrectangle hpentagon).first
        second := GridPentagonBetween.ofRightEq
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

/-- The terminal-side second-rectangle promotion does not identify distinct terms: equality
of the promoted recuts is equivalent to equality of the original decompositions. -/
@[simp]
theorem recutRightEqRightSecond_inj
    (D E : GridRectanglePentagonDecomposition a s x z)
    (hcommonD : D.rectangle.right = D.pentagon.right)
    (hcommonE : E.rectangle.right = E.pentagon.right)
    (honeD : D.toRectangleDecomposition.HasOneCommonSide)
    (honeE : E.toRectangleDecomposition.HasOneCommonSide)
    (hrectangleD : D.rectangle.IsEmpty) (hpentagonD : D.pentagon.IsEmpty)
    (hrectangleE : E.rectangle.IsEmpty) (hpentagonE : E.pentagon.IsEmpty)
    (hsecondD : (D.recutOfIsEmpty honeD hrectangleD hpentagonD).second.right =
      D.pentagon.right)
    (hsecondE : (E.recutOfIsEmpty honeE hrectangleE hpentagonE).second.right =
      E.pentagon.right) :
    D.recutRightEqRightSecond hcommonD honeD hrectangleD hpentagonD hsecondD =
        E.recutRightEqRightSecond hcommonE honeE hrectangleE hpentagonE hsecondE ↔ D = E := by
  constructor
  · intro h
    have hD := D.isRecut_recutRightEqRightSecond
      hcommonD honeD hrectangleD hpentagonD hsecondD
    have hE := E.isRecut_recutRightEqRightSecond
      hcommonE honeE hrectangleE hpentagonE hsecondE
    rw [← h] at hE
    have hfirstD : D.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleD
    have hlastD : D.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonD
    have hfirstE : E.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleE
    have hlastE : E.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonE
    have hbackD := hD.symm honeD hfirstD hlastD
    have hbackE := hE.symm honeE hfirstE hlastE
    have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
      (D.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
    apply toRectangleDecomposition_injective
    exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
      hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE
  · rintro rfl
    rfl

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

/-- Geometry of the rectangle left after the first terminal-side recut: it keeps the
original rectangle's rows and occupies its initial column subinterval. -/
theorem recutRightEqRightFirst_rectangle_geometry
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    let E := D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
    E.rectangle.left = D.rectangle.left ∧
    E.rectangle.right = D.pentagon.left ∧
    E.rectangle.bottom = D.rectangle.bottom ∧
    E.rectangle.top = D.rectangle.top ∧
    E.rectangle.toGridRectangle.coveredColumns ⊆
      D.rectangle.toGridRectangle.coveredColumns ∧
    a ∉ E.rectangle.toGridRectangle.coveredColumns ∧
    a ∈ D.rectangle.toGridRectangle.coveredColumns := by
  let E := D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst
  obtain ⟨hcol, _, _⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hfirst
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  obtain ⟨_, hsecondLeft⟩ := hdata.recut_sides
  -- The first rectangle's terminal side forces the second alternative of the recut.
  have hbranch : (D.recutOfIsEmpty hone hrectangle hpentagon).middle =
      x.swapColumns D.pentagon.left D.rectangle.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.left := by
    rcases hdata.recut_branch with h | h
    · have hh := h.2.2.1
      rw [hfirst] at hh
      have hh' : D.rectangle.right = D.rectangle.left := by
        simpa only [toRectangleDecomposition_first_left, hcommon] using hh
      exact False.elim (D.rectangle.left_ne_right hh'.symm)
    · constructor
      · simpa only [toRectangleDecomposition_second_left,
          toRectangleDecomposition_first_right] using h.2.1
      · simpa only [toRectangleDecomposition_second_left] using h.2.2.2
  have hEleft : E.rectangle.left = D.rectangle.left := by
    exact (D.recutRightEqRightFirst_rectangle_left hcommon hone hrectangle hpentagon hfirst).trans
      (hsecondLeft.trans D.toRectangleDecomposition_first_left)
  have hEright : E.rectangle.right = D.pentagon.left :=
    (D.recutRightEqRightFirst_rectangle_right hcommon hone hrectangle hpentagon hfirst).trans
      hbranch.2
  -- Swapping the two side columns leaves these row endpoints unchanged.
  have hEbottom : E.rectangle.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, hEleft,
      D.recutRightEqRightFirst_middle hcommon hone hrectangle hpentagon hfirst,
      hbranch.1, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (Grid.ne_left_of_mem_cIoo hcol).symm
        D.rectangle.left_ne_right, ← GridRectangleBetween.bottom_def]
  have hEtop : E.rectangle.top = D.rectangle.top := by
    rw [GridRectangleBetween.top_def, hEright,
      D.recutRightEqRightFirst_middle hcommon hone hrectangle hpentagon hfirst,
      hbranch.1, GridState.swapColumns_apply, Equiv.swap_apply_left,
      ← GridRectangleBetween.top_def]
  have ha : a ∈ D.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hcommon, D.pentagon.right_eq]
    exact Grid.self_mem_cIco_finRotate (by
      intro h
      exact D.rectangle.left_ne_right ((h.trans D.pentagon.right_eq.symm).trans hcommon.symm))
  have haNot : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro haE
    have hcol' : D.pentagon.left ∈ Grid.cIoo D.rectangle.left (finRotate n a) := by
      simpa only [hcommon, D.pentagon.right_eq] using hcol
    have htail : a ∈ Grid.cIco D.pentagon.left (finRotate n a) :=
      Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol')
    exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')) haE htail
  -- The new column interval is the initial piece of the old interval.
  have hCols : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.rectangle.toGridRectangle.coveredColumns := by
    intro c hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright] at hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right]
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol]
    exact Finset.mem_union.mpr (Or.inl hc)
  exact ⟨hEleft, hEright, hEbottom, hEtop, hCols, haNot, ha⟩

/-- Geometry of the rectangle left after the second terminal-side recut: it occupies
an initial subinterval of the original pentagon's columns, away from the swapped columns. -/
theorem recutRightEqRightSecond_rectangle_geometry
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    let E := D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
    E.rectangle.left = D.pentagon.left ∧
    E.rectangle.right = D.rectangle.left ∧
    E.rectangle.bottom = D.pentagon.bottom ∧
    E.rectangle.top = D.pentagon.top ∧
    E.rectangle.toGridRectangle.coveredColumns ⊆
      D.pentagon.toGridRectangle.coveredColumns ∧
    a ∉ E.rectangle.toGridRectangle.coveredColumns ∧
    finRotate n a ∉ E.rectangle.toGridRectangle.coveredColumns := by
  let E := D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond
  obtain ⟨hcol, _, _, _⟩ :=
    D.second_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hsecond
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hEleft : E.rectangle.left = D.pentagon.left :=
    (D.recutRightEqRightSecond_rectangle_left hcommon hone hrectangle hpentagon hsecond).trans
      (hdata.recut_sides.1.trans D.toRectangleDecomposition_second_left)
  -- Here the second rectangle carries the common side, forcing the first recut branch.
  have hfirstRight : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.rectangle.left := by
    rcases hdata.recut_branch with h | h
    · simpa only [toRectangleDecomposition_first_left] using h.2.2.1
    · have hh : D.pentagon.right = D.pentagon.left := by
        simpa only [toRectangleDecomposition_second_left] using hsecond.symm.trans h.2.2.2
      exact False.elim (D.pentagon.left_ne_right hh.symm)
  have hEright : E.rectangle.right = D.rectangle.left :=
    (D.recutRightEqRightSecond_rectangle_right hcommon hone hrectangle hpentagon hsecond).trans
      hfirstRight
  -- Identify the pentagon's rows in the source state to compare the rectangles.
  have hPbottom : D.pentagon.bottom = x D.pentagon.left := by
    rw [GridRectangleBetween.bottom_def]
    exact D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol).symm
      (fun h => D.pentagon.left_ne_right (h.trans hcommon))
  have hPtop : D.pentagon.top = x D.rectangle.left := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_right,
      ← GridRectangleBetween.bottom_def]
  have hEbottom : E.rectangle.bottom = D.pentagon.bottom := by
    rw [GridRectangleBetween.bottom_def, hEleft, ← hPbottom]
  have hEtop : E.rectangle.top = D.pentagon.top := by
    rw [GridRectangleBetween.top_def, hEright, ← hPtop]
  have hcol' : D.rectangle.left ∈ Grid.cIoo D.pentagon.left (finRotate n a) := by
    simpa only [hcommon, D.pentagon.right_eq] using hcol
  have haNot : a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro haE
    have htail : a ∈ Grid.cIco D.rectangle.left (finRotate n a) :=
      Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol')
    exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')) haE htail
  have hbNot : finRotate n a ∉ E.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright]
    intro hb
    exact Grid.right_notMem_cIco D.pentagon.left (finRotate n a)
      (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hb hcol')
  -- Both swapped columns lie beyond this initial piece of the pentagon's interval.
  have hCols : E.rectangle.toGridRectangle.coveredColumns ⊆
      D.pentagon.toGridRectangle.coveredColumns := by
    intro c hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hEleft, hEright] at hc
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, D.pentagon.right_eq]
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol']
    exact Finset.mem_union.mpr (Or.inl hc)
  exact ⟨hEleft, hEright, hEbottom, hEtop, hCols, haNot, hbNot⟩

end GridRectanglePentagonDecomposition

end TauCeti
