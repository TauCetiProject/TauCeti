/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic
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
  `..._pentagon_left`, `..._pentagon_bottom`, `..._pentagon_top` (and the `...Second`
  analogues): the promoted components in terms of the underlying recut, so consumers never
  unfold the definitions.
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
* `middle`: the middle rectangle of the underlying recut
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

/-- The middle rectangle of the first promotion is the middle rectangle of the underlying
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

/-- Recut a rectangle followed by a pentagon when their unique common side is terminal for
both, then promote the second new rectangle to a pentagon. This applies when the second recut
rectangle inherits the original pentagon's terminal side; the turn-row membership is derived
from the common-terminal-side geometry via `turn_mem_recut_second_of_right_eq_right`.
The result is a rectangle--pentagon decomposition.

The result is a `GridRectanglePentagonDecomposition` with:
* `middle`: the middle rectangle of the underlying recut
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

/-- The middle rectangle of the second promotion is the middle rectangle of the underlying
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

end GridRectanglePentagonDecomposition

end TauCeti
