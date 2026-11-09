/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.StrictInitial

/-!
# Objects over a strict initial object are terminal

If `C` has strict initial objects and `X` is initial, Mathlib identifies `Over X` with a point
(`CategoryTheory.overEquivOfIsInitial`). This file records the consequence that every object of
`Over X` is terminal, so any two parallel morphisms in `Over X` are equal. For schemes, apply it
to `AlgebraicGeometry.isInitialOfIsEmpty`: over an empty base scheme every object of the slice
category is terminal.

## Main declarations

* `CategoryTheory.Over.isTerminalOfIsInitial`: every object of `Over X` is terminal when `X` is
  a strict initial object.
-/

public section

namespace CategoryTheory.Over

open Limits

variable {C : Type*} [Category* C] [HasStrictInitialObjects C] {X : C}

/-- If `C` has strict initial objects and `X` is initial, every object of `Over X` is terminal:
its structure morphism is an isomorphism, identifying it with `Over.mk (𝟙 X)`. -/
noncomputable def isTerminalOfIsInitial (h : IsInitial X) (A : Over X) : IsTerminal A :=
  mkIdTerminal.ofIso ((overEquivOfIsInitial.{0} X h).unitIso.app A).symm

end CategoryTheory.Over
