/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Quadratic AdjoinRoot reduction

The defining equation for the root of `X² - d` in its `AdjoinRoot` model.
-/

public section

open Polynomial

namespace TauCeti.AdjoinRoot

variable {R : Type*} [CommRing R]

/-- The root of `X² - d` in its `AdjoinRoot` model squares to the coefficient `d`. -/
@[simp] theorem root_sq (d : R) :
    (AdjoinRoot.root (X ^ 2 - C d)) ^ 2 = algebraMap R (AdjoinRoot (X ^ 2 - C d)) d := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X,
    AdjoinRoot.algebraMap_eq]

end TauCeti.AdjoinRoot
