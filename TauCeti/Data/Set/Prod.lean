/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Prod

/-!
# Fibre products of functions

This file adds to Mathlib's API for the fibre product `Function.Pullback f g` of two functions with
a common codomain.

## Main results

* `Function.Pullback.ext`: a point of the fibre product is determined by its two coordinates.
-/

public section

open Function

variable {X Y Z : Type*} {f : X → Y} {g : Z → Y}

/-- A point of the fibre product `X ×_Y Z` is determined by its two coordinates. -/
@[ext]
theorem Function.Pullback.ext {p q : f.Pullback g} (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) :
    p = q :=
  Subtype.ext (Prod.ext h₁ h₂)
