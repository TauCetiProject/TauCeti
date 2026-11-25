/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Modules over a semisimple ring are injective objects

Every module over a semisimple ring is injective (`Module.injective_of_isSemisimpleRing`), so
every object of `ModuleCat R` is an injective object of the category. In particular this applies
to vector spaces over a field.
-/

public section

universe u v

namespace ModuleCat

open CategoryTheory

/-- **Every module over a semisimple ring is an injective object** of the category of modules. -/
instance injective_of_isSemisimpleRing (R : Type u) [Ring R] [IsSemisimpleRing R]
    (X : ModuleCat.{v} R) : Injective X :=
  haveI := Module.injective_of_isSemisimpleRing R X
  Module.injective_object_of_injective_module R X

end ModuleCat
