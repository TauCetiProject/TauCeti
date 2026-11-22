/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Categories whose simple objects have scalar endomorphisms

This module defines the lightweight typeclass `TauCeti.HasScalarSimpleEnd k C`, asserting that in a
`k`-linear preadditive category `C`, the structure map `algebraMap k (End X)` is surjective for
every simple object `X`.

Instances derived from Schur's lemma over an algebraically closed field live in
`TauCeti/CategoryTheory/Preadditive/Schur.lean`. Separating the interface allows consumers such as
grading-character classifications to work over arbitrary fields with scalar simple endomorphisms
without importing algebraically closed field theory.
-/

public section

open CategoryTheory

universe w v u

namespace TauCeti

/-- A `k`-linear preadditive category has scalar simple endomorphisms if for every simple object
`X`, the structure map `k → End X` is surjective. -/
class HasScalarSimpleEnd (k : Type w) [CommSemiring k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] : Prop where
  /-- For every simple object `X`, `algebraMap k (End X)` is surjective. -/
  surjective_algebraMap (X : C) [Simple X] : Function.Surjective (algebraMap k (End X))

end TauCeti
