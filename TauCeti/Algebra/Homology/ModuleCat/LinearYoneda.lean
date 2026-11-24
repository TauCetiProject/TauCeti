/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Cochains of `Hom(X, Y)` for complexes of modules

For a chain complex `X` of `R`-modules and an `R`-module `Y`, an element of degree `i` of Mathlib's
cochain complex `ChainComplex.linearYonedaObj X S Y` of `S`-modules is a morphism `X.X i ⟶ Y`. The
additive structure on these cochains is that of morphisms of modules, but the two types agree only
after unfolding `ChainComplex.linearYonedaObj`, so rewriting lemmas about morphisms such as
`ModuleCat.hom_sub` do not apply to cochains directly. This file records the underlying linear map
of the zero cochain and of a difference of cochains.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.ChainComplex

variable {R : Type u} [Ring R] {S : Type*} [Ring S] [Linear S (ModuleCat.{v} R)]
  {α : Type*} [AddRightCancelSemigroup α] [One α] {X : _root_.ChainComplex (ModuleCat.{v} R) α}
  {Y : ModuleCat.{v} R} {i : α}

/-- The zero cochain of `Hom(X, Y)` is the zero linear map. -/
@[simp]
lemma linearYonedaObj_hom_zero : ModuleCat.Hom.hom (0 : (X.linearYonedaObj S Y).X i) = 0 :=
  rfl

/-- A difference of cochains of `Hom(X, Y)` is the difference of their linear maps. -/
@[simp]
lemma linearYonedaObj_hom_sub (u v : (X.linearYonedaObj S Y).X i) :
    ModuleCat.Hom.hom (u - v) = ModuleCat.Hom.hom u - ModuleCat.Hom.hom v :=
  rfl

end TauCeti.ChainComplex
