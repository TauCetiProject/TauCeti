/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor.Basic
public import TauCeti.CategoryTheory.Monoidal.Tor.Coproduct

/-!
# `Tor` of modules commutes with direct sums in either variable

Over a commutative ring `R`, tensoring with a module on either side preserves all colimits, and
direct sums of `R`-modules indexed by small types are exact. So for every `n` the functor
`Torₙ^R(X, -)` (Mathlib's `CategoryTheory.Tor`, which derives the second variable) preserves
direct sums, and so does `Torₙ^R(-, Y)`: the comparison maps `⨁ⱼ Torₙ(X, Yⱼ) ⟶ Torₙ(X, ⨁ⱼ Yⱼ)`
and `⨁ⱼ Torₙ(Xⱼ, Y) ⟶ Torₙ(⨁ⱼ Xⱼ, Y)` are isomorphisms
(`ModuleCat.isIso_sigmaComparison_Tor_obj`, `ModuleCat.isIso_sigmaComparison_Tor_flip_obj`).
In particular, for `R = ℤ` and `n = 1`, `Tor₁` of abelian groups commutes with direct sums in
either variable.
-/

public section

open CategoryTheory Limits

universe w u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- **`Tor` of modules commutes with direct sums in the second variable**: the comparison map
`⨁ⱼ Torₙ(X, Yⱼ) ⟶ Torₙ(X, ⨁ⱼ Yⱼ)` is an isomorphism. -/
theorem isIso_sigmaComparison_Tor_obj {J : Type w} [Small.{u} J]
    (X : ModuleCat.{u} R) (Y : J → ModuleCat.{u} R) (n : ℕ) :
    IsIso (sigmaComparison ((Tor (ModuleCat.{u} R) n).obj X) Y) :=
  inferInstance

/-- **`Tor` of modules commutes with direct sums in the first variable**: the comparison map
`⨁ⱼ Torₙ(Xⱼ, Y) ⟶ Torₙ(⨁ⱼ Xⱼ, Y)` is an isomorphism. -/
theorem isIso_sigmaComparison_Tor_flip_obj {J : Type w} [Small.{u} J]
    (X : J → ModuleCat.{u} R) (Y : ModuleCat.{u} R) (n : ℕ) :
    IsIso (sigmaComparison ((Tor (ModuleCat.{u} R) n).flip.obj Y) X) :=
  inferInstance

end ModuleCat
