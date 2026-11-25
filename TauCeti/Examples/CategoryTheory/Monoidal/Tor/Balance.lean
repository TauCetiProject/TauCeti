/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.CategoryTheory.Monoidal.Tor.Balance

/-!
# Checks for the balance of `Tor₁`

Over a principal ideal domain every module has projective dimension at most one
(`ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing`), tensoring is right exact, and
projective modules are flat, so `Tor₁(X, Y) ≅ Tor'₁(X, Y)` for all modules `X` and `Y`, in
particular for abelian groups. Mathlib's `Tor` derives the second variable and `Tor'` the first,
so the two sides are computed from projective resolutions of different modules.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.TorBalanceExample

/-- **Balance of `Tor₁` over a principal ideal domain.** For modules `X` and `Y` over a principal
ideal domain, `Tor₁(X, Y) ≅ Tor'₁(X, Y)`. -/
noncomputable example {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ModuleCat.{0} R) :
    ((Tor (ModuleCat.{0} R) 1).obj X).obj Y ≅ ((Tor' (ModuleCat.{0} R) 1).obj X).obj Y :=
  torOneIsoTor'OneOfHasProjectiveDimensionLEOne X Y

/-- **Balance of `Tor₁` over `ℤ`.** For abelian groups `X` and `Y`,
`Tor₁^ℤ(X, Y) ≅ Tor'₁^ℤ(X, Y)`. -/
noncomputable example (X Y : ModuleCat.{0} ℤ) :
    ((Tor (ModuleCat.{0} ℤ) 1).obj X).obj Y ≅ ((Tor' (ModuleCat.{0} ℤ) 1).obj X).obj Y :=
  torOneIsoTor'OneOfHasProjectiveDimensionLEOne X Y

end TauCeti.TorBalanceExample
