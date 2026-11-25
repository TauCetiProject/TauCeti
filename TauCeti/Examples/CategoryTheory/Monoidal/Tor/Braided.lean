/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.CategoryTheory.Monoidal.Tor.Braided

/-!
# Checks for the balance of `Tor₁`

Over a principal ideal domain every module has projective dimension at most one
(`ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing`), so `Tor₁(X, Y) ≅ Tor'₁(Y, X)`
for all modules `X` and `Y`, in particular for abelian groups. Mathlib's `Tor` derives the second
variable and `Tor'` the first, so the two sides are computed from projective resolutions of
different modules.
-/

public section

open CategoryTheory

namespace TauCeti.TorBraidedExample

/-- **Balance of `Tor₁` over a principal ideal domain.** For modules `X` and `Y` over a principal
ideal domain, `Tor₁(X, Y) ≅ Tor'₁(Y, X)`. -/
noncomputable example {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : ModuleCat.{0} R) :
    ((Tor (ModuleCat.{0} R) 1).obj X).obj Y ≅ ((Tor' (ModuleCat.{0} R) 1).obj Y).obj X :=
  torOneIsoTor'OneOfHasProjectiveDimensionLEOne X Y

/-- **Balance of `Tor₁` over `ℤ`.** For abelian groups `X` and `Y`,
`Tor₁^ℤ(X, Y) ≅ Tor'₁^ℤ(Y, X)`. -/
noncomputable example (X Y : ModuleCat.{0} ℤ) :
    ((Tor (ModuleCat.{0} ℤ) 1).obj X).obj Y ≅ ((Tor' (ModuleCat.{0} ℤ) 1).obj Y).obj X :=
  torOneIsoTor'OneOfHasProjectiveDimensionLEOne X Y

end TauCeti.TorBraidedExample
