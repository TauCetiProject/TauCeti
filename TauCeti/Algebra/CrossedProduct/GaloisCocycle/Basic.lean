/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Bundled Galois cocycles

A `TauCeti.GaloisCocycle K` bundles a finite Galois subextension `L` of the separable closure
`Kˢ/K` with a `2`-cocycle of `Gal(L/K)` with values in `Lˣ`. Bundling the extension together with
its instances lets a statement quantify over "some finite Galois splitting field and some cocycle
of its Galois group" without quantifying over instances.

## Main definitions

* `TauCeti.GaloisCocycle K`: a finite Galois subextension of `Kˢ/K` with a `2`-cocycle of its
  Galois group.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
-/

public section

universe u

namespace TauCeti

variable (K : Type u) [Field K]

/-- A **Galois cocycle** of `K`: a finite Galois subextension `L` of the separable closure
`Kˢ/K`, together with a `2`-cocycle of `Gal(L/K)` with values in `Lˣ`. The extension is taken
inside `Kˢ` so that it determines an open subgroup of the absolute Galois group. -/
structure GaloisCocycle where
  /-- The finite Galois subextension `L` of `Kˢ/K`. -/
  extension : IntermediateField K (SeparableClosure K)
  [finiteDimensional : FiniteDimensional K extension]
  [isGalois : IsGalois K extension]
  /-- The `2`-cocycle of `Gal(L/K)`. -/
  cocycle : TwoCocycle K extension

attribute [instance] GaloisCocycle.finiteDimensional GaloisCocycle.isGalois

end TauCeti
