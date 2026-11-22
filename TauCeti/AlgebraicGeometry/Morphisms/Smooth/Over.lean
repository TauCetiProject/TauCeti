/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Smooth objects of the cartesian monoidal category `Over S`

The objects of `Over S` that are smooth over `S` are closed under the cartesian monoidal
structure: the product `X ⊗ Y` of two smooth `S`-schemes is smooth over `S`, and so is the unit
`𝟙_ (Over S)`, the base `S` itself. These instances make the domains of the structure maps of a
group object of `Over S`, and of its axioms, available as smooth test objects.

## Main declarations

* `TauCeti.AlgebraicGeometry.smooth_tensorObj_hom`: products of smooth `S`-schemes are smooth.
* `TauCeti.AlgebraicGeometry.smooth_tensorUnit_hom`: the unit of `Over S` is smooth over `S`.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The product in `Over S` of two smooth `S`-schemes is smooth over `S`. -/
instance smooth_tensorObj_hom (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

/-- The monoidal unit of `Over S`, the base `S` itself, is smooth over `S`. -/
instance smooth_tensorUnit_hom : Smooth (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (Smooth (𝟙 S))

end TauCeti.AlgebraicGeometry
