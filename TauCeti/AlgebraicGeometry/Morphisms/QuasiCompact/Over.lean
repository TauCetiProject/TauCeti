/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Morphisms.OverTensorUnit

/-!
# Quasi-compact and quasi-separated objects of the cartesian monoidal category `Over S`

The objects of `Over S` that are quasi-compact (quasi-separated) over `S` are closed under the
cartesian monoidal structure: the product `X ⊗ Y` of two quasi-compact (quasi-separated)
`S`-schemes is quasi-compact (quasi-separated) over `S`. These instances make the domains of the
structure maps of a group object of `Over S`, and of its axioms, available where quasi-compactness
or quasi-separatedness over `S` is required.

## Main declarations

* `TauCeti.AlgebraicGeometry.quasiCompact_tensorObj_hom`: products of quasi-compact `S`-schemes
  are quasi-compact.
* `TauCeti.AlgebraicGeometry.quasiSeparated_tensorObj_hom`: products of quasi-separated
  `S`-schemes are quasi-separated.

The unit `𝟙_ (Over S)` is quasi-compact and quasi-separated over `S` because its structure morphism
is proper (`TauCeti.AlgebraicGeometry.isProper_tensorUnit_hom`, in
`TauCeti.AlgebraicGeometry.Morphisms.OverTensorUnit`, which this file imports).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The product in `Over S` of two quasi-compact `S`-schemes is quasi-compact over `S`. -/
instance quasiCompact_tensorObj_hom (X Y : Over S) [QuasiCompact X.hom] [QuasiCompact Y.hom] :
    QuasiCompact (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

/-- The product in `Over S` of two quasi-separated `S`-schemes is quasi-separated over `S`. -/
instance quasiSeparated_tensorObj_hom (X Y : Over S) [QuasiSeparated X.hom]
    [QuasiSeparated Y.hom] : QuasiSeparated (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end TauCeti.AlgebraicGeometry
