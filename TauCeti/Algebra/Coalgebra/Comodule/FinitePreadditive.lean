/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Preadditive structure on finitely generated comodules

This file makes the preadditive structure on the category of finitely generated right
comodules over a coalgebra over a commutative ring available from a finite-comodule import.
The category is a full subcategory of all comodules, so Mathlib transfers the preadditive
structure from `ComoduleCat`.

This is a small Layer 1 prerequisite for the reductive-groups roadmap's finite-dimensional
representation category: additive hom-sets and an additive inclusion functor are needed before
tensor products, duals, and Tannakian reconstruction can be built on finitely generated
comodules.

## References

This supplies additive-category bookkeeping for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule category should have additive hom-sets before the
rigid monoidal representation category is developed. The transfer mechanism is Mathlib's
`ObjectProperty.FullSubcategory` preadditive instance.
-/

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

example : Preadditive (FGComoduleCat.{u, v, w} R C) :=
  inferInstance

example : (FGComoduleCat.incl (R := R) (C := C)).Additive :=
  inferInstance

end FGComoduleCat

end TauCeti
