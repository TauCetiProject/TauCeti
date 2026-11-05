/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import TauCeti.CategoryTheory.Monoidal.Center.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Center.Limits

/-!
# Simple objects in the Drinfeld centre

An object of the Drinfeld centre whose underlying object is simple is itself simple, provided
the forgetful functor preserves monomorphisms. The converse need not hold: a half-braiding can
exclude subobjects of the underlying object from being subobjects in the centre.

When `C` has finite limits and tensoring on both sides preserves them, the forgetful functor
preserves finite limits and hence monomorphisms. These hypotheses hold in a rigid abelian
monoidal category. In particular, if the tensor unit of `C` is simple, the canonical tensor unit
of `Center C` is simple. No semisimplicity, finiteness of the simple classes, or assumption on a
coefficient field is needed.

Together with `CategoryTheory.Center.instFiniteDimensionalHom`, this supplies the simple-unit
and Hom-finiteness properties of the centre using its canonical monoidal and linear structures.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

universe v u

namespace CategoryTheory.Center

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-- An object of the centre with simple underlying object is simple, whenever the forgetful
functor preserves monomorphisms. -/
instance instSimple [(forget C).PreservesMonomorphisms] (X : Center C) [Simple X.1] :
    Simple X := by
  have : Simple ((forget C).obj X) := ‹Simple X.1›
  exact (forget C).simple_of_simple_obj X

/-- If the forgetful functor preserves monomorphisms, a simple tensor unit in `C` gives a
simple tensor unit in its centre, for the canonical monoidal structure. -/
instance instSimpleUnit [(forget C).PreservesMonomorphisms]
    [Simple (𝟙_ C)] : Simple (𝟙_ (Center C)) := by
  have : Simple ((forget C).obj (𝟙_ (Center C))) :=
    Simple.of_iso (Functor.Monoidal.εIso (forget C)).symm
  exact (forget C).simple_of_simple_obj _

end CategoryTheory.Center
