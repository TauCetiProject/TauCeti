/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Tensoring with a flat module preserves homology

Tensoring on the right with a flat module `M` over a commutative ring is an exact functor
`ModuleCat R ⥤ ModuleCat R` (`Module.Flat.rTensor_shortComplex_exact`), so it preserves homology.

Mathlib already provides this for tensoring on the left: there the functor preserves finite limits
by flatness (`Module.Flat.iff_preservesFiniteLimits_tensorLeft`) and finite colimits as a left
adjoint, and `CategoryTheory.Functor.preservesHomologyOfExact` applies. For tensoring on the
right, instance search finds no `PreservesFiniteColimits` instance, so the instance below is
needed.

## Main results

* `TauCeti.ModuleCat.preservesHomology_tensorRight`: tensoring on the right with a flat module
  preserves homology.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

variable {R : Type u} [CommRing R] (M : _root_.ModuleCat.{u} R)

/-- Tensoring on the right with a flat module is exact, so it preserves homology. -/
instance preservesHomology_tensorRight [Module.Flat R M] : (tensorRight M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS ↦ Module.Flat.rTensor_shortComplex_exact M S hS

end TauCeti.ModuleCat
