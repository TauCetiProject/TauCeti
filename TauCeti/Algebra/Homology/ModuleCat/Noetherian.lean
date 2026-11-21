/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Noetherianity and finiteness of homology of complexes of modules

For a homological complex `K` of `R`-modules of arbitrary shape `c`, if the term `K.X i` at index
`i` is a Noetherian `R`-module, then the homology `K.homology i` is a subquotient of `K.X i` and
is therefore Noetherian (`HomologicalComplex.isNoetherian_homology`) and finitely generated
(`HomologicalComplex.finite_homology`), without assuming that the ring `R` itself is Noetherian.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- If the term `K.X i` of a homological complex of `R`-modules is a Noetherian module, then its
homology `K.homology i` is a Noetherian module. -/
instance isNoetherian_homology (i : ι) [IsNoetherian R (K.X i)] :
    IsNoetherian R (K.homology i) :=
  -- The middle term of `K.sc i` is `K.X i` by construction.
  have : IsNoetherian R (K.sc i).X₂ := ‹IsNoetherian R (K.X i)›
  inferInstanceAs (IsNoetherian R (K.sc i).homology)

/-- If the term `K.X i` of a homological complex of `R`-modules is a Noetherian module, then its
homology `K.homology i` is finitely generated. -/
theorem finite_homology (i : ι) [IsNoetherian R (K.X i)] :
    Module.Finite R (K.homology i) :=
  Module.IsNoetherian.finite R (K.homology i)

end HomologicalComplex
