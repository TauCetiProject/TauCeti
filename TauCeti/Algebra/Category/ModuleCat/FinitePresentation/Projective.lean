/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.FullSubcategory

/-!
# Projective objects in the category of finitely presented modules

Specializing `TauCeti.Algebra.Category.ModuleCat.Projective.FullSubcategory` to
`(TauCeti.finitePresentationModules R).FullSubcategory`, an object `P` is a projective object of
`(finitePresentationModules R).FullSubcategory` if and only if its underlying `R`-module is
projective (`TauCeti.projective_finitePresentationModules_iff`). In particular, the regular module
`TauCeti.finitePresentationModulesRegular R` is projective.

## Main results

* `TauCeti.projective_finitePresentationModules_iff`: characterization of projective objects in
  `(finitePresentationModules R).FullSubcategory`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

variable (R : Type u) [Ring R]

/-- An object `P` of `(finitePresentationModules R).FullSubcategory` is projective if and only if
its underlying `R`-module is projective. -/
theorem projective_finitePresentationModules_iff
    (P : (finitePresentationModules R).FullSubcategory) :
    Projective P ↔ Module.Projective R P.obj :=
  (finitePresentationModules R).projective_iff_moduleProjective
    (finitePresentationModulesRegularLinearEquiv R) P

/-- The regular module `R` is a projective object of
`(finitePresentationModules R).FullSubcategory`. -/
instance : Projective (finitePresentationModulesRegular R) :=
  (projective_finitePresentationModules_iff R _).mpr (Module.Projective.of_equiv
    (finitePresentationModulesRegularLinearEquiv R).symm)

end TauCeti
