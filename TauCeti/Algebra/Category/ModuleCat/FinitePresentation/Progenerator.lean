/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.Algebra.Category.ModuleCat.Progenerator

/-!
# Progenerators in the category of finitely presented modules

Specializing `TauCeti.Algebra.Category.ModuleCat.Progenerator` to
`(TauCeti.finitePresentationModules R).FullSubcategory`, an object `P` is a categorical
progenerator if and only if its underlying `R`-module is projective and a generator
(`TauCeti.isProgenerator_finitePresentationModules_iff`). In particular, over any ring `R`, the
regular module `R` is a progenerator of `(finitePresentationModules R).FullSubcategory`
(`TauCeti.isProgenerator_finitePresentationModulesRegular`).

## Main results

* `TauCeti.isProgenerator_finitePresentationModules_iff`: characterization of progenerators in
  `(finitePresentationModules R).FullSubcategory`.
* `TauCeti.isProgenerator_finitePresentationModulesRegular`: the regular module `R` is a
  progenerator of `(finitePresentationModules R).FullSubcategory`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (R : Type u) [Ring R]

/-- An object `P` of `(finitePresentationModules R).FullSubcategory` is a categorical progenerator
if and only if its underlying `R`-module is projective and a generator. -/
theorem isProgenerator_finitePresentationModules_iff
    (P : (finitePresentationModules R).FullSubcategory) :
    IsProgenerator P ↔ Module.Projective R P.obj ∧ TauCeti.Module.IsGenerator R P.obj :=
  (finitePresentationModules R).isProgenerator_iff_moduleProjective_and_isGenerator
    (finitePresentationModules_le_finiteModules R)
    (eqToIso (finitePresentationModulesRegular_obj R)).toLinearEquiv P

/-- Over any ring `R`, the regular module `R` is a progenerator of the category of finitely
presented `R`-modules. -/
theorem isProgenerator_finitePresentationModulesRegular :
    IsProgenerator (finitePresentationModulesRegular R) :=
  let e : (finitePresentationModulesRegular R).obj ≃ₗ[R] R :=
    (eqToIso (finitePresentationModulesRegular_obj R)).toLinearEquiv
  (isProgenerator_finitePresentationModules_iff R _).mpr
    ⟨Module.Projective.of_equiv e.symm, TauCeti.Module.IsGenerator.of_linearEquiv e⟩

end TauCeti
