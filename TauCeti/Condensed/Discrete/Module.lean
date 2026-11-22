/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Module

/-!
# Free condensed modules on discrete condensed sets

The free condensed `R`-module on the discrete condensed set on a set `Y` is the discrete
condensed module on the free `R`-module `Y →₀ R` (`Condensed.freeCompLocallyConstantIso`). Both
functors are left adjoint to taking the underlying set of the sections over the point, so they
agree by uniqueness of left adjoints. The comparison of the two right adjoints is
`Condensed.underlyingCompForgetIso`.
-/

public section

universe u

open CategoryTheory Functor

noncomputable section

namespace Condensed

variable (R : Type (u + 1)) [Ring R]

/-- Taking the sections over the point of a condensed `R`-module and then its underlying set is
the same as forgetting the module structure first and then taking the sections over the point:
the forgetful functor from condensed modules to condensed sets acts sectionwise, so both functors
send `M` to the underlying set of `M(*)`. -/
def underlyingCompForgetIso :
    underlying (ModuleCat R) ⋙ CategoryTheory.forget (ModuleCat R) ≅
      forget R ⋙ (sheafSections (coherentTopology CompHaus.{u}) (Type (u + 1))).obj
        (Opposite.op (CompHaus.of PUnit.{u + 1})) :=
  Iso.refl _

/-- The free condensed `R`-module on a discrete condensed set is the discrete condensed module on
the free `R`-module, by uniqueness of left adjoints. -/
def freeCompLocallyConstantIso :
    CondensedSet.LocallyConstant.functor.{u} ⋙ free R ≅
      ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R :=
  ((CompHausLike.LocallyConstant.adjunction _ _).comp (freeForgetAdjunction R)).leftAdjointUniq
    (((ModuleCat.adj R).comp (CondensedMod.LocallyConstant.adjunction R)).ofNatIsoRight
      (underlyingCompForgetIso R))

end Condensed
