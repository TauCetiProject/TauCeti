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
condensed module on the free `R`-module `Y →₀ R` (`TauCeti.locallyConstantCompFreeIso`). Both
functors are left adjoint to taking the underlying set of the sections over the point, so they
agree by uniqueness of left adjoints. The comparison of the two right adjoints is
`TauCeti.underlyingCompForgetIso`.
-/

public section

universe u

open CategoryTheory Functor

noncomputable section

namespace TauCeti

open Condensed

variable (R : Type (u + 1)) [Ring R]

/-- Taking the sections over the point of a condensed `R`-module and then its underlying set is
the same as forgetting the module structure first and then taking the sections over the point:
the forgetful functor from condensed modules to condensed sets acts sectionwise, so both functors
send `M` to the underlying set of `M(*)`. -/
def underlyingCompForgetIso :
    underlying (ModuleCat R) ⋙ CategoryTheory.forget (ModuleCat R) ≅
      Condensed.forget R ⋙ (sheafSections (coherentTopology CompHaus.{u}) (Type (u + 1))).obj
        (Opposite.op (CompHaus.of PUnit.{u + 1})) :=
  Iso.refl _

/-- The components of `underlyingCompForgetIso` are identities. -/
@[simp]
lemma underlyingCompForgetIso_hom_app (M : CondensedMod.{u} R) :
    (underlyingCompForgetIso R).hom.app M = 𝟙 _ :=
  (rfl)

/-- The components of the inverse of `underlyingCompForgetIso` are identities. -/
@[simp]
lemma underlyingCompForgetIso_inv_app (M : CondensedMod.{u} R) :
    (underlyingCompForgetIso R).inv.app M = 𝟙 _ :=
  (rfl)

/-- The free condensed `R`-module on a discrete condensed set is the discrete condensed module on
the free `R`-module, by uniqueness of left adjoints. -/
def locallyConstantCompFreeIso :
    CondensedSet.LocallyConstant.functor.{u} ⋙ free R ≅
      ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R :=
  ((CompHausLike.LocallyConstant.adjunction _ _).comp (freeForgetAdjunction R)).leftAdjointUniq
    (((ModuleCat.adj R).comp (CondensedMod.LocallyConstant.adjunction R)).ofNatIsoRight
      (underlyingCompForgetIso R))

end TauCeti
