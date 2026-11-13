/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech.Resolution
public import TauCeti.Topology.Sheaves.Cohomology.Godement

/-!
# Čech cohomology computes derived global sections on compact Hausdorff spaces

For sheaves of modules over a commutative ring `R` on a compact normal space `X`, in particular
on a compact Hausdorff space, the cover-colimit Čech cohomology `Hⁿ(X, F)`
(`TauCeti.Topology.cechCohomology`) is naturally isomorphic, as an `R`-module, to the native right
derived functor `RⁿΓ(F)` of global sections (`TauCeti.Topology.cechCohomologyIsoRightDerivedΓ`).

Both sides are computed by the global sections of the Godement resolution `F ⟶ G•(F)`, whose
terms are flasque: the Čech side by dimension shifting along the long exact Čech sequence
(`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque`), and the derived side by the
flasque-resolution comparison (`TauCeti.Topology.rightDerivedΓIsoGodement`). The first
identification is natural in the sheaf (`TauCeti.Topology.cechCohomologyIsoGodement`), and the
comparison is the composite of the two (`TauCeti.Topology.cechCohomologyIsoRightDerivedΓ_hom_app`).

## Main definitions

* `TauCeti.Topology.cechCohomologyIsoGodement`: `Hⁿ(X, F) ≅ Hⁿ(Γ(G•(F)))`, naturally in `F`.
* `TauCeti.Topology.cechCohomologyIsoRightDerivedΓ`: `Hⁿ(X, F) ≅ RⁿΓ(F)`, naturally in `F`.

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.16.2 (tag 09V2) and Lemma 20.30.2
  (tag 0FKT).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} [CompactSpace X] [NormalSpace X]

section Ring

variable {R : Type u} [Ring R]

/-- The global sections of the Godement resolution compute cover-colimit Čech cohomology on a
compact normal space, naturally in the sheaf. This is the Čech counterpart of
`TauCeti.Topology.rightDerivedΓIsoGodement`. -/
def cechCohomologyIsoGodement (n : ℕ) :
    sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
        cechCohomology X (ModuleCat.{u} R) n ≅
      godementResolution (ModuleCat.{u} R) X ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n :=
  NatIso.ofComponents
    (fun F ↦ cechCohomologyObjIsoOfIsFlasque ((toGodementResolution (ModuleCat.{u} R) X).app F)
      (isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X F) n)
    (fun f ↦ cechCohomologyObjIsoOfIsFlasque_hom_naturality _ _ _
      ((toGodementResolution (ModuleCat.{u} R) X).naturality f).symm _ n)

/-- The component of `cechCohomologyIsoGodement` at `F` is the comparison
`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque` for the Godement resolution of `F`. -/
@[simp]
lemma cechCohomologyIsoGodement_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (cechCohomologyIsoGodement n).app F =
      cechCohomologyObjIsoOfIsFlasque ((toGodementResolution (ModuleCat.{u} R) X).app F)
        (isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X F) n := by
  rw [cechCohomologyIsoGodement]
  exact NatIso.ofComponents.app _ _ F

end Ring

variable {R : Type u} [CommRing R]
  [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

/-- **Čech cohomology is derived-functor cohomology on compact Hausdorff spaces.** For sheaves of
`R`-modules on a compact normal space `X`, the cover-colimit Čech cohomology `Hⁿ(X, F)` is
naturally isomorphic to the right derived functor `RⁿΓ(F)` of global sections. Both are computed
by the global sections of the Godement resolution
(`TauCeti.Topology.cechCohomologyIsoRightDerivedΓ_hom_app`). -/
def cechCohomologyIsoRightDerivedΓ (n : ℕ) :
    sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
        cechCohomology X (ModuleCat.{u} R) n ≅
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n :=
  cechCohomologyIsoGodement n ≪≫ (rightDerivedΓIsoGodement n).symm

/-- The comparison `cechCohomologyIsoRightDerivedΓ` is the Godement computation of Čech
cohomology followed by the inverse of the Godement computation of `RⁿΓ`. -/
lemma cechCohomologyIsoRightDerivedΓ_hom_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (cechCohomologyIsoRightDerivedΓ n).hom.app F =
      (cechCohomologyIsoGodement n).hom.app F ≫ (rightDerivedΓIsoGodement n).inv.app F := by
  rw [cechCohomologyIsoRightDerivedΓ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

end TauCeti.Topology
