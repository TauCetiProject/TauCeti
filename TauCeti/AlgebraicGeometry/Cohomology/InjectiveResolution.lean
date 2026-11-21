/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
import TauCeti.AlgebraicGeometry.Cohomology.Flasque

/-!
# Module-injective resolutions and cohomology presheaves

The underlying abelian sheaves of an injective resolution of scheme modules are flasque.
Consequently, the homology of its complex of abelian presheaves computes the cohomology
presheaf of the coefficient module. The comparison is natural in maps of resolutions.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TopologicalSpace Functor
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CategoryTheory.InjectiveResolution

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The homology of the underlying presheaf complex of a module-injective resolution is
the cohomology presheaf of its coefficient module. -/
def cohomologyPresheafIso (P : InjectiveResolution M) (n : ℕ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).homology n ≅
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n := by
  haveI : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  exact Sheaf.H'.homologyIsoCohomologyPresheaf
    (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
    ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
    (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (P.cocomplex.X j) k V) n

/-- The cohomology-presheaf comparison for module-injective resolutions commutes with
a map of resolutions lifting a morphism of coefficient modules. -/
@[reassoc]
lemma cohomologyPresheafIso_naturality
    (P : InjectiveResolution M) (Q : InjectiveResolution N) (φ : M ⟶ N)
    (ψ : P.cocomplex ⟶ Q.cocomplex) (hψ : P.ι.f 0 ≫ ψ.f 0 = φ ≫ Q.ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (((toSheaf X).mapHomologicalComplex _).map ψ)) n ≫
      (Q.cohomologyPresheafIso n).hom =
    (P.cohomologyPresheafIso n).hom ≫
      (Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := by
  have : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  have : Mono ((toSheaf X).map (Q.ι.f 0)) := Functor.map_mono _ _
  dsimp only [cohomologyPresheafIso]
  exact Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom
    (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
    (K' := ((toSheaf X).mapHomologicalComplex _).obj Q.cocomplex)
    ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
    (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (P.cocomplex.X j) k V) n
    ((toSheaf X).map (Q.ι.f 0)) (Q.map_ι_f_zero_comp_d (toSheaf X))
    (Q.exact₀_map (toSheaf X)) (Q.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (Q.cocomplex.X j) k V)
    (φ := (toSheaf X).map φ) (ψ := ((toSheaf X).mapHomologicalComplex _).map ψ)
    (by
      exact (toSheaf X).map_comp _ _ |>.symm.trans
        ((congrArg (toSheaf X).map hψ).trans ((toSheaf X).map_comp _ _)))

end CategoryTheory.InjectiveResolution
