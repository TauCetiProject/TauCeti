/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
import TauCeti.AlgebraicGeometry.Cohomology.Flasque

/-!
# Module-injective resolutions and cohomology presheaves

The underlying abelian sheaves of an injective resolution of scheme modules are flasque.
Consequently, the homology of its complex of abelian presheaves computes the cohomology
presheaf of the coefficient module. The comparison is natural in maps of resolutions, and sends
the homology class of a cycle to its class `CategoryTheory.Sheaf.H'.resolutionClass`
(`CategoryTheory.InjectiveResolution.cohomologyPresheafIso_hom_app_homologyπ_apply`). After an exact
functor, global functions act on these classes by multiplication of sections
(`AlgebraicGeometry.Scheme.Modules.cohomologyOnMap_globalSectionsSmul_resolutionClass`).
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
    ((toSheaf X).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d (toSheaf X) P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (toSheaf X) P.exact₀)
    (CochainComplex.map_exactAt_succ (toSheaf X) P.cocomplex_exactAt_succ)
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
    ((toSheaf X).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d (toSheaf X) P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (toSheaf X) P.exact₀)
    (CochainComplex.map_exactAt_succ (toSheaf X) P.cocomplex_exactAt_succ)
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (P.cocomplex.X j) k V) n
    ((toSheaf X).map (Q.ι.f 0))
    (CochainComplex.map_augmentation_comp_d (toSheaf X) Q.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (toSheaf X) Q.exact₀)
    (CochainComplex.map_exactAt_succ (toSheaf X) Q.cocomplex_exactAt_succ)
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (Q.cocomplex.X j) k V)
    (φ := (toSheaf X).map φ) (ψ := ((toSheaf X).mapHomologicalComplex _).map ψ)
    (by
      exact (toSheaf X).map_comp _ _ |>.symm.trans
        ((congrArg (toSheaf X).map hψ).trans ((toSheaf X).map_comp _ _)))

/-- Under `cohomologyPresheafIso`, the homology class of a cycle `s ∈ Pⁿ(U)` is its class
`CategoryTheory.Sheaf.H'.resolutionClass` in `Hⁿ(U, M)`. -/
lemma cohomologyPresheafIso_hom_app_homologyπ_apply (P : InjectiveResolution M) (n : ℕ)
    (U : X.Opensᵒᵖ)
    (z : ((((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).cycles n).obj U) :
    (P.cohomologyPresheafIso n).hom.app U
        (((((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
          (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).homologyπ n).app U z) =
      Sheaf.H'.resolutionClass (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
        ((toSheaf X).map (P.ι.f 0))
        (CochainComplex.map_augmentation_comp_d (toSheaf X) P.ι_f_zero_comp_complex_d)
        (CochainComplex.map_augmentation_exact (toSheaf X) P.exact₀)
        (CochainComplex.map_exactAt_succ (toSheaf X) P.cocomplex_exactAt_succ) U.unop
        (((((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
          (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).iCycles n).app U z)
        (Sheaf.H'.d_hom_app_iCycles_app n z) :=
  Sheaf.H'.homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply _ _ _ _ _ n U z

end CategoryTheory.InjectiveResolution

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z : Scheme.{u}} (G : X.Modules ⥤ Z.Modules) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] {M : X.Modules} (P : InjectiveResolution M)

/-- **Global functions act on classes of sections.** Let `G` be an exact functor from modules on
`X` to modules on `Z` and `P` an injective resolution of `M`. Multiplication by a global function
`c` on `Z` sends the class in `Hⁿ(V, G(M))` of a section `u` of `G(Pⁿ)` over `V` to the class of
`c • u`. -/
lemma cohomologyOnMap_globalSectionsSmul_resolutionClass {n : ℕ} (V : Z.Opens) (c : Γ(Z, ⊤))
    (u : Γ(G.obj (P.cocomplex.X n), V)) (hu : (G.map (P.cocomplex.d n (n + 1))).app V u = 0) :
    cohomologyOnMap ((G.obj M).globalSectionsSmul c) n V
      (CategoryTheory.Sheaf.H'.resolutionClass
        (K := ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex)
        ((G ⋙ toSheaf Z).map (P.ι.f 0))
        (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
        (CochainComplex.map_augmentation_exact _ P.exact₀)
        (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) V u hu) =
      CategoryTheory.Sheaf.H'.resolutionClass
        (K := ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex)
        ((G ⋙ toSheaf Z).map (P.ι.f 0))
        (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
        (CochainComplex.map_augmentation_exact _ P.exact₀)
        (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) V
        (Z.presheaf.map V.leTop.op c • u) (by
          -- The differential of the complex of abelian sheaves is, by definition, `Hom.app` of
          -- the module differential, which is linear over functions.
          change (G.map (P.cocomplex.d n (n + 1))).app V (_ • u) = 0
          rw [Scheme.Modules.Hom.app_smul, hu, smul_zero]) := by
  let ψ₀ : (G.mapHomologicalComplex _).obj P.cocomplex ⟶
      (G.mapHomologicalComplex _).obj P.cocomplex :=
    { f k := (G.obj (P.cocomplex.X k)).globalSectionsSmul c
      comm' i j _ := Scheme.Modules.globalSectionsSmul_naturality _ c }
  let ψ : ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex ⟶
      ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex :=
    ((toSheaf Z).mapHomologicalComplex _).map ψ₀
  have hψ : (G ⋙ toSheaf Z).map (P.ι.f 0) ≫ ψ.f 0 =
      (toSheaf Z).map ((G.obj M).globalSectionsSmul c) ≫ (G ⋙ toSheaf Z).map (P.ι.f 0) := by
    exact ((toSheaf Z).map_comp _ _).symm.trans ((congrArg (toSheaf Z).map
      (Scheme.Modules.globalSectionsSmul_naturality _ c).symm).trans ((toSheaf Z).map_comp _ _))
  refine (CategoryTheory.Sheaf.H'.cohomologyPresheafFunctor_map_app_resolutionClass
    (K := ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex)
    (K' := ((G ⋙ toSheaf Z).mapHomologicalComplex _).obj P.cocomplex)
    ((G ⋙ toSheaf Z).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) V ((G ⋙ toSheaf Z).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) (ψ := ψ) hψ u hu).trans ?_
  congr 1
  -- The component of `ψ` in degree `n` is, by construction, `globalSectionsSmul c` on `G(Pⁿ)`.
  change ((G.obj (P.cocomplex.X n)).globalSectionsSmul c).app V u = _
  rw [globalSectionsSmul_app]
  rfl

end AlgebraicGeometry.Scheme.Modules
