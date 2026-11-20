/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution

/-!
# Cohomology from images of injective resolutions

A functor to abelian sheaves preserving zero morphisms can send an injective resolution
to a resolution with acyclic terms, without preserving injectives or exactness on every object.
The complex of underlying presheaves then computes the cohomology presheaf of the image coefficient.
The comparison is natural in maps of the original resolutions. It specializes
`Sheaf.H'.homologyIsoCohomologyPresheaf` and its naturality theorem to images of resolutions.
-/

public section

open CategoryTheory Limits

universe v v' u u'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasZeroMorphisms D] {M N : D}

/-- The image of an injective resolution computes the cohomology presheaf of
`G.obj M` when its augmentation is monic, it is exact, and its terms are acyclic on the site. -/
noncomputable def mapCohomologyPresheafIso (P : InjectiveResolution M)
    (G : D ⥤ Sheaf J AddCommGrpCat.{v}) [G.PreservesZeroMorphisms] [Mono (G.map P.ι₀)]
    (h₀ : (ShortComplex.mk _ _ (P.map_ι₀_comp_d G)).Exact)
    (hpos : ∀ q, ((G.mapHomologicalComplex _).obj P.cocomplex).ExactAt (q + 1))
    (hV : ∀ V j k, Subsingleton ((G.obj (P.cocomplex.X j)).H' (k + 1) V)) (n : ℕ) :
    (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
      ((G.mapHomologicalComplex _).obj P.cocomplex)).homology n ≅
        (G.obj M).cohomologyPresheaf n := by
  exact Sheaf.H'.homologyIsoCohomologyPresheaf
    (K := (G.mapHomologicalComplex _).obj P.cocomplex)
    (G.map P.ι₀) (P.map_ι₀_comp_d G) h₀ hpos hV n

/-- The comparison for the image of a resolution commutes with a map of
resolutions lifting a coefficient morphism. -/
@[reassoc]
lemma mapCohomologyPresheafIso_naturality (P : InjectiveResolution M)
    (Q : InjectiveResolution N) (G : D ⥤ Sheaf J AddCommGrpCat.{v}) [G.PreservesZeroMorphisms]
    [Mono (G.map P.ι₀)] [Mono (G.map Q.ι₀)]
    (φ : M ⟶ N) (ψ : P.cocomplex ⟶ Q.cocomplex)
    (hψ : P.ι₀ ≫ ψ.f 0 = φ ≫ Q.ι₀)
    (hP₀ : (ShortComplex.mk _ _ (P.map_ι₀_comp_d G)).Exact)
    (hPpos : ∀ q, ((G.mapHomologicalComplex _).obj P.cocomplex).ExactAt (q + 1))
    (hPV : ∀ V j k, Subsingleton ((G.obj (P.cocomplex.X j)).H' (k + 1) V))
    (hQ₀ : (ShortComplex.mk _ _ (Q.map_ι₀_comp_d G)).Exact)
    (hQpos : ∀ q, ((G.mapHomologicalComplex _).obj Q.cocomplex).ExactAt (q + 1))
    (hQV : ∀ V j k, Subsingleton ((G.obj (Q.cocomplex.X j)).H' (k + 1) V)) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).map
        ((G.mapHomologicalComplex _).map ψ)) n ≫
      (Q.mapCohomologyPresheafIso G hQ₀ hQpos hQV n).hom =
    (P.mapCohomologyPresheafIso G hP₀ hPpos hPV n).hom ≫
      (Sheaf.cohomologyPresheafFunctor J n).map (G.map φ) := by
  dsimp only [mapCohomologyPresheafIso]
  exact Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom
    (K := (G.mapHomologicalComplex _).obj P.cocomplex)
    (K' := (G.mapHomologicalComplex _).obj Q.cocomplex)
    (G.map P.ι₀) (P.map_ι₀_comp_d G) hP₀ hPpos hPV n
    (G.map Q.ι₀) (Q.map_ι₀_comp_d G) hQ₀ hQpos hQV
    (φ := G.map φ) (ψ := (G.mapHomologicalComplex _).map ψ)
    ((G.map_comp _ _).symm.trans ((congrArg G.map hψ).trans (G.map_comp _ _)))

end CategoryTheory.InjectiveResolution
