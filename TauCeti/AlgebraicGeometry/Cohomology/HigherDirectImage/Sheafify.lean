/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.HigherDirectImage
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Flasque
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# Higher direct images of scheme modules as sheafified cohomology

Let `f : X ⟶ Y` be a morphism of schemes and `M` a sheaf of modules on `X`. The higher direct
image `R^q f_* M` is computed by injective resolutions in the category of sheaves of modules on
`X` (`AlgebraicGeometry.Scheme.Hom.higherDirectImage`). This file shows that its underlying
abelian sheaf is the sheafification of the presheaf `V ↦ H^q(f⁻¹ V, M)` on `Y`
(`AlgebraicGeometry.Scheme.Hom.toSheafHigherDirectImageObjIsoSheafify`).

An injective resolution `M ⟶ I^•` of sheaves of modules need not be injective as a resolution of
abelian sheaves, but its terms are flasque
(`AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective`), hence have no higher cohomology on
any open subset. Forgetting the module structures is exact and commutes with pushforward, so the
underlying abelian sheaf of `R^q f_* M` is the `q`-th homology of the pushforward of the flasque
resolution of abelian sheaves underlying `I^•`. The pushforward of such an acyclic resolution
computes the sheafified cohomology presheaves
(`CategoryTheory.Functor.sheafPushforwardContinuousHomologyIsoSheafify`).

This is the starting point for computing higher direct images over the affine opens of the base,
for instance for quasi-coherent sheaves along quasi-compact quasi-separated morphisms.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toSheafHigherDirectImageObjIsoSheafify`: the underlying abelian
  sheaf of `R^q f_* M` is the sheafification of `V ↦ H^q(f⁻¹ V, M)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.1.
* [Stacks Project, Lemma 21.7.4 (Tag 072W)](https://stacks.math.columbia.edu/tag/072W), for
  morphisms of sites.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images are sheafified cohomology presheaves.** For a morphism of schemes
`f : X ⟶ Y` and a sheaf of modules `M` on `X`, the underlying abelian sheaf of the higher direct
image `R^q f_* M` is the sheafification of the presheaf `V ↦ H^q(f⁻¹ V, M)` on `Y`. -/
def toSheafHigherDirectImageObjIsoSheafify (M : X.Modules) (q : ℕ) :
    (toSheaf Y).obj ((f.higherDirectImage q).obj M) ≅
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((Opens.map f.base).op ⋙ ((toSheaf X).obj M).cohomologyPresheaf q) :=
  letI := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  let P := injectiveResolution M
  haveI : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  (toSheaf Y).mapIso (P.isoRightDerivedObj (Scheme.Modules.pushforward f) q) ≪≫
    ((toSheaf Y).mapHomologicalComplexCompHomologyFunctorIso _ q).symm.app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      -- forgetting the module structure commutes with pushforward
      ((Functor.mapHomologicalComplexCompIso
          (eqToIso (pushforward_comp_toSheaf f) : Scheme.Modules.pushforward f ⋙ toSheaf Y ≅
            toSheaf X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base) _).app
          P.cocomplex ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app P.cocomplex).symm) ≪≫
    -- the abelian sheaves underlying an injective resolution of modules are flasque, hence
    -- acyclic on every open
    (Opens.map f.base).sheafPushforwardContinuousHomologyIsoSheafify _ _
      (L := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
      ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
      (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
      (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
        (P.cocomplex.X j) k V) q

end AlgebraicGeometry.Scheme.Hom
