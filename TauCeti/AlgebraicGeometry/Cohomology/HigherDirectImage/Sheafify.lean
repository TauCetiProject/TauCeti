/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Presheaf

/-!
# Higher direct images of scheme modules as sheafified cohomology

Let `f : X ⟶ Y` be a morphism of schemes and `M` a sheaf of modules on `X`. The higher direct
image `R^q f_* M` is computed by injective resolutions in the category of sheaves of modules on
`X` (`AlgebraicGeometry.Scheme.Hom.higherDirectImage`). This file shows that its underlying
abelian sheaf is the sheafification of the presheaf `V ↦ H^q(f⁻¹ V, M)` on `Y`
(`AlgebraicGeometry.Scheme.Hom.toSheafHigherDirectImageObjIsoSheafify`).

The module presheaf `f.higherDirectImagePresheaf q` retains the module structures in
this computation. Its sheafification is the higher direct image as a sheaf of modules
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafSheafificationIso`), and its
underlying abelian presheaf is `V ↦ H^q(f⁻¹ V, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso`). Forgetting scalars
commutes with sheafification, giving the abelian-sheaf comparison here.

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
  (toSheaf Y).mapIso ((f.higherDirectImagePresheafSheafificationIso q).app M).symm ≪≫
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 Y.ringCatSheaf.obj)).app
      ((f.higherDirectImagePresheaf q).obj M) ≪≫
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso
      (f.higherDirectImagePresheafToPresheafIso M q)

end AlgebraicGeometry.Scheme.Hom
