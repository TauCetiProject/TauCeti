/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
public import TauCeti.Topology.Sheaves.Cech.Basic
public import TauCeti.Topology.Sheaves.CoverSystems

/-!
# Čech cohomology of presheaves on a topological space

The Čech cohomology of a presheaf `P` on an arbitrary topological space `X` is the colimit, over
open covers ordered by refinement, of the cohomology of the Čech complexes `Č(U, P)`. The open
covers of `X` do not form a small system, but the point-neighborhood covers do
(`TauCeti.Topology.PointOpenCover`): they are indexed by `X` itself, every small open cover is
refined by one of them, and any two of them have a common refinement. So the Čech cohomology is
defined here as the colimit over point-neighborhood covers, using the colimit of
`TauCeti.CategoryTheory.cechCohomology`. Its transition maps are induced by refinement maps and do
not depend on their choice.

No hypothesis is made on `X`. On the empty space the only point-neighborhood cover is the empty
family, whose Čech complex vanishes, so the Čech cohomology of every presheaf vanishes, even when
`P(∅)` does not. For a sheaf `F`, the augmentations identify the degree `0` Čech cohomology with the
global sections `F(X)`.

## Main definitions

* `TauCeti.Topology.cechCohomology X A n`: the degree `n` Čech cohomology of presheaves on `X`
  with values in `A`, as a functor of the presheaf.
* `TauCeti.Topology.cechCohomologyZeroIso F`: for a sheaf `F`, the identification of its degree
  `0` Čech cohomology with `F(X)`.

## Main results

* `TauCeti.Topology.isZero_cechCohomology_obj_of_isEmpty`: on the empty space, the Čech cohomology
  of every presheaf vanishes in every degree.
* `TauCeti.Topology.cechCohomologyZeroIso_hom`: the identification in degree `0` is the
  augmentation of the Čech complex of any point-neighborhood cover, followed by its structure map.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), and Lemma 20.9.2 (tag 01EG) for
  degree `0`.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A, Remark A.4.2 and Definition A.4.3.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe v' u u'

namespace TauCeti.Topology

variable (X : TopCat.{u}) (A : Type u') [Category.{v'} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A] (n : ℕ)

/-- The degree `n` Čech cohomology of presheaves on `X` with values in `A`: the colimit over the
point-neighborhood covers `U`, ordered by refinement, of the degree `n` cohomology of the Čech
complexes `Č(U, P)`. The transition maps are induced by refinement maps
(`TauCeti.CategoryTheory.cechCohomologyDiagram_map_app`). -/
abbrev cechCohomology : ((Opens X)ᵒᵖ ⥤ A) ⥤ A :=
  TauCeti.CategoryTheory.cechCohomology A PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n

/-- **Čech cohomology vanishes on the empty space.** The only point-neighborhood cover of the empty
space is the empty family, whose Čech complex is zero, so the Čech cohomology of every presheaf
vanishes in every degree, even if its value on the empty open is nonzero. -/
theorem isZero_cechCohomology_obj_of_isEmpty [IsEmpty X] (P : (Opens X)ᵒᵖ ⥤ A) :
    IsZero ((cechCohomology X A n).obj P) :=
  TauCeti.CategoryTheory.isZero_cechCohomology_obj _ _ n (fun _ ↦ inferInstanceAs (IsEmpty X)) P

variable {X A} [HasZeroObject A] (F : Sheaf (Opens.grothendieckTopology X) A)

/-- The degree `0` Čech cohomology of a sheaf `F` on `X` is its object of global sections `F(X)`.
-/
def cechCohomologyZeroIso : F.obj.obj (op ⊤) ≅ (cechCohomology X A 0).obj F.obj :=
  TauCeti.CategoryTheory.cechCohomologyZeroIso _ _ isTerminalTop F.obj fun U ↦
    quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U.opens U.isOpenCover F

/-- The identification of the degree `0` Čech cohomology of a sheaf with its global sections is
the augmentation of the Čech complex of any point-neighborhood cover `U`, followed by the
structure map of the colimit at `U`. -/
theorem cechCohomologyZeroIso_hom (U : PointOpenCover X) :
    (cechCohomologyZeroIso F).hom =
      (HomologicalComplex.singleObjHomologySelfIso _ 0 _).inv ≫
        HomologicalComplex.homologyMap
          (TauCeti.CategoryTheory.cechAugmentation U.opens isTerminalTop F.obj) 0 ≫
            (TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct
              (fun _ _ h ↦ h) 0 U).app F.obj :=
  TauCeti.CategoryTheory.cechCohomologyZeroIso_hom PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) isTerminalTop F.obj
    (fun U ↦ quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U.opens U.isOpenCover F) U

end TauCeti.Topology
