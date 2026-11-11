/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Čech cohomology from arbitrary small covers, and finite covers of compact spaces

The Čech cohomology `TauCeti.Topology.cechCohomology X A n` of presheaves on a topological space
`X` is the colimit over the point-neighborhood covers of `X`. Every `u`-small open cover `U` of
`X` is refined by a point-neighborhood cover, so it has a canonical map `toCechCohomology A n U hU`
from its Čech cohomology to `TauCeti.Topology.cechCohomology X A n`, natural in the presheaf and
with respect to refinements, and independent of the chosen refinement.

On a compact space, the finite indexed covers `TauCeti.Topology.FiniteOpenCover X` form another
cofinal system of covers. The colimit of the Čech cohomologies over them is canonically isomorphic
to the Čech cohomology (`finiteCechCohomologyIso`), compatibly with the maps from every small open
cover. No separation axiom is assumed.

## Main definitions

* `TauCeti.Topology.toCechCohomology A n U hU`: the map to the Čech cohomology from the Čech
  cohomology of a `u`-small open cover `U`.
* `TauCeti.Topology.finiteCechCohomologyIso X A n`: on a compact space, the isomorphism between
  the colimit over finite indexed covers and the Čech cohomology.

## Main results

* `TauCeti.Topology.cechComplexHomologyMap_comp_toCechCohomology`: `toCechCohomology` is natural
  with respect to refinements of open covers.
* `TauCeti.Topology.toCechCohomology_comp_finiteCechCohomologyIso_inv`: the inverse of
  `finiteCechCohomologyIso` on the image of the Čech cohomology of a small open cover.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A: Definition A.4.3 and
  Lemma A.4.4, for Čech cohomology as a colimit over covers and the cofinality of finite covers
  of compact spaces.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe v' u u'

namespace TauCeti.Topology

variable {X : TopCat.{u}} (A : Type u') [Category.{v'} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A] (n : ℕ)

/-- The map from the Čech cohomology `Hⁿ(Č(U, P))` of a `u`-small open cover `U` of `X` to the
Čech cohomology of `P` on `X`, natural in the presheaf `P`: the map induced by a refinement of `U`
by a point-neighborhood cover, followed by the structure map of the colimit. It depends on neither
choice (`TauCeti.CategoryTheory.toCechCohomology_eq`). -/
def toCechCohomology {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    cechComplexFunctor U ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechCohomology X A n :=
  TauCeti.CategoryTheory.toCechCohomology A _ _ n (FormalCoproduct.mk ι U)
    (PointOpenCover.exists_refinement U hU)

/-- For a point-neighborhood cover, `toCechCohomology` is the structure map of the colimit. -/
@[simp]
theorem toCechCohomology_opens (V : PointOpenCover X) :
    toCechCohomology A n V.opens V.isOpenCover =
      TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V :=
  TauCeti.CategoryTheory.toCechCohomology_self A _ _ n V _

/-- Compute the structure map of any small cover using any point-neighborhood cover
refining it, independently of the refinement chosen in its definition. -/
theorem toCechCohomology_eq {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U)
    (V : PointOpenCover X) (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology A n U hU =
      TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫
        TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) n V :=
  TauCeti.CategoryTheory.toCechCohomology_eq A _ _ n _ V φ

/-- **`toCechCohomology` is natural with respect to refinements.** If the open cover `V` refines
the open cover `U` through `φ`, the map from the Čech cohomology of `U` to the Čech cohomology on
`X` factors through the map induced by `φ`. -/
@[reassoc]
theorem cechComplexHomologyMap_comp_toCechCohomology {ι κ : Type u} {U : ι → Opens X}
    {V : κ → Opens X} (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (hU : IsOpenCover U)
    (hV : IsOpenCover V) :
    TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫ toCechCohomology A n V hV =
      toCechCohomology A n U hU :=
  TauCeti.CategoryTheory.cechComplexHomologyMap_comp_toCechCohomology A _ _ n φ _

variable (X) [CompactSpace X] [HasColimitsOfShape (FiniteOpenCover X) A]

/-- **Finite covers compute Čech cohomology on a compact space.** On a compact space, the colimit
of the Čech cohomologies over the finite indexed covers is canonically isomorphic to the Čech
cohomology, naturally in the presheaf. No separation axiom is assumed. -/
def finiteCechCohomologyIso :
    TauCeti.CategoryTheory.cechCohomology A (FiniteOpenCover.toFormalCoproduct (X := X))
        (fun _ _ h ↦ h) n ≅ cechCohomology X A n :=
  TauCeti.CategoryTheory.cechCohomologyIso A _ _ _ _ n
    (fun W ↦ PointOpenCover.exists_refinement W.opens W.isOpenCover)
    (fun V ↦ FiniteOpenCover.exists_refinement V.opens V.isOpenCover)

/-- The isomorphism `finiteCechCohomologyIso` sends the structure map at a finite cover to the map
`toCechCohomology` of that cover. -/
@[reassoc (attr := simp)]
theorem cechCohomologyι_comp_finiteCechCohomologyIso_hom (W : FiniteOpenCover X) :
    TauCeti.CategoryTheory.cechCohomologyι FiniteOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n W ≫
        (finiteCechCohomologyIso X A n).hom =
      toCechCohomology A n W.opens W.isOpenCover := by
  rw [finiteCechCohomologyIso, TauCeti.CategoryTheory.cechCohomologyIso_hom]
  exact TauCeti.CategoryTheory.cechCohomologyι_comp_cechCohomologyComparison A _ _ _ _ n _ W

/-- The inverse of `finiteCechCohomologyIso` sends the image of the Čech cohomology of any
`u`-small open cover to the map induced by a refinement by a finite indexed cover, followed by the
structure map at that finite cover. -/
@[reassoc]
theorem toCechCohomology_comp_finiteCechCohomologyIso_inv {ι : Type u} (U : ι → Opens X)
    (hU : IsOpenCover U) (W : FiniteOpenCover X)
    (φ : W.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology A n U hU ≫ (finiteCechCohomologyIso X A n).inv =
      TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫
        TauCeti.CategoryTheory.cechCohomologyι FiniteOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) n W := by
  rw [finiteCechCohomologyIso, TauCeti.CategoryTheory.cechCohomologyIso_inv]
  exact (TauCeti.CategoryTheory.toCechCohomology_comp_cechCohomologyComparison A _ _ _ _ n _ _
    _).trans (TauCeti.CategoryTheory.toCechCohomology_eq A _ _ n _ W φ)

end TauCeti.Topology
