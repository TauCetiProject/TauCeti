/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Refinement
public import TauCeti.Topology.Sheaves.CoverSystems

/-!
# Čech cohomology of presheaves on a topological space

Let `X : Type u` be a topological space and `P : (Opens X)ᵒᵖ ⥤ A` a presheaf with values in a
preadditive category with `u`-small products and homology, for instance `ModuleCat.{u} R`. The
degree `n` Čech cohomology `Ȟⁿ(X, P)` is the colimit, over open covers ordered by refinement, of
the cohomology of the Čech complexes `Č(U, P)`. The transition maps are induced by refinement
maps and do not depend on them, so this is a colimit over a directed preorder, not over the
category of refinement maps, which is not filtered.

All `u`-small open covers do not form a `u`-small preorder, so the colimit is taken over the
cofinal system of point-neighborhood covers `TauCeti.Topology.PointOpenCover X`, which is
`u`-small. Every `u`-small open cover `U` of `X` has a canonical map
`toCechCohomology P n U hU : Hⁿ(Č(U, P)) ⟶ Ȟⁿ(X, P)`, natural with respect to refinements, and
maps out of `Ȟⁿ(X, P)` are determined by their composites with these maps. On a compact space
the finite indexed covers `TauCeti.Topology.FiniteOpenCover X` form another cofinal system, and
their colimit is canonically isomorphic to `Ȟⁿ(X, P)` (`finiteCechCohomologyIso`). Neither
construction assumes any separation axiom or a sheaf condition on `P`.

## Main definitions

* `TauCeti.Topology.cechCohomology P n`: the degree `n` Čech cohomology `Ȟⁿ(X, P)`.
* `TauCeti.Topology.toCechCohomology P n U hU`: the map to it from the cohomology of the Čech
  complex of a `u`-small open cover `U`.
* `TauCeti.Topology.finiteCechCohomologyIso P n`: on a compact space, the isomorphism with the
  colimit over finite indexed covers.

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

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe v' u u'

namespace TauCeti.Topology

variable {X : Type u} [TopologicalSpace X] {A : Type u'} [Category.{v'} A] [Preadditive A]
  [HasProducts.{u} A] [CategoryWithHomology A] (P : (Opens X)ᵒᵖ ⥤ A) (n : ℕ)

/-- The degree `n` cohomology of the Čech complexes of `P` for the point-neighborhood covers of
`X`, as a diagram over their refinement preorder. -/
abbrev PointOpenCover.cechCohomologyDiagram : PointOpenCover X ⥤ A :=
  TauCeti.CategoryTheory.cechCohomologyDiagram P n PointOpenCover.toFormalCoproduct
    fun _ _ h ↦ h

/-- The degree `n` cohomology of the Čech complexes of `P` for the finite indexed covers of `X`,
as a diagram over their refinement preorder. -/
abbrev FiniteOpenCover.cechCohomologyDiagram : FiniteOpenCover X ⥤ A :=
  TauCeti.CategoryTheory.cechCohomologyDiagram P n FiniteOpenCover.toFormalCoproduct
    fun _ _ h ↦ h

variable [HasColimitsOfShape (PointOpenCover X) A]

/-- The degree `n` **Čech cohomology** `Ȟⁿ(X, P)` of a presheaf `P` on `X`: the colimit of the
cohomology of the Čech complexes of `P` over the point-neighborhood covers of `X`, a `u`-small
system of open covers cofinal among all `u`-small open covers. -/
@[expose]
def cechCohomology : A :=
  colimit (PointOpenCover.cechCohomologyDiagram P n)

/-- The map `Hⁿ(Č(U, P)) ⟶ Ȟⁿ(X, P)` from the Čech cohomology of a fixed `u`-small open cover:
the map induced by a refinement of `U` by a point-neighborhood cover, followed by the
coprojection. It depends on neither choice. -/
def toCechCohomology {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    (cechCohomologyFunctor P n).obj (op (FormalCoproduct.mk ι U)) ⟶ cechCohomology P n :=
  toCechCohomologyColimit P n _ _ _ (PointOpenCover.exists_refinement U hU)

/-- For a point-neighborhood cover, `toCechCohomology` is the coprojection of the colimit. -/
@[simp]
theorem toCechCohomology_opens (V : PointOpenCover X) :
    toCechCohomology P n V.opens V.isOpenCover =
      colimit.ι (PointOpenCover.cechCohomologyDiagram P n) V :=
  toCechCohomologyColimit_self P n _ _ V _

/-- **`toCechCohomology` is natural with respect to refinements.** If the open cover `V` refines
the open cover `U` through `φ`, the map from the Čech cohomology of `U` to `Ȟⁿ(X, P)` factors
through the map induced by `φ`. -/
@[reassoc (attr := simp)]
theorem cechCohomologyFunctor_map_comp_toCechCohomology {ι κ : Type u} {U : ι → Opens X}
    {V : κ → Opens X} (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (hU : IsOpenCover U)
    (hV : IsOpenCover V) :
    (cechCohomologyFunctor P n).map φ.op ≫ toCechCohomology P n V hV =
      toCechCohomology P n U hU :=
  cechCohomologyFunctor_map_comp_toCechCohomologyColimit P n _ _ φ _

/-- Maps out of `Ȟⁿ(X, P)` are determined by their composites with the maps from the Čech
cohomology of the point-neighborhood covers. -/
@[ext]
theorem cechCohomology_hom_ext {B : A} {f g : cechCohomology P n ⟶ B}
    (h : ∀ V : PointOpenCover X,
      toCechCohomology P n V.opens V.isOpenCover ≫ f =
        toCechCohomology P n V.opens V.isOpenCover ≫ g) : f = g :=
  colimit.hom_ext fun V ↦ by
    have hV := h V
    rw [toCechCohomology_opens] at hV
    -- `hV` is stated for the family `FormalCoproduct.mk X V.opens`, which is the abbreviation
    -- `V.toFormalCoproduct` indexing the colimit
    exact hV

/-- **Finite covers compute Čech cohomology on a compact space.** On a compact space, the
colimit of the cohomology of the Čech complexes over finite indexed covers is canonically
isomorphic to `Ȟⁿ(X, P)`. No separation axiom is assumed. -/
def finiteCechCohomologyIso [CompactSpace X] [HasColimitsOfShape (FiniteOpenCover X) A] :
    colimit (FiniteOpenCover.cechCohomologyDiagram P n) ≅ cechCohomology P n :=
  cechCohomologyColimitIso P n _ _ _ _
    (fun W ↦ PointOpenCover.exists_refinement W.opens W.isOpenCover)
    (fun V ↦ FiniteOpenCover.exists_refinement V.opens V.isOpenCover)

/-- The isomorphism `finiteCechCohomologyIso` sends the coprojection at a finite cover to the
map `toCechCohomology` of that cover. -/
@[reassoc (attr := simp)]
theorem colimit_ι_finiteCechCohomologyIso_hom [CompactSpace X]
    [HasColimitsOfShape (FiniteOpenCover X) A] (W : FiniteOpenCover X) :
    colimit.ι (FiniteOpenCover.cechCohomologyDiagram P n) W ≫
        (finiteCechCohomologyIso P n).hom =
      toCechCohomology P n W.opens W.isOpenCover := by
  rw [finiteCechCohomologyIso, cechCohomologyColimitIso_hom]
  exact colimit_ι_cechCohomologyColimitMap P n _ _ _ _ _ W

/-- The inverse of `finiteCechCohomologyIso` sends the image of the Čech cohomology of any
`u`-small open cover to the map induced by a refinement by a finite indexed cover, followed by
the coprojection at that finite cover. -/
@[reassoc]
theorem toCechCohomology_comp_finiteCechCohomologyIso_inv [CompactSpace X]
    [HasColimitsOfShape (FiniteOpenCover X) A] {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U)
    (W : FiniteOpenCover X) (φ : W.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology P n U hU ≫ (finiteCechCohomologyIso P n).inv =
      (cechCohomologyFunctor P n).map φ.op ≫
        colimit.ι (FiniteOpenCover.cechCohomologyDiagram P n) W := by
  rw [Iso.comp_inv_eq, Category.assoc, colimit_ι_finiteCechCohomologyIso_hom,
    cechCohomologyFunctor_map_comp_toCechCohomology]

end TauCeti.Topology
