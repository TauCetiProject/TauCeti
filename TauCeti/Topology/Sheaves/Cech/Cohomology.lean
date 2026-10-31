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

For a presheaf `P` on an arbitrary topological space `X : Type u`, with values in a
preadditive category with homology and `u`-small products, the degree `n` Čech cohomology
`Hⁿ_Č(X, P)` is the colimit, over open covers ordered by refinement, of the degree `n` cohomology
of the Čech complexes `Č(U, P)`. The transition maps are induced by refinement maps; different
refinement maps between the same two covers induce homotopic maps of Čech complexes, so the
maps on cohomology are well defined.

The colimit is taken over the `u`-small directed preorder `TauCeti.Topology.PointOpenCover X` of
covers indexed by the points of `X`, which is cofinal among all `u`-small open covers
(`TauCeti.Topology.PointOpenCover.exists_refinement`). No separation, compactness or
nonemptiness assumption on `X` is made, and the Čech complexes use all tuples of indices,
including repeated indices and empty intersections.

Every `u`-small open cover `U`, not only a point-neighborhood cover, has a map
`Hⁿ(Č(U, P)) ⟶ Hⁿ_Č(X, P)` (`TauCeti.Topology.toCechCohomology`). It is defined through a chosen
point-neighborhood refinement, but it agrees with the composite through every such refinement
(`TauCeti.Topology.toCechCohomology_eq`), and these maps are compatible with all refinement
maps between covers and natural in `P`.

On the empty space the Čech cohomology vanishes in every degree, for every presheaf, even one
with a nonzero value on the empty open: the empty family is the only point-neighborhood cover,
and its Čech complex is zero.

## Main definitions

* `TauCeti.Topology.cechCohomology X n`: the degree `n` Čech cohomology of presheaves on `X`, as
  a functor of the presheaf.
* `TauCeti.Topology.toCechCohomology P U hU n`: the map from the degree `n` cohomology of the Čech
  complex of the open cover `U` to the Čech cohomology.

## Main results

* `TauCeti.Topology.toCechCohomology_eq`: the map from a cover agrees with the map through any
  point-neighborhood refinement.
* `TauCeti.Topology.homologyMap_cechComplexMap_comp_toCechCohomology`: the maps from covers are
  compatible with refinement maps.
* `TauCeti.Topology.isZero_cechCohomology_of_isEmpty`: Čech cohomology vanishes on the empty
  space.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A, Remark A.4.2 and Definition A.4.3.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe v' u u'

namespace TauCeti.Topology

variable (X : Type u) [TopologicalSpace X] {A : Type u'} [Category.{v'} A] [Preadditive A]
  [HasProducts.{u} A] [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A]
  (n : ℕ)

/-- The degree `n` Čech cohomology `Hⁿ_Č(X, P)` of presheaves `P` on `X`: the colimit, over the
point-neighborhood covers of `X` ordered by refinement, of the degree `n` cohomology of their
Čech complexes. It is reducible to the specialization of `TauCeti.CategoryTheory.cechCohomology`,
so that the structure maps and the lemmas of that colimit apply to it directly. -/
abbrev cechCohomology : ((Opens X)ᵒᵖ ⥤ A) ⥤ A :=
  CategoryTheory.cechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n

variable {X}

/-- The map from the degree `n` cohomology of the Čech complex of a `u`-small open cover `U` to
the Čech cohomology of `X`. It is the map induced by a chosen point-neighborhood refinement of
`U`, followed by the map from that refinement; by `toCechCohomology_eq` it does not depend on
the choice. -/
def toCechCohomology (P : (Opens X)ᵒᵖ ⥤ A) {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    ((cechComplexFunctor U).obj P).homology n ⟶ (cechCohomology X n).obj P :=
  HomologicalComplex.homologyMap
      (CategoryTheory.cechComplexMap P (PointOpenCover.exists_refinement U hU).choose_spec.some)
      n ≫
    CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P
      (PointOpenCover.exists_refinement U hU).choose

/-- Refining a point-neighborhood cover `V` of an open cover `U` further, to a point-neighborhood
cover `W`, does not change the composite of the induced map on cohomology with the map to Čech
cohomology. -/
private lemma homologyMap_comp_toCechCohomology_eq_of_le (P : (Opens X)ᵒᵖ ⥤ A) {ι : Type u}
    {U : ι → Opens X} {V W : PointOpenCover X} (hVW : V ≤ W)
    (ψ : W.toFormalCoproduct ⟶ V.toFormalCoproduct)
    (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P φ) n ≫
        CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P V =
      HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P (ψ ≫ φ)) n ≫
        CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P
          W := by
  rw [CategoryTheory.cechComplexMap_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
    CategoryTheory.homologyMap_cechComplexMap_comp_toCechCohomology _ (fun _ _ h ↦ h) n P hVW]

/-- Any two point-neighborhood refinements of an open cover `U` give the same composite of the
induced map on cohomology with the map to Čech cohomology. -/
private lemma homologyMap_comp_toCechCohomology_eq (P : (Opens X)ᵒᵖ ⥤ A) {ι : Type u}
    {U : ι → Opens X} (V₁ V₂ : PointOpenCover X)
    (φ₁ : V₁.toFormalCoproduct ⟶ FormalCoproduct.mk ι U)
    (φ₂ : V₂.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P φ₁) n ≫
        CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P V₁ =
      HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P φ₂) n ≫
        CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P
          V₂ := by
  -- compare both on the common refinement `V₁.inter V₂`
  rw [homologyMap_comp_toCechCohomology_eq_of_le n P (V₁.le_inter_left V₂)
      ((PointOpenCover.le_iff _ _).1 (V₁.le_inter_left V₂)).some,
    homologyMap_comp_toCechCohomology_eq_of_le n P (V₁.le_inter_right V₂)
      ((PointOpenCover.le_iff _ _).1 (V₁.le_inter_right V₂)).some,
    (CategoryTheory.cechComplexMapHomotopy P _ _).homologyMap_eq n]

/-- The map from the Čech cohomology of an open cover `U` agrees with the map induced by any
point-neighborhood refinement `V` of `U`, followed by the map from `V`. -/
theorem toCechCohomology_eq (P : (Opens X)ᵒᵖ ⥤ A) {ι : Type u} (U : ι → Opens X)
    (hU : IsOpenCover U) (V : PointOpenCover X)
    (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology n P U hU =
      HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P φ) n ≫
        CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P V :=
  homologyMap_comp_toCechCohomology_eq n P _ _ _ _

/-- On a point-neighborhood cover, the map from its Čech cohomology to the Čech cohomology of `X`
is the structure map of the colimit. -/
@[simp]
theorem toCechCohomology_pointOpenCover (P : (Opens X)ᵒᵖ ⥤ A) (V : PointOpenCover X) :
    toCechCohomology n P V.opens V.isOpenCover =
      CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P V := by
  rw [toCechCohomology_eq n P V.opens V.isOpenCover V (𝟙 _), CategoryTheory.cechComplexMap_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]

/-- The maps from the Čech cohomology of open covers are compatible with refinement maps: for a
refinement `φ` of `U` by `V`, the map induced by `φ` on cohomology followed by the map from `V`
is the map from `U`. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_toCechCohomology (P : (Opens X)ᵒᵖ ⥤ A) {ι κ : Type u}
    {U : ι → Opens X} (hU : IsOpenCover U) {V : κ → Opens X} (hV : IsOpenCover V)
    (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) :
    HomologicalComplex.homologyMap (CategoryTheory.cechComplexMap P φ) n ≫
        toCechCohomology n P V hV =
      toCechCohomology n P U hU := by
  obtain ⟨W, ⟨ψ⟩⟩ := PointOpenCover.exists_refinement V hV
  rw [toCechCohomology_eq n P V hV W ψ, toCechCohomology_eq n P U hU W (ψ ≫ φ),
    CategoryTheory.cechComplexMap_comp, HomologicalComplex.homologyMap_comp_assoc]

/-- The maps from the Čech cohomology of open covers are natural in the presheaf. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_naturality {P Q : (Opens X)ᵒᵖ ⥤ A} (α : P ⟶ Q) {ι : Type u}
    (U : ι → Opens X) (hU : IsOpenCover U) :
    toCechCohomology n P U hU ≫ (cechCohomology X n).map α =
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) n ≫
        toCechCohomology n Q U hU := by
  obtain ⟨V, ⟨φ⟩⟩ := PointOpenCover.exists_refinement U hU
  rw [toCechCohomology_eq n P U hU V φ, toCechCohomology_eq n Q U hU V φ, Category.assoc,
    CategoryTheory.toCechCohomology_naturality, ← HomologicalComplex.homologyMap_comp_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc,
    CategoryTheory.cechComplexMap_naturality]

/-- **Čech cohomology vanishes on the empty space**, in every degree and for every presheaf,
including presheaves with a nonzero value on the empty open. -/
theorem isZero_cechCohomology_of_isEmpty [IsEmpty X] (P : (Opens X)ᵒᵖ ⥤ A) :
    IsZero ((cechCohomology X n).obj P) := by
  -- the only point-neighborhood cover is the empty family, whose Čech complex is zero
  let V : PointOpenCover X := default
  let e := CategoryTheory.toCechCohomology PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n P V
  have : IsIso e :=
    CategoryTheory.isIso_toCechCohomology_of_isTop _ (fun _ _ h ↦ h) n P
      fun _ ↦ ⟨⟨isEmptyElim, isEmptyElim⟩⟩
  exact (ShortComplex.isZero_homology_of_isZero_X₂ (((cechComplexFunctor V.opens).obj P).sc n)
    (CategoryTheory.isZero_cechComplexFunctor_obj_X V.opens P n)).of_iso (asIso e).symm

end TauCeti.Topology
