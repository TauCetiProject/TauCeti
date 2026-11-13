/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Degree zero Čech cohomology for a covering of a site

Let `(C, J)` be a site with finite products and a terminal object `T`, and let `U` be a family of
objects whose maps to `T` generate a covering sieve. For a sheaf `F`, the sheaf condition for this
sieve says that the augmentation `F(T) ⟶ Č(U, F)` is a quasi-isomorphism in degree `0`: the degree
`0` Čech cohomology `H⁰(U, F)` is the object of global sections. For an abelian sheaf this is also
the degree `0` sheaf cohomology `H⁰(F)`, and the identification is natural in `F` and compatible
with refinement of coverings. This is the base case of Leray's acyclicity theorem
(`TauCeti.CategoryTheory.homologyCechComplexIsoH`).

## Main results

* `TauCeti.CategoryTheory.quasiIsoAt_cechAugmentation_zero_of_mem`: for a sheaf and a covering
  family, the augmentation of the Čech complex is a quasi-isomorphism in degree `0`;
* `TauCeti.CategoryTheory.homologyZeroCechIso`: for an abelian sheaf and a covering family,
  `H⁰(U, F) ≅ H⁰(F)`, induced by the augmentation
  (`TauCeti.CategoryTheory.homologyMap_cechAugmentation_comp_homologyZeroCechIso_hom`), naturally
  in `F`
  (`TauCeti.CategoryTheory.homologyMap_comp_homologyZeroCechIso_hom`) and compatibly with
  refinement maps
  (`TauCeti.CategoryTheory.homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom`).

## References

The formalization is adapted from split 6 of the
[lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/lookahead/SchemeAndStackFoundations/leray-spectral-sequence),
at commit `877ee62`
(<https://github.com/roed-math/TauCeti-w2-fresh/tree/877ee6253118ae038b46aca137f48841db354fe9>),
where it is part of the proof of Leray's acyclicity theorem; it is split off here so that the
degree `0` comparison for open covers can use it.

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech cohomology
  and cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  {ι : Type v} (U : ι → C) {T : C} (hT : IsTerminal T)
  (hU : Sieve.ofArrows U (fun i ↦ hT.from (U i)) ∈ J T)

include hU

omit [HasFiniteProducts C] in
/-- A sheaf satisfies the sheaf condition for a covering family of maps to the terminal object,
in the form used by the augmentation of the Čech complex. -/
theorem isSheafFor_ofArrows_of_mem {A : Type*} [Category* A] (F : Sheaf J A) (E : Aᵒᵖ) :
    (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (F.obj ⋙ coyoneda.obj E) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact F.property E.unop _ hU

/-- For a sheaf and a covering family of maps to the terminal object, the augmentation of the
Čech complex is a quasi-isomorphism in degree `0`: the degree `0` Čech cohomology is the object of
global sections. -/
theorem quasiIsoAt_cechAugmentation_zero_of_mem {A : Type*} [Category* A] [Preadditive A]
    [HasProducts.{v} A] [HasZeroObject A] [CategoryWithHomology A] (F : Sheaf J A) :
    QuasiIsoAt (cechAugmentation U hT F.obj) 0 :=
  (quasiIsoAt_cechAugmentation_zero_iff U hT F.obj).2 (isSheafFor_ofArrows_of_mem U hT hU F)

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The degree `0` Čech cohomology of a sheaf for a covering family is the group of global
sections, which is also the degree `0` sheaf cohomology. -/
def homologyZeroCechIso (F : Sheaf J AddCommGrpCat.{v}) :
    ((cechComplexFunctor U).obj F.obj).homology 0 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F 0) :=
  have := quasiIsoAt_cechAugmentation_zero_of_mem U hT hU F
  (asIso (HomologicalComplex.homologyMap (cechAugmentation U hT F.obj) 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _ ≪≫
      ((_root_.CategoryTheory.Sheaf.H.equiv₀ F hT).symm.toAddCommGrpIso)

/-- The identification of degree `0` Čech cohomology with degree `0` sheaf cohomology is induced
by the augmentation `F(T) ⟶ Č(U, F)`: composed with it, it is the identification of the global
sections `F(T)` with `H⁰(F)`. -/
@[reassoc (attr := simp)]
theorem homologyMap_cechAugmentation_comp_homologyZeroCechIso_hom (F : Sheaf J AddCommGrpCat.{v}) :
    HomologicalComplex.homologyMap (cechAugmentation U hT F.obj) 0 ≫
        (homologyZeroCechIso U hT hU F).hom =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _).hom ≫
        ((_root_.CategoryTheory.Sheaf.H.equiv₀ F hT).symm.toAddCommGrpIso).hom := by
  have := quasiIsoAt_cechAugmentation_zero_of_mem U hT hU F
  simp only [homologyZeroCechIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]

/-- The identification of degree `0` Čech cohomology with degree `0` sheaf cohomology is natural
in the sheaf. -/
@[reassoc (attr := simp)]
theorem homologyMap_comp_homologyZeroCechIso_hom {P Q : Sheaf J AddCommGrpCat.{v}} (g : P ⟶ Q) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map g.hom) 0 ≫
        (homologyZeroCechIso U hT hU Q).hom =
      (homologyZeroCechIso U hT hU P).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  have := quasiIsoAt_cechAugmentation_zero_of_mem U hT hU P
  have := quasiIsoAt_cechAugmentation_zero_of_mem U hT hU Q
  rw [← cancel_epi (HomologicalComplex.homologyMap (cechAugmentation U hT P.obj) 0)]
  simp only [homologyZeroCechIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← HomologicalComplex.homologyMap_comp_assoc, cechAugmentation_naturality]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc]
  congr 1
  ext x
  exact (_root_.CategoryTheory.Sheaf.H.equiv₀_symm_naturality hT g x).symm

/-- Refinement maps commute with the identification of degree `0` Čech cohomology with the global
sections. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom {κ : Type v} (V : κ → C)
    (hV : Sieve.ofArrows V (fun i ↦ hT.from (V i)) ∈ J T) (F : Sheaf J AddCommGrpCat.{v})
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 0 ≫
        (homologyZeroCechIso U hT hU F).hom = (homologyZeroCechIso V hT hV F).hom := by
  have := quasiIsoAt_cechAugmentation_zero_of_mem V hT hV F
  rw [← cancel_epi (HomologicalComplex.homologyMap (cechAugmentation V hT F.obj) 0)]
  simp only [homologyZeroCechIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← HomologicalComplex.homologyMap_comp_assoc, cechAugmentation_comp_cechComplexMap]
  have := quasiIsoAt_cechAugmentation_zero_of_mem U hT hU F
  simp only [IsIso.hom_inv_id_assoc]

end TauCeti.CategoryTheory
