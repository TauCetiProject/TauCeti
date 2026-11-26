/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.TotalComplexShift
public import TauCeti.Algebra.Homology.Functor.Extend
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Colimit

/-!
# Čech hypercohomology commutes with shifts

Let `P` be a presheaf of integer-graded cochain complexes and `y` an integer. Shifting the
coefficients, `P[y] = P ⋙ shiftFunctor _ y` with the native convention `P[y]^q = P^(q+y)` and
differential `(-1)^y d`, shifts the total Čech complex of every family `U`: there is an
isomorphism `Tot Č(U, P[y]) ≅ (Tot Č(U, P))[y]` (`TauCeti.CategoryTheory.cechTotalComplexShiftIso`),
natural in `P` and compatible with the maps induced by morphisms of families. The Čech complex of
`P[y]` is the termwise shift of the Čech complex of `P`, so it is Mathlib's
`HomologicalComplex₂.totalShift₂Iso` for the Čech bicomplex of `P`: on the summand in Čech
degree `p` it is the multiplication by `(-1)^(p y)` (`HomologicalComplex₂.ι_totalShift₂Iso_hom_f`).
These signs are needed because the internal differential of `P[y]` carries the sign `(-1)^y` while
its Čech differential does not.

Passing to cohomology and to the colimit over a system of families, Čech hypercohomology commutes
with shifts: `Hⁿ(P[y]) ≅ Hⁿ'(P)` for `y + n = n'`, naturally in `P`
(`TauCeti.CategoryTheory.cechHypercohomologyShiftIso`). This applies in particular to the Čech
hypercohomology `TauCeti.Topology.cechHypercohomology` of a presheaf of complexes on a topological
space, the colimit over point-neighborhood covers. For instance, the hypercohomology of a presheaf
placed in degree `-k` is that of the same presheaf placed in degree `0`, moved up by `k` degrees.

## Main definitions

* `TauCeti.CategoryTheory.cechTotalComplexShiftIso`: `Tot Č(U, P[y]) ≅ (Tot Č(U, P))[y]`.
* `TauCeti.CategoryTheory.cechHypercohomologyShiftIso`: `Hⁿ(P[y]) ≅ Hⁿ'(P)` for `y + n = n'`.

## Main results

* `TauCeti.CategoryTheory.cechTotalComplexShiftIso_hom_naturality`: naturality in the presheaf.
* `TauCeti.CategoryTheory.cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom`: compatibility
  with the maps induced by morphisms of families.
* `TauCeti.CategoryTheory.cechHypercohomologyι_app_cechHypercohomologyShiftIso_hom`: on the
  structure map of each family, the isomorphism on hypercohomology is the one induced by
  `cechTotalComplexShiftIso` on cohomology.
* `TauCeti.CategoryTheory.cechHypercohomologyShiftIso_hom_naturality`: naturality in the presheaf.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (total Čech complexes of complexes of
  presheaves).
* The signs are those of Joël Riou's Mathlib construction `HomologicalComplex₂.totalShift₂Iso`
  (`Mathlib.Algebra.Homology.TotalComplexShift`).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex₂

universe w t v v' u u'

namespace TauCeti.CategoryTheory

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [HasZeroObject A]
  [HasCoproducts.{0} A]

section Bicomplex

variable {y : ℤ} {K K' L L' : CochainComplex (CochainComplex A ℤ) ℕ}

/-- The isomorphism `Tot(K'.extend) ≅ (Tot K.extend)[y]` induced by an identification of `K'` with
the termwise shift of the bicomplex `K`. -/
private def totalShiftIsoOfIso
    (eK : ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).obj K ≅ K') :
    total (K'.extend ComplexShape.embeddingUpNat) (ComplexShape.up ℤ) ≅
      (total (K.extend ComplexShape.embeddingUpNat) (ComplexShape.up ℤ))⟦y⟧ :=
  total.mapIso ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso eK.symm ≪≫
      ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso _ K).symm) _ ≪≫
    totalShift₂Iso _ y

/-- `totalShiftIsoOfIso` is natural in maps of bicomplexes compatible with the
identifications. -/
private lemma totalShiftIsoOfIso_hom_naturality
    (eK : ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).obj K ≅ K')
    (eL : ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).obj L ≅ L')
    (g : K ⟶ L) (g' : K' ⟶ L')
    (hg : g' ≫ eL.inv =
      eK.inv ≫ ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map g) :
    total.map (HomologicalComplex.extendMap g' ComplexShape.embeddingUpNat) _ ≫
        (totalShiftIsoOfIso eL).hom =
      (totalShiftIsoOfIso eK).hom ≫
        (total.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) _)⟦y⟧' := by
  have h₂ : HomologicalComplex.extendMap
        (((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map g)
          ComplexShape.embeddingUpNat ≫
        ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso _ L).inv =
      ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso _ K).inv ≫
        ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map
          (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      Functor.mapHomologicalComplexExtendObjIso_hom_naturality, Iso.inv_hom_id_assoc]
  simp only [totalShiftIsoOfIso, Iso.trans_hom, total.mapIso_hom, Functor.mapIso_hom,
    Iso.symm_hom, ComplexShape.Embedding.extendFunctor_map, ← total.map_comp_assoc,
    ← HomologicalComplex.extendMap_comp_assoc, hg]
  rw [HomologicalComplex.extendMap_comp, Category.assoc, h₂, ← Category.assoc, total.map_comp,
    Category.assoc, totalShift₂Iso_hom_naturality, total.map_comp]
  simp only [Category.assoc]

end Bicomplex

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasProducts.{w} A]

section Total

variable {ι κ : Type w} (U : ι → C) {V : κ → C} (y : ℤ)

/-- **Total Čech complexes commute with shifting the coefficients.** For a presheaf `P` of
cochain complexes, the total Čech complex of the shifted presheaf `P[y]` is the shift of the total
Čech complex of `P`, naturally in `P` (`cechTotalComplexShiftIso_hom_naturality`). The shift is
moved out of the Čech complex (`cechComplexFunctorMapIso`) and through the extension to `ℤ`
(`CategoryTheory.Functor.mapHomologicalComplexExtendObjIso`); on the resulting bicomplex this is
Mathlib's `HomologicalComplex₂.totalShift₂Iso` (`cechTotalComplexShiftIso_hom`), which multiplies
the summand in Čech degree `p` by `(-1)^(p y)` (`HomologicalComplex₂.ι_totalShift₂Iso_hom_f`). -/
def cechTotalComplexShiftIso (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexFunctor U).obj (P ⋙ shiftFunctor (CochainComplex A ℤ) y) ≅
      ((cechTotalComplexFunctor U).obj P)⟦y⟧ :=
  totalShiftIsoOfIso ((cechComplexFunctorMapIso U (shiftFunctor _ y)).app P)

/-- `cechTotalComplexShiftIso` is the total map of the inverse of `cechComplexFunctorMapIso`,
extended to `ℤ` and followed by the inverse of
`CategoryTheory.Functor.mapHomologicalComplexExtendObjIso`, composed with
`HomologicalComplex₂.totalShift₂Iso`. -/
lemma cechTotalComplexShiftIso_hom (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexShiftIso U y P).hom =
      total.map (HomologicalComplex.extendMap
          ((cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app P)
            ComplexShape.embeddingUpNat ≫
          ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso _ _).inv) _ ≫
        (totalShift₂Iso (((cechComplexFunctor U).obj P).extend
          ComplexShape.embeddingUpNat) y).hom :=
  (rfl)

/-- `cechTotalComplexShiftIso` is natural in the presheaf of complexes. -/
@[reassoc]
lemma cechTotalComplexShiftIso_hom_naturality {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechTotalComplexFunctor U).map (Functor.whiskerRight α (shiftFunctor _ y)) ≫
        (cechTotalComplexShiftIso U y Q).hom =
      (cechTotalComplexShiftIso U y P).hom ≫ ((cechTotalComplexFunctor U).map α)⟦y⟧' := by
  rw [cechTotalComplexFunctor_map, cechTotalComplexFunctor_map]
  exact totalShiftIsoOfIso_hom_naturality _ _ _ _
    ((cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.naturality α)

variable {U} in
/-- **`cechTotalComplexShiftIso` commutes with refinement maps.** For a morphism of families `φ`
from `U` to `V`, the map induced by `φ` on the total Čech complexes of `P[y]` corresponds to the
shift of the map it induces on those of `P`. -/
@[reassoc]
theorem cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom (P : Cᵒᵖ ⥤ CochainComplex A ℤ)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexMap (P ⋙ shiftFunctor (CochainComplex A ℤ) y) φ ≫
        (cechTotalComplexShiftIso U y P).hom =
      (cechTotalComplexShiftIso V y P).hom ≫ (cechTotalComplexMap P φ)⟦y⟧' := by
  rw [cechTotalComplexMap_def, cechTotalComplexMap_def]
  refine totalShiftIsoOfIso_hom_naturality _ _ _ _ ?_
  rw [Iso.comp_inv_eq, Category.assoc, Iso.app_hom,
    cechComplexFunctorMapIso_hom_app_comp_cechComplexMap, ← Iso.app_hom, Iso.inv_hom_id_assoc]

variable {U} in
/-- The inverse of `cechTotalComplexShiftIso` commutes with the maps induced by morphisms of
families: this is `cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom` for the inverses. -/
@[reassoc]
theorem shiftFunctor_map_cechTotalComplexMap_comp_cechTotalComplexShiftIso_inv
    (P : Cᵒᵖ ⥤ CochainComplex A ℤ) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechTotalComplexMap P φ)⟦y⟧' ≫ (cechTotalComplexShiftIso U y P).inv =
      (cechTotalComplexShiftIso V y P).inv ≫
        cechTotalComplexMap (P ⋙ shiftFunctor (CochainComplex A ℤ) y) φ := by
  rw [Iso.comp_inv_eq, Category.assoc, cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom,
    Iso.inv_hom_id_assoc]

end Total

section Hypercohomology

variable [CategoryWithHomology A] {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (y n n' : ℤ) (h : y + n = n')
  [HasColimitsOfShape J A]

/-- **Čech hypercohomology commutes with shifts.** For a system `E` of families and a presheaf
`P` of cochain complexes, the degree `n` Čech hypercohomology of the shifted presheaf `P[y]` is
the degree `n'` Čech hypercohomology of `P`, where `y + n = n'`. It is induced on the colimit by
the isomorphisms `cechTotalComplexShiftIso` of the total Čech complexes of the families of `E`,
followed by the identification of the cohomology of a shifted complex
(`cechHypercohomologyι_app_cechHypercohomologyShiftIso_hom`), and it is natural in `P`
(`cechHypercohomologyShiftIso_hom_naturality`). -/
def cechHypercohomologyShiftIso (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechHypercohomology A E hE n).obj (P ⋙ shiftFunctor (CochainComplex A ℤ) y) ≅
      (cechHypercohomology A E hE n').obj P where
  hom := cechHypercohomologyDesc E hE n
    (fun j ↦ HomologicalComplex.homologyMap (cechTotalComplexShiftIso (E j).obj y P).hom n ≫
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso y n n' h).hom.app
        ((cechTotalComplexFunctor (E j).obj).obj P) ≫
      (cechHypercohomologyι E hE n' j).app P)
    fun i j hij φ ↦ by
      rw [← HomologicalComplex.homologyMap_comp_assoc,
        cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom,
        HomologicalComplex.homologyMap_comp_assoc,
        ← homologyMap_cechTotalComplexMap_comp_cechHypercohomologyι_app E hE n' hij φ P]
      congr 1
      -- `homologyMap (g⟦y⟧') n` is the image of `g` under the shifted homology functor
      exact ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
        y n n' h).hom.naturality_assoc (cechTotalComplexMap P φ) _
  inv := cechHypercohomologyDesc E hE n'
    (fun j ↦
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso y n n' h).inv.app
          ((cechTotalComplexFunctor (E j).obj).obj P) ≫
        HomologicalComplex.homologyMap (cechTotalComplexShiftIso (E j).obj y P).inv n ≫
        (cechHypercohomologyι E hE n j).app (P ⋙ shiftFunctor (CochainComplex A ℤ) y))
    fun i j hij φ ↦ by
      rw [← homologyMap_cechTotalComplexMap_comp_cechHypercohomologyι_app E hE n hij φ,
        ← HomologicalComplex.homologyMap_comp_assoc,
        ← shiftFunctor_map_cechTotalComplexMap_comp_cechTotalComplexShiftIso_inv,
        HomologicalComplex.homologyMap_comp_assoc]
      -- `homologyMap (g⟦y⟧') n` is the image of `g` under the shifted homology functor
      exact ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
        y n n' h).inv.naturality_assoc (cechTotalComplexMap P φ) _
  hom_inv_id := by
    ext j
    rw [cechHypercohomologyι_app_cechHypercohomologyDesc_assoc, Category.assoc, Category.assoc,
      cechHypercohomologyι_app_cechHypercohomologyDesc, Iso.hom_inv_id_app_assoc,
      ← HomologicalComplex.homologyMap_comp_assoc, Iso.hom_inv_id,
      HomologicalComplex.homologyMap_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    ext j
    rw [cechHypercohomologyι_app_cechHypercohomologyDesc_assoc, Category.assoc, Category.assoc,
      cechHypercohomologyι_app_cechHypercohomologyDesc, ← HomologicalComplex.homologyMap_comp_assoc,
      Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc, Category.comp_id]

/-- On the structure map of a family `E j`, `cechHypercohomologyShiftIso` is the map induced by
`cechTotalComplexShiftIso` on cohomology, followed by the identification of the cohomology of a
shifted complex. -/
@[reassoc (attr := simp)]
lemma cechHypercohomologyι_app_cechHypercohomologyShiftIso_hom (P : Cᵒᵖ ⥤ CochainComplex A ℤ)
    (j : J) :
    (cechHypercohomologyι E hE n j).app (P ⋙ shiftFunctor (CochainComplex A ℤ) y) ≫
        (cechHypercohomologyShiftIso E hE y n n' h P).hom =
      HomologicalComplex.homologyMap (cechTotalComplexShiftIso (E j).obj y P).hom n ≫
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso y n n' h).hom.app
          ((cechTotalComplexFunctor (E j).obj).obj P) ≫
        (cechHypercohomologyι E hE n' j).app P :=
  cechHypercohomologyι_app_cechHypercohomologyDesc _ _ _ _ _ _

/-- On the structure map of a family `E j`, the inverse of `cechHypercohomologyShiftIso` is the
identification of the cohomology of a shifted complex, followed by the map induced by the inverse
of `cechTotalComplexShiftIso` on cohomology. -/
@[reassoc (attr := simp)]
lemma cechHypercohomologyι_app_cechHypercohomologyShiftIso_inv (P : Cᵒᵖ ⥤ CochainComplex A ℤ)
    (j : J) :
    (cechHypercohomologyι E hE n' j).app P ≫ (cechHypercohomologyShiftIso E hE y n n' h P).inv =
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso y n n' h).inv.app
          ((cechTotalComplexFunctor (E j).obj).obj P) ≫
        HomologicalComplex.homologyMap (cechTotalComplexShiftIso (E j).obj y P).inv n ≫
        (cechHypercohomologyι E hE n j).app (P ⋙ shiftFunctor (CochainComplex A ℤ) y) :=
  cechHypercohomologyι_app_cechHypercohomologyDesc _ _ _ _ _ _

/-- `cechHypercohomologyShiftIso` is natural in the presheaf of complexes. -/
@[reassoc]
lemma cechHypercohomologyShiftIso_hom_naturality {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechHypercohomology A E hE n).map (Functor.whiskerRight α (shiftFunctor _ y)) ≫
        (cechHypercohomologyShiftIso E hE y n n' h Q).hom =
      (cechHypercohomologyShiftIso E hE y n n' h P).hom ≫
        (cechHypercohomology A E hE n').map α := by
  ext j
  rw [cechHypercohomologyι_naturality_assoc,
    cechHypercohomologyι_app_cechHypercohomologyShiftIso_hom,
    cechHypercohomologyι_app_cechHypercohomologyShiftIso_hom_assoc,
    cechHypercohomologyι_naturality, ← HomologicalComplex.homologyMap_comp_assoc,
    cechTotalComplexShiftIso_hom_naturality, HomologicalComplex.homologyMap_comp_assoc]
  congr 1
  -- `homologyMap (g⟦y⟧') n` is the image of `g` under the shifted homology functor
  exact ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
    y n n' h).hom.naturality_assoc ((cechTotalComplexFunctor (E j).obj).map α) _

end Hypercohomology

end TauCeti.CategoryTheory
