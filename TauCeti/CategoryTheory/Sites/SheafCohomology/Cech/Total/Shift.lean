/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.Algebra.Homology.TotalComplex.ExtendShift
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Colimit

/-!
# Čech hypercohomology commutes with shifts

Let `P` be a presheaf of integer-graded cochain complexes and `y` an integer. Shifting the
coefficients, `P[y] = P ⋙ shiftFunctor _ y` with the native convention `P[y]^q = P^(q+y)` and
differential `(-1)^y d`, shifts the total Čech complex of every family `U`: there is an
isomorphism `Tot Č(U, P[y]) ≅ (Tot Č(U, P))[y]` (`TauCeti.CategoryTheory.cechTotalComplexShiftIso`),
natural in `P` and compatible with the maps induced by morphisms of families. The Čech complex of
`P[y]` is the termwise shift of the Čech complex of `P`, so it is
`HomologicalComplex₂.totalExtendShift₂Iso`, built from Mathlib's
`HomologicalComplex₂.totalShift₂Iso`, for the Čech bicomplex of `P`: on the summand in Čech
degree `p` it is the multiplication by `(-1)^(p y)`
(`TauCeti.CategoryTheory.ι_cechTotalComplexShiftIso_hom_f`).
These signs are needed because the internal differential of `P[y]` carries the sign `(-1)^y` while
its Čech differential does not.

Passing to cohomology and to the colimit over a system of families, Čech hypercohomology commutes
with shifts: `Hⁿ(P[y]) ≅ Hⁿ'(P)` for `y + n = n'`, naturally in `P`
(`TauCeti.CategoryTheory.cechHypercohomologyShiftIso`). This applies in particular to the Čech
hypercohomology `TauCeti.Topology.cechHypercohomology` of a presheaf of complexes on a topological
space, the colimit over point-neighborhood covers. For instance, the degree `n` hypercohomology of
a presheaf placed in degree `-k` is the degree `n + k` hypercohomology of the same presheaf placed
in degree `0`.

## Main definitions

* `TauCeti.CategoryTheory.cechTotalComplexShiftIso`: `Tot Č(U, P[y]) ≅ (Tot Č(U, P))[y]`.
* `TauCeti.CategoryTheory.cechHypercohomologyShiftIso`: `Hⁿ(P[y]) ≅ Hⁿ'(P)` for `y + n = n'`.

## Main results

* `TauCeti.CategoryTheory.ι_cechTotalComplexShiftIso_hom_f`: on the summand in Čech degree `p`,
  `cechTotalComplexShiftIso` is the identification of the terms up to the sign `(-1)^(p y)`.
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

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasProducts.{w} A]

section Total

variable {ι κ : Type w} (U : ι → C) {V : κ → C} (y : ℤ)

/-- **Total Čech complexes commute with shifting the coefficients.** For a presheaf `P` of
cochain complexes, the total Čech complex of the shifted presheaf `P[y]` is the shift of the total
Čech complex of `P`, naturally in `P` (`cechTotalComplexShiftIso_hom_naturality`). The shift is
moved out of the Čech complex (`cechComplexFunctorMapIso`); on the resulting bicomplex this is
`HomologicalComplex₂.totalExtendShift₂Iso` (`cechTotalComplexShiftIso_hom`), which multiplies
the summand in Čech degree `p` by `(-1)^(p y)` (`ι_cechTotalComplexShiftIso_hom_f`). -/
def cechTotalComplexShiftIso (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexFunctor U).obj (P ⋙ shiftFunctor (CochainComplex A ℤ) y) ≅
      ((cechTotalComplexFunctor U).obj P)⟦y⟧ :=
  total.mapIso ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      ((cechComplexFunctorMapIso U (shiftFunctor _ y)).app P).symm) _ ≪≫
    totalExtendShift₂Iso _ ((cechComplexFunctor U).obj P) y

/-- `cechTotalComplexShiftIso` is the total map of the inverse of `cechComplexFunctorMapIso`,
extended to `ℤ`, followed by `HomologicalComplex₂.totalExtendShift₂Iso`. -/
lemma cechTotalComplexShiftIso_hom (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexShiftIso U y P).hom =
      total.map (HomologicalComplex.extendMap
          ((cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app P)
            ComplexShape.embeddingUpNat) _ ≫
        (totalExtendShift₂Iso _ ((cechComplexFunctor U).obj P) y).hom :=
  (rfl)

/-- On the summand in degrees `(p, q)`, `cechTotalComplexShiftIso` is the identification of the
terms of the Čech complexes of `P[y]` and `P`, multiplied by the sign `(-1)^(p y)`, followed by
the inclusion of the summand in degrees `(p, q')` of the total Čech complex of `P`, where
`q' = q + y`. -/
@[reassoc]
lemma ι_cechTotalComplexShiftIso_hom_f (P : Cᵒᵖ ⥤ CochainComplex A ℤ) (p q n : ℤ)
    (hpq : p + q = n) (q' : ℤ) (hq' : q' = q + y) (n' : ℤ) (hn' : n' = n + y) :
    ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫ (cechTotalComplexShiftIso U y P).hom.f n =
      (p * y).negOnePow •
        (((HomologicalComplex.extendMap
            ((cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app P)
              ComplexShape.embeddingUpNat).f p).f q ≫
          (((shiftFunctor _ y).mapHomologicalComplexExtendObjIso _
            ((cechComplexFunctor U).obj P)).inv.f p).f q ≫
          (shiftFunctor₂XXIso _ p q y q' hq').hom ≫
          ιTotal _ (ComplexShape.up ℤ) p q' n' (by dsimp; lia) ≫
          (CochainComplex.shiftFunctorObjXIso _ y n n' hn').inv) := by
  rw [cechTotalComplexShiftIso_hom, HomologicalComplex.comp_f, ιTotal_map_assoc]
  -- the source summand is the one of `(cechComplexFunctor U ⋙ _).obj P`, which is only
  -- definitionally the one of the shifted Čech bicomplex, so the summand lemma is applied as a term
  exact (_ ≫= ι_totalExtendShift₂Iso_hom_f _ _ y p q n hpq q' hq' n' hn').trans
    (Linear.comp_units_smul _ _ _)

variable {U} in
/-- The common step of the compatibilities of `cechTotalComplexShiftIso` with maps of Čech
complexes: a map `f` of Čech complexes of shifted presheaves that corresponds to the shift of a
map `g` under `cechComplexFunctorMapIso` induces, on total complexes, the shift of the map induced
by `g`. -/
private lemma total_map_extendMap_comp_cechTotalComplexShiftIso_hom
    {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ}
    (f : (cechComplexFunctor V).obj (P ⋙ shiftFunctor (CochainComplex A ℤ) y) ⟶
      (cechComplexFunctor U).obj (Q ⋙ shiftFunctor (CochainComplex A ℤ) y))
    (g : (cechComplexFunctor V).obj P ⟶ (cechComplexFunctor U).obj Q)
    (h : f ≫ (cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app Q =
      (cechComplexFunctorMapIso V (shiftFunctor _ y)).inv.app P ≫
        ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map g) :
    total.map (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) (ComplexShape.up ℤ) ≫
        (cechTotalComplexShiftIso U y Q).hom =
      (cechTotalComplexShiftIso V y P).hom ≫
        (total.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
          (ComplexShape.up ℤ))⟦y⟧' := by
  rw [cechTotalComplexShiftIso_hom, cechTotalComplexShiftIso_hom, ← total.map_comp_assoc,
    ← HomologicalComplex.extendMap_comp, h, HomologicalComplex.extendMap_comp,
    total.map_comp_assoc, totalExtendShift₂Iso_hom_naturality, Category.assoc]

/-- `cechTotalComplexShiftIso` is natural in the presheaf of complexes. -/
@[reassoc]
lemma cechTotalComplexShiftIso_hom_naturality {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechTotalComplexFunctor U).map (Functor.whiskerRight α (shiftFunctor _ y)) ≫
        (cechTotalComplexShiftIso U y Q).hom =
      (cechTotalComplexShiftIso U y P).hom ≫ ((cechTotalComplexFunctor U).map α)⟦y⟧' := by
  have h : (cechComplexFunctor U).map (Functor.whiskerRight α (shiftFunctor _ y)) ≫
        (cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app Q =
      (cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app P ≫
        ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map
          ((cechComplexFunctor U).map α) :=
    (cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.naturality α
  rw [cechTotalComplexFunctor_map, cechTotalComplexFunctor_map]
  exact total_map_extendMap_comp_cechTotalComplexShiftIso_hom y _ _ h

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
  have h : cechComplexMap (P ⋙ shiftFunctor (CochainComplex A ℤ) y) φ ≫
        (cechComplexFunctorMapIso U (shiftFunctor _ y)).inv.app P =
      (cechComplexFunctorMapIso V (shiftFunctor _ y)).inv.app P ≫
        ((shiftFunctor (CochainComplex A ℤ) y).mapHomologicalComplex _).map
          (cechComplexMap P φ) := by
    rw [← Iso.app_inv, ← Iso.app_inv, Iso.comp_inv_eq, Category.assoc, Iso.app_hom,
      cechComplexFunctorMapIso_hom_app_comp_cechComplexMap, ← Iso.app_hom, Iso.inv_hom_id_assoc]
  rw [cechTotalComplexMap_def, cechTotalComplexMap_def]
  exact total_map_extendMap_comp_cechTotalComplexShiftIso_hom y _ _ h

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
      (cechHypercohomology A E hE n').obj P :=
  HasColimit.isoOfNatIso (NatIso.ofComponents
    (fun j ↦ (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso
        (cechTotalComplexShiftIso (E j).obj y P) ≪≫
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso y n n' h).app
        ((cechTotalComplexFunctor (E j).obj).obj P))
    fun {i j} f ↦ by
      rw [Functor.flip_obj_map, Functor.flip_obj_map,
        cechHypercohomologyDiagram_map A E hE n f (hE (leOfHom f)).some,
        cechHypercohomologyDiagram_map A E hE n' f (hE (leOfHom f)).some]
      simp only [cechTotalComplexHomologyMap_app, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        HomologicalComplex.homologyFunctor_map, ← HomologicalComplex.homologyMap_comp_assoc,
        cechTotalComplexMap_comp_cechTotalComplexShiftIso_hom]
      rw [HomologicalComplex.homologyMap_comp_assoc,
        CochainComplex.homologyMap_shift_comp_homologyFunctor_shiftIso_hom_app, Category.assoc])

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
        (cechHypercohomologyι E hE n' j).app P := by
  rw [cechHypercohomologyι_app, cechHypercohomologyι_app]
  exact (HasColimit.ι_isoOfNatIso_hom _ j).trans (Category.assoc _ _ _)

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
        (cechHypercohomologyι E hE n j).app (P ⋙ shiftFunctor (CochainComplex A ℤ) y) := by
  rw [cechHypercohomologyι_app, cechHypercohomologyι_app]
  exact (HasColimit.ι_isoOfNatIso_inv _ j).trans (Category.assoc _ _ _)

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
    cechTotalComplexShiftIso_hom_naturality, HomologicalComplex.homologyMap_comp_assoc,
    CochainComplex.homologyMap_shift_comp_homologyFunctor_shiftIso_hom_app_assoc]

end Hypercohomology

end TauCeti.CategoryTheory
