/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Basic

/-!
# Cover-colimit Čech hypercohomology

For a preorder of indexed families, ordered towards refinements, total Čech cohomology
forms a diagram even though no coherent choice of raw refinement functions is given.
The total refinement prism makes the transition maps independent of these choices.
The colimit of this diagram is Čech hypercohomology for the system of families.

The construction is functorial in presheaves of integer-graded complexes. It uses the native
direct-sum total with differential `δ + (-1)^p d`. It does not require a lower bound;
no convergence or derived comparison for unbounded complexes is asserted.

The descent map and its uniqueness allow comparison maps to be constructed from compatible
fixed-family cohomology maps. The specialization to small systems of open covers is in
`TauCeti.Topology.Sheaves.Cech.Hypercohomology`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25, especially equation (20.25.0.2),
  for refinement independence, and §20.15 for the cover-colimit construction.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w t v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  (A : Type u') [Category.{v'} A] [Preadditive A] [HasZeroObject A]
  [HasProducts.{w} A] [HasCoproducts.{0} A] [CategoryWithHomology A]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (n : ℤ)

/-- Total Čech cohomology of the families in `E`, as a diagram of functors of the
coefficient complex. Transition maps are induced by any raw refinement.
The body is exposed and implicitly reducible so that its objects compute to fixed-family total
cohomology functors, including when matching simplification lemmas. -/
@[expose, implicit_reducible, simps obj]
def cechHypercohomologyDiagram : J ⥤ (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ A where
  obj j := cechTotalComplexFunctor (E j).obj ⋙ HomologicalComplex.homologyFunctor A _ n
  map f := cechTotalComplexHomologyMap A n (hE (leOfHom f)).some
  map_id _ := (cechTotalComplexHomologyMap_eq A n _ _).trans
    (cechTotalComplexHomologyMap_id A n)
  map_comp _ _ := (cechTotalComplexHomologyMap_eq A n _ _).trans
    (cechTotalComplexHomologyMap_comp A n _ _)

instance (j : J) : ((cechHypercohomologyDiagram A E hE n).obj j).Additive := by
  rw [cechHypercohomologyDiagram_obj]
  infer_instance

instance : (cechHypercohomologyDiagram A E hE n).flip.Additive where
  map_add := by
    intros
    ext j
    exact Functor.map_add ((cechHypercohomologyDiagram A E hE n).obj j)

/-- Any refinement between comparable families computes the transition map. -/
lemma cechHypercohomologyDiagram_map {i j : J} (f : i ⟶ j) (φ : E j ⟶ E i) :
    (cechHypercohomologyDiagram A E hE n).map f = cechTotalComplexHomologyMap A n φ :=
  cechTotalComplexHomologyMap_eq A n _ φ

variable [HasColimitsOfShape J A]

/-- Čech hypercohomology for a system of families is the colimit of fixed-family total
cohomology, functorially in the presheaf of complexes. The body is exposed so that its objects
compute to colimits, as required by the structure and descent maps. -/
@[expose]
def cechHypercohomology : (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ A :=
  (cechHypercohomologyDiagram A E hE n).flip ⋙ colim

instance : (cechHypercohomology A E hE n).Additive := by
  unfold cechHypercohomology
  infer_instance

/-- The hypercohomology object is the colimit of the fixed-family total cohomology diagram. -/
lemma cechHypercohomology_obj (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechHypercohomology A E hE n).obj P =
      colimit ((cechHypercohomologyDiagram A E hE n).flip.obj P) :=
  (rfl)

/-- A coefficient morphism induces the map of the pointwise colimits. -/
lemma cechHypercohomology_map {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechHypercohomology A E hE n).map α =
      colim.map ((cechHypercohomologyDiagram A E hE n).flip.map α) :=
  (rfl)

variable {A}

/-- The structure map from a family's total cohomology, natural in the coefficient complex. -/
def cechHypercohomologyι (j : J) :
    cechTotalComplexFunctor (E j).obj ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechHypercohomology A E hE n :=
  (pointwiseCocone (cechHypercohomologyDiagram A E hE n)).ι.app j

variable (A)

/-- The pointwise colimit cocone for total Čech cohomology, natural in the coefficient
complex. Its point and legs are the public hypercohomology functor and structure maps. The
body is implicitly reducible so their types match in downstream simplification lemmas. -/
@[expose, implicit_reducible, simps]
def cechHypercohomologyCocone : Cocone (cechHypercohomologyDiagram A E hE n) where
  pt := cechHypercohomology A E hE n
  ι :=
    { app := cechHypercohomologyι E hE n
      naturality i j f := by
        unfold cechHypercohomologyι
        exact (pointwiseCocone (cechHypercohomologyDiagram A E hE n)).ι.naturality f }

/-- Hypercohomology is the colimit in the functor category, computed pointwise. -/
def isColimitCechHypercohomologyCocone :
    IsColimit (cechHypercohomologyCocone A E hE n) :=
  pointwiseIsColimit (cechHypercohomologyDiagram A E hE n)

variable {A}

/-- The structure maps are the insertions into the colimit. -/
lemma cechHypercohomologyι_app (j : J) (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechHypercohomologyι E hE n j).app P =
      colimit.ι ((cechHypercohomologyDiagram A E hE n).flip.obj P) j :=
  (rfl)

/-- Structure maps respect the transition maps of the diagram. -/
@[reassoc (attr := simp)]
lemma cechHypercohomologyDiagram_map_comp_cechHypercohomologyι {i j : J} (f : i ⟶ j) :
    (cechHypercohomologyDiagram A E hE n).map f ≫ cechHypercohomologyι E hE n j =
      cechHypercohomologyι E hE n i :=
  (pointwiseCocone (cechHypercohomologyDiagram A E hE n)).w f

/-- Structure maps respect every raw refinement between comparable families. -/
@[reassoc]
lemma cechTotalComplexHomologyMap_comp_cechHypercohomologyι
    {i j : J} (h : i ≤ j) (φ : E j ⟶ E i) :
    cechTotalComplexHomologyMap A n φ ≫ cechHypercohomologyι E hE n j =
      cechHypercohomologyι E hE n i := by
  rw [← cechHypercohomologyDiagram_map A E hE n (homOfLE h) φ]
  exact cechHypercohomologyDiagram_map_comp_cechHypercohomologyι E hE n (homOfLE h)

/-- Pointwise structure maps respect every raw refinement between comparable families. -/
@[reassoc]
lemma homologyMap_cechTotalComplexMap_comp_cechHypercohomologyι_app
    {i j : J} (h : i ≤ j) (φ : E j ⟶ E i) (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n ≫
        (cechHypercohomologyι E hE n j).app P = (cechHypercohomologyι E hE n i).app P := by
  have hφ := NatTrans.congr_app
    (cechTotalComplexHomologyMap_comp_cechHypercohomologyι E hE n h φ) P
  rw [NatTrans.comp_app, cechTotalComplexHomologyMap_app] at hφ
  exact hφ

/-- Pointwise structure maps commute with coefficient morphisms. -/
@[reassoc]
lemma cechHypercohomologyι_naturality (j : J)
    {P Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    (cechHypercohomologyι E hE n j).app P ≫ (cechHypercohomology A E hE n).map α =
      HomologicalComplex.homologyMap ((cechTotalComplexFunctor (E j).obj).map α) n ≫
        (cechHypercohomologyι E hE n j).app Q :=
  ((cechHypercohomologyι E hE n j).naturality α).symm

variable {E hE n} in
/-- Natural transformations out of hypercohomology are determined by the structure maps. -/
lemma cechHypercohomology_hom_ext {G : (Cᵒᵖ ⥤ CochainComplex A ℤ) ⥤ A}
    {f g : cechHypercohomology A E hE n ⟶ G}
    (h : ∀ j, cechHypercohomologyι E hE n j ≫ f = cechHypercohomologyι E hE n j ≫ g) :
    f = g :=
  (isColimitCechHypercohomologyCocone A E hE n).hom_ext h

variable {E hE n} in
/-- Maps out of hypercohomology are determined by their composites with all structure maps. -/
@[ext]
lemma cechHypercohomology_obj_hom_ext {P : Cᵒᵖ ⥤ CochainComplex A ℤ} {Y : A}
    {f g : (cechHypercohomology A E hE n).obj P ⟶ Y}
    (h : ∀ j, (cechHypercohomologyι E hE n j).app P ≫ f =
      (cechHypercohomologyι E hE n j).app P ≫ g) : f = g :=
  colimit.hom_ext h

/-- A compatible family of maps out of fixed-family total cohomology descends uniquely to
hypercohomology. Compatibility is stated for arbitrary raw refinements, not chosen ones. -/
def cechHypercohomologyDesc {P : Cᵒᵖ ⥤ CochainComplex A ℤ} {Y : A}
    (f : ∀ j, ((cechTotalComplexFunctor (E j).obj).obj P).homology n ⟶ Y)
    (hf : ∀ ⦃i j : J⦄, i ≤ j → ∀ φ : E j ⟶ E i,
      HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n ≫ f j = f i) :
    (cechHypercohomology A E hE n).obj P ⟶ Y :=
  colimit.desc ((cechHypercohomologyDiagram A E hE n).flip.obj P)
    { pt := Y
      ι :=
        { app := f
          naturality _ j h := by
            rw [Functor.flip_obj_map, cechHypercohomologyDiagram_map A E hE n h
              (hE (leOfHom h)).some, cechTotalComplexHomologyMap_app]
            exact (hf (leOfHom h) _).trans (Category.comp_id _).symm } }

/-- The descended map has the prescribed composite with each structure map. -/
@[reassoc (attr := simp)]
lemma cechHypercohomologyι_app_cechHypercohomologyDesc
    {P : Cᵒᵖ ⥤ CochainComplex A ℤ} {Y : A}
    (f : ∀ j, ((cechTotalComplexFunctor (E j).obj).obj P).homology n ⟶ Y)
    (hf : ∀ ⦃i j : J⦄, i ≤ j → ∀ φ : E j ⟶ E i,
      HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n ≫ f j = f i) (j : J) :
    (cechHypercohomologyι E hE n j).app P ≫ cechHypercohomologyDesc E hE n f hf = f j :=
  colimit.ι_desc _ j

/-- A system consisting of empty families has zero hypercohomology in every integer degree. -/
lemma isZero_cechHypercohomology_obj (hE₀ : ∀ j, IsEmpty (E j).I)
    (P : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    IsZero ((cechHypercohomology A E hE n).obj P) := by
  refine (IsZero.iff_id_eq_zero _).2 (cechHypercohomology_obj_hom_ext fun j ↦ ?_)
  let := hE₀ j
  exact ((HomologicalComplex.homologyFunctor A _ n).map_isZero
    (isZero_cechTotalComplexFunctor_obj (E j).obj P)).eq_of_src _ _

end TauCeti.CategoryTheory
