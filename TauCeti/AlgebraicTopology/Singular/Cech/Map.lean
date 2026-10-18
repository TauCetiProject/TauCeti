/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cech
import all TauCeti.AlgebraicTopology.Singular.Cech
import TauCeti.Topology.Category.TopCat.Basic

/-!
# Naturality of the ordered Čech--singular comparison

A map of spaces carrying each member of an indexed family into the corresponding member of
another family induces a map of ordered Čech double complexes. It preserves the summand indexed
by each finite set and acts there by the singular-chain map of the restriction to that
intersection. The induced map of total complexes commutes with augmentation to singular chains.
Thus the augmentation quasi-isomorphisms for open covers compare the maps as well as the objects.
The identity map of a space includes refinements with the same ordered index type.

Unlike the unnormalized Čech nerve, the ordered complex has no columns beyond the cardinality
of a finite index type. The maps here use its existing ordered Čech functor and Mathlib's total
complex functor, so they preserve the column filtration. No covering hypothesis or
abelian assumption is needed for the chain maps or their augmentation square.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, §15, for the Čech--singular comparison and its naturality.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology
open scoped Finset

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

variable {X Y Z : TopCat.{w}} {ι : Type w}
  (U : ι → Opens X) (V : ι → Opens Y) (f : X ⟶ Y)
  (hf : ∀ i, Set.MapsTo f (U i) (V i))

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- A map carrying `U i` into `V i` induces a natural transformation on the singular chains of
all finite intersections, including the empty intersection. -/
def cechSingularChainsMap : cechSingularChains U R ⟶ cechSingularChains V R where
  app s := by
    have hmem (T : TopCat.{w}) (A : ι → Opens T) (y : T) :
        y ∈ s.unop.inf A ↔ ∀ i ∈ s.unop, y ∈ A i := by
      rw [← SetLike.mem_coe, Opens.coe_finset_inf]
      simp
    have hmaps : Set.MapsTo f (↑(s.unop.inf U) : Set X) (↑(s.unop.inf V) : Set Y) := fun x hx ↦
      (hmem Y V (f x)).2 fun i hi ↦ hf i ((hmem X U x).1 hx i hi)
    exact ((singularChainComplexFunctor C).obj R).map (TopCat.ofHom
      ⟨hmaps.restrict f _ _, f.hom.continuous.continuousOn.mapsToRestrict hmaps⟩)
  naturality s t a := by
    dsimp only [cechSingularChains_map]
    exact (Functor.map_comp_eq_of_topCat_apply_eq ((singularChainComplexFunctor C).obj R)
      _ _ _ (fun _ ↦ rfl)).trans (((singularChainComplexFunctor C).obj R).map_comp _ _)

/-- The map on an intersection is induced by any restriction of `f` to that intersection.
The equation with the ambient inclusions specifies the restriction without choosing a
presentation of its subtype-valued continuous map. -/
lemma cechSingularChainsMap_app_eq (s : Finset ι)
    (g : (Opens.toTopCat X).obj (s.inf U) ⟶ (Opens.toTopCat Y).obj (s.inf V))
    (hg : g ≫ Opens.inclusion' (s.inf V) = Opens.inclusion' (s.inf U) ≫ f) :
    (cechSingularChainsMap U V f hf R).app (op s) =
      ((singularChainComplexFunctor C).obj R).map g := by
  apply congrArg ((singularChainComplexFunctor C).obj R).map
  ext x
  exact (ConcreteCategory.congr_hom hg x).symm

/-- The finite-intersection chain maps commute with the inclusions into the ambient spaces. -/
@[reassoc (attr := simp↓)]
lemma cechSingularChainsMap_app_comp_inclusion (s : Finset ι) :
    (cechSingularChainsMap U V f hf R).app (op s) ≫
        ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.inf V)) =
      ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.inf U)) ≫
        ((singularChainComplexFunctor C).obj R).map f := by
  dsimp only [cechSingularChainsMap]
  exact (Functor.map_comp_eq_of_topCat_apply_eq ((singularChainComplexFunctor C).obj R)
    _ _ _ (fun _ ↦ rfl)).trans (((singularChainComplexFunctor C).obj R).map_comp _ _)

/-- Identity maps act identically on singular chains of finite intersections. -/
@[simp]
lemma cechSingularChainsMap_id :
    cechSingularChainsMap U U (𝟙 X) (fun _ _ hx ↦ hx) R = 𝟙 _ := by
  apply NatTrans.ext
  funext s
  rw [cechSingularChainsMap_app_eq U U (𝟙 X) (fun _ _ hx ↦ hx) R s.unop
    (𝟙 _) (by simp)]
  exact CategoryTheory.Functor.map_id _ _

variable (W : ι → Opens Z) (g : Y ⟶ Z) (hg : ∀ i, Set.MapsTo g (V i) (W i))

/-- Maps on finite-intersection singular chains respect composition. -/
lemma cechSingularChainsMap_comp :
    cechSingularChainsMap U W (f ≫ g) (fun i _ hx ↦ hg i (hf i hx)) R =
      cechSingularChainsMap U V f hf R ≫ cechSingularChainsMap V W g hg R := by
  apply NatTrans.ext
  funext s
  dsimp only [cechSingularChainsMap, NatTrans.comp_app]
  exact (Functor.map_comp_eq_of_topCat_apply_eq ((singularChainComplexFunctor C).obj R)
    _ _ _ (fun _ ↦ rfl)).symm

variable [LinearOrder ι]

/-- A map of indexed families induces a map of their ordered Čech--singular double complexes. -/
def cechDoubleComplexMap : cechDoubleComplex U R ⟶ cechDoubleComplex V R :=
  NatTrans.orderedCechComplexMap (cechSingularChainsMap U V f hf R)

/-- On each finite-intersection summand, the double-complex map is the corresponding singular
chain map. -/
@[reassoc (attr := simp)]
lemma ι_cechDoubleComplexMap_f {p : ℕ} (s : {s : Finset ι // #s = p + 1}) :
    cechDoubleComplexι U R s ≫ (cechDoubleComplexMap U V f hf R).f p =
      (cechSingularChainsMap U V f hf R).app (op s.1) ≫ cechDoubleComplexι V R s :=
  NatTrans.ι_orderedCechComplexMap_f _ s

/-- Identity maps induce identity ordered Čech double-complex maps. -/
@[simp]
lemma cechDoubleComplexMap_id :
    cechDoubleComplexMap U U (𝟙 X) (fun _ _ hx ↦ hx) R = 𝟙 _ := by
  simp only [cechDoubleComplexMap, cechSingularChainsMap_id, NatTrans.orderedCechComplexMap_id]
  rfl

/-- Ordered Čech double-complex maps respect composition. -/
lemma cechDoubleComplexMap_comp :
    cechDoubleComplexMap U W (f ≫ g) (fun i _ hx ↦ hg i (hf i hx)) R =
      cechDoubleComplexMap U V f hf R ≫ cechDoubleComplexMap V W g hg R := by
  simp only [cechDoubleComplexMap, cechSingularChainsMap_comp,
    NatTrans.orderedCechComplexMap_comp]
  rfl

/-- The column-zero augmentation commutes with the map induced by a map of indexed families. -/
@[reassoc (attr := simp)]
lemma cechDoubleComplexMap_f_zero_comp_cechAugmentation :
    (cechDoubleComplexMap U V f hf R).f 0 ≫ cechAugmentation V R =
      cechAugmentation U R ≫ ((singularChainComplexFunctor C).obj R).map f := by
  apply cechDoubleComplex_hom_ext U R
  intro s
  simp only [ι_cechDoubleComplexMap_f_assoc, ι_cechAugmentation,
    ι_cechAugmentation_assoc, cechSingularChainsMap_app_comp_inclusion]

/-- The map of total ordered Čech--singular complexes induced by a map of indexed families. -/
def cechTotalMap :
    (cechDoubleComplex U R).total (ComplexShape.down ℕ) ⟶
      (cechDoubleComplex V R).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map (cechDoubleComplexMap U V f hf R) (ComplexShape.down ℕ)

/-- The map of total complexes acts on each bidegree by the map of double complexes. -/
@[reassoc (attr := simp)]
lemma ιTotal_cechTotalMap_f (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    (cechDoubleComplex U R).ιTotal (ComplexShape.down ℕ) p q n h ≫
        (cechTotalMap U V f hf R).f n =
      ((cechDoubleComplexMap U V f hf R).f p).f q ≫
        (cechDoubleComplex V R).ιTotal (ComplexShape.down ℕ) p q n h :=
  HomologicalComplex₂.ιTotal_map (K := cechDoubleComplex U R)
    (L := cechDoubleComplex V R) (φ := cechDoubleComplexMap U V f hf R)
    (ComplexShape.down ℕ) p q n h

/-- Identity maps induce identity maps of total complexes. -/
@[simp]
lemma cechTotalMap_id :
    cechTotalMap U U (𝟙 X) (fun _ _ hx ↦ hx) R = 𝟙 _ := by
  simp only [cechTotalMap, cechDoubleComplexMap_id, HomologicalComplex₂.total.map_id]

/-- Maps of total ordered Čech--singular complexes respect composition. -/
lemma cechTotalMap_comp :
    cechTotalMap U W (f ≫ g) (fun i _ hx ↦ hg i (hf i hx)) R =
      cechTotalMap U V f hf R ≫ cechTotalMap V W g hg R := by
  simp only [cechTotalMap, cechDoubleComplexMap_comp, HomologicalComplex₂.total.map_comp]

/-- **Naturality of the ordered Čech--singular comparison.** The augmentation from the total
complex commutes with the chain map induced by the original continuous map of spaces. For open
covers these augmentations are the quasi-isomorphisms computing singular homology. -/
@[reassoc (attr := simp)]
lemma cechTotalMap_comp_cechTotalAugmentation :
    cechTotalMap U V f hf R ≫ cechTotalAugmentation V R =
      cechTotalAugmentation U R ≫ ((singularChainComplexFunctor C).obj R).map f := by
  simp only [cechTotalMap, cechTotalAugmentation_def,
    HomologicalComplex₂.total_map_totalAugmentation, HomologicalComplex₂.totalAugmentation_comp,
    cechDoubleComplexMap_f_zero_comp_cechAugmentation]

end Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)
  [LinearOrder ι]

/-- The ordered Čech comparison intertwines the induced map on total-complex homology with
the singular homology map of the original map of spaces. For covers the comparison maps in
this square are isomorphisms. -/
@[reassoc]
lemma homologyMap_cechTotalMap_comp_cechTotalAugmentation (n : ℕ) :
    HomologicalComplex.homologyMap (cechTotalMap U V f hf R) n ≫
        HomologicalComplex.homologyMap (cechTotalAugmentation V R) n =
      HomologicalComplex.homologyMap (cechTotalAugmentation U R) n ≫
        ((singularHomologyFunctor C n).obj R).map f := by
  rw [← HomologicalComplex.homologyMap_comp, cechTotalMap_comp_cechTotalAugmentation,
    HomologicalComplex.homologyMap_comp]
  rfl

end TauCeti
