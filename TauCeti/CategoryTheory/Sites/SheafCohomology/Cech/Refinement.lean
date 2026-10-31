/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.HasLimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech cohomology along a refinement preorder

Let `C` be a category with finite products and let `F : I → FormalCoproduct C` be a family of
families of objects of `C`, indexed by a preorder `I`, such that `i ≤ j` implies that there is a
morphism of families `F j ⟶ F i`. For open covers of a space, `I` is a system of covers ordered
towards finer covers, and `i ≤ j` means that the cover `F j` refines the cover `F i`.

A morphism of families `F j ⟶ F i` is not determined by `i ≤ j`, and the maps of Čech complexes
`Č(F i, P) ⟶ Č(F j, P)` induced by different choices differ. They are homotopic
(`TauCeti.CategoryTheory.cechComplexMapHomotopy`), so the induced maps on cohomology do not
depend on the choice. This file assembles them into the diagram `I ⥤ A` of degree `n` Čech
cohomologies, functorially in the presheaf `P`, and takes its colimit. For the systems of open
covers of `TauCeti.Topology.PointOpenCover`, this colimit is the Čech cohomology of a presheaf
on a topological space.

No filteredness of the category of actual morphisms of families is asserted: transition maps
are only defined on cohomology. The colimit is formed over the preorder `I` itself; it is a
filtered colimit when `I` is directed.

## Main definitions

* `TauCeti.CategoryTheory.cechHomologyFunctor F hF n`: the functor sending a presheaf `P` to
  the diagram `i ↦ Hⁿ(Č(F i, P))` over `I`, with transition maps induced by any refinement.
* `TauCeti.CategoryTheory.cechCohomology F hF n`: the colimit over `I` of this diagram, as a
  functor of the presheaf.
* `TauCeti.CategoryTheory.toCechCohomology F hF n P i`: the map from the cohomology of the
  Čech complex of the family `F i` to the colimit.

## Main results

* `TauCeti.CategoryTheory.cechHomologyFunctor_obj_map`: the transition map along `i ≤ j` is the
  map on cohomology induced by any morphism of families `F j ⟶ F i`.
* `TauCeti.CategoryTheory.homologyMap_cechComplexMap_comp_toCechCohomology`: the maps to the
  colimit are compatible with every morphism of families between comparable members of the
  system.
* `TauCeti.CategoryTheory.isIso_toCechCohomology_of_isTop`: over a preorder with a greatest
  element, the colimit is the cohomology of the Čech complex of the family at that element.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), for the refinement maps and the
  definition of Čech cohomology as a colimit over covers.
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v v' v'' u u' u''

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] [CategoryWithHomology A]
  {I : Type u''} [Preorder I] (F : I → FormalCoproduct.{w} C)
  (hF : ∀ ⦃i j : I⦄, i ≤ j → Nonempty (F j ⟶ F i)) (n : ℕ)

/-- The diagram over `I` of the degree `n` cohomologies of the Čech complexes of the families
`F i`, as a functor of the presheaf. The transition map along `i ≤ j` is induced by a morphism
of families `F j ⟶ F i`; by `cechHomologyFunctor_obj_map` it does not depend on the choice.
The body is exposed because the statements about this functor compare its values with the
cohomology of the Čech complexes. -/
@[expose]
def cechHomologyFunctor : (Cᵒᵖ ⥤ A) ⥤ I ⥤ A where
  obj P :=
    { obj i := ((cechComplexFunctor (F i).obj).obj P).homology n
      map h := HomologicalComplex.homologyMap (cechComplexMap P (hF h.le).some) n
      map_id i := by
        rw [(cechComplexMapHomotopy P _ (𝟙 _)).homologyMap_eq n, cechComplexMap_id,
          HomologicalComplex.homologyMap_id]
      map_comp h h' := by
        rw [← HomologicalComplex.homologyMap_comp, ← cechComplexMap_comp]
        exact (cechComplexMapHomotopy P _ _).homologyMap_eq n }
  map α :=
    { app i := HomologicalComplex.homologyMap ((cechComplexFunctor (F i).obj).map α) n
      naturality i j h := by
        simp only [← HomologicalComplex.homologyMap_comp, cechComplexMap_naturality] }
  map_id P := by
    ext i
    simp
  map_comp α β := by
    ext i
    simp [HomologicalComplex.homologyMap_comp]

@[simp]
theorem cechHomologyFunctor_obj_obj (P : Cᵒᵖ ⥤ A) (i : I) :
    ((cechHomologyFunctor F hF n).obj P).obj i =
      ((cechComplexFunctor (F i).obj).obj P).homology n :=
  (rfl)

/-- The transition map of the diagram of Čech cohomologies along `i ≤ j` is the map on
cohomology induced by any morphism of families `F j ⟶ F i`. -/
theorem cechHomologyFunctor_obj_map (P : Cᵒᵖ ⥤ A) {i j : I} (h : i ⟶ j) (φ : F j ⟶ F i) :
    ((cechHomologyFunctor F hF n).obj P).map h =
      HomologicalComplex.homologyMap (cechComplexMap P φ) n :=
  (cechComplexMapHomotopy P _ _).homologyMap_eq n

@[simp]
theorem cechHomologyFunctor_map_app {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (i : I) :
    ((cechHomologyFunctor F hF n).map α).app i =
      HomologicalComplex.homologyMap ((cechComplexFunctor (F i).obj).map α) n :=
  (rfl)

variable [HasColimitsOfShape I A]

/-- The degree `n` Čech cohomology relative to the system of families `F`: the colimit over `I`
of the degree `n` cohomologies of the Čech complexes `Č(F i, P)`, as a functor of the
presheaf `P`. -/
def cechCohomology : (Cᵒᵖ ⥤ A) ⥤ A :=
  cechHomologyFunctor F hF n ⋙ colim

/-- The map from the degree `n` cohomology of the Čech complex of the family `F i` to the Čech
cohomology relative to the system `F`. -/
def toCechCohomology (P : Cᵒᵖ ⥤ A) (i : I) :
    ((cechComplexFunctor (F i).obj).obj P).homology n ⟶ (cechCohomology F hF n).obj P :=
  colimit.ι ((cechHomologyFunctor F hF n).obj P) i

/-- The maps to Čech cohomology are compatible with every morphism of families between comparable
members of the system: for `i ≤ j`, the map induced on cohomology by any `F j ⟶ F i`, followed
by the map from the `j`th term, is the map from the `i`th term. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_toCechCohomology (P : Cᵒᵖ ⥤ A) {i j : I} (hij : i ≤ j)
    (φ : F j ⟶ F i) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ toCechCohomology F hF n P j =
      toCechCohomology F hF n P i := by
  rw [← cechHomologyFunctor_obj_map F hF n P (homOfLE hij) φ]
  exact colimit.w _ _

/-- The maps to Čech cohomology are natural in the presheaf. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (i : I) :
    toCechCohomology F hF n P i ≫ (cechCohomology F hF n).map α =
      HomologicalComplex.homologyMap ((cechComplexFunctor (F i).obj).map α) n ≫
        toCechCohomology F hF n Q i :=
  colimit.ι_map _ i

/-- If `i` is a greatest element of `I`, then the Čech cohomology relative to `F` is the
cohomology of the Čech complex of the family `F i`. -/
theorem isIso_toCechCohomology_of_isTop (P : Cᵒᵖ ⥤ A) {i : I} (hi : IsTop i) :
    IsIso (toCechCohomology F hF n P i) :=
  (colimit.isColimit _).isIso_ι_app_of_isTerminal i
    (IsTerminal.ofUniqueHom (fun j ↦ homOfLE (hi j)) fun _ _ ↦ Subsingleton.elim _ _)

/-- Two morphisms out of Čech cohomology are equal if they agree after composing with the map
from the cohomology of each family of the system. -/
@[ext]
theorem cechCohomology_hom_ext {P : Cᵒᵖ ⥤ A} {Z : A} {f g : (cechCohomology F hF n).obj P ⟶ Z}
    (h : ∀ i, toCechCohomology F hF n P i ≫ f = toCechCohomology F hF n P i ≫ g) : f = g :=
  colimit.hom_ext h

end TauCeti.CategoryTheory
