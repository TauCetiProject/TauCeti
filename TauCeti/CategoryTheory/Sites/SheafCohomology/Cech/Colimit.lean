/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.Connected
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech cohomology as a colimit over a system of families

Let `C` be a category with finite products and let `E : J → FormalCoproduct C` be a system of
families of objects of `C`, indexed by a preorder `J`, such that `E j` admits a morphism of
families to `E i` whenever `i ≤ j`. For open covers, `J` is a set of covers ordered towards finer
covers, and a morphism `E j ⟶ E i` is a refinement map. The relation `i ≤ j` remembers only that
such a morphism exists, not the morphism itself.

For a presheaf `P : Cᵒᵖ ⥤ A` with values in a preadditive category with products and homology,
the degree `n` Čech cohomologies `Hⁿ(Č(E j, P))` of the members of the system form a diagram
`J ⥤ A`: its transition maps are induced by an arbitrary choice of morphisms of families, and do
not depend on that choice because any two morphisms of families induce homotopic maps of Čech
complexes (`TauCeti.CategoryTheory.cechComplexMapHomotopy`). The Čech cohomology of `P` for the
system is the colimit of this diagram, and it is functorial in `P`.

If `C` has a terminal object `T` and `P` satisfies the sheaf condition for each family `E j`, so
that the augmentation identifies `P(T)` with the degree `0` Čech cohomology of every `E j`, then
the degree `0` Čech cohomology of `P` for a connected system is `P(T)`
(`TauCeti.CategoryTheory.cechCohomologyZeroIso`).

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyDiagram A E hE n`: the diagram `j ↦ Hⁿ(Č(E j, -))` of
  functors of the presheaf, with transition maps induced by morphisms of families.
* `TauCeti.CategoryTheory.cechCohomology A E hE n`: its colimit, the degree `n` Čech cohomology
  for the system `E`, as a functor of the presheaf.
* `TauCeti.CategoryTheory.cechCohomologyι E hE n j`: the structure map from the Čech cohomology
  of the family `E j`.
* `TauCeti.CategoryTheory.isColimitCechCohomologyCocone A E hE n`: the Čech cohomology for the
  system, with the structure maps, is a colimit of the diagram of functors of the presheaf.
* `TauCeti.CategoryTheory.cechCohomologyDesc E hE n f hf`: the map out of the Čech cohomology of
  a presheaf induced by a compatible family of maps out of the Čech cohomologies of the families
  of the system.
* `TauCeti.CategoryTheory.cechCohomologyZeroIso`: the identification of degree `0` Čech
  cohomology with `P(T)` when `P` satisfies the sheaf condition for every family of the system.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyDiagram_map`: the transition map is the map induced by
  any morphism of families.
* `TauCeti.CategoryTheory.cechComplexHomologyMap_comp_cechCohomologyι`: the structure maps are
  compatible with the maps induced by morphisms of families.
* `TauCeti.CategoryTheory.isZero_cechCohomology_obj`: the Čech cohomology vanishes if every family
  of the system is empty.
* `TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_naturality`: the identification in degree `0`
  is natural in the presheaf.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), for the colimit over refinements
  and the independence of the transition maps from the refinement maps.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A, Definition A.4.3.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w t v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] [CategoryWithHomology A]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (n : ℕ)

/-! ### The diagram of Čech cohomologies -/

variable (A) in
/-- The degree `n` Čech cohomology of presheaves for the families of the system `E`, as a diagram
indexed by `J`. Its value at `j` is the functor `P ↦ Hⁿ(Č(E j, P))`, and its transition map for
`i ≤ j` is induced by a morphism of families `E j ⟶ E i`; any such morphism gives the same map
(`cechCohomologyDiagram_map`). The body is exposed so that the values of the diagram unfold to
Čech cohomology objects, which the statements about its maps need. -/
@[expose, simps obj]
def cechCohomologyDiagram : J ⥤ (Cᵒᵖ ⥤ A) ⥤ A where
  obj j := cechComplexFunctor (E j).obj ⋙ HomologicalComplex.homologyFunctor A _ n
  map f := cechComplexHomologyMap A n (hE (leOfHom f)).some
  map_id _ := (cechComplexHomologyMap_eq A n _ _).trans (cechComplexHomologyMap_id A n)
  map_comp _ _ := (cechComplexHomologyMap_eq A n _ _).trans (cechComplexHomologyMap_comp A n _ _)

variable (A) in
/-- **The transition maps do not depend on the refinement maps.** For `i ≤ j`, the transition map
of the diagram is the map on Čech cohomology induced by any morphism of families `E j ⟶ E i`. -/
theorem cechCohomologyDiagram_map {i j : J} (f : i ⟶ j) (φ : E j ⟶ E i) :
    (cechCohomologyDiagram A E hE n).map f = cechComplexHomologyMap A n φ :=
  cechComplexHomologyMap_eq A n _ φ

/-- Fixed-family Čech cohomology is additive in the coefficient presheaf. -/
instance cechCohomologyDiagram_obj_additive (j : J) :
    ((cechCohomologyDiagram A E hE n).obj j).Additive :=
  inferInstanceAs (cechComplexFunctor (E j).obj ⋙
    HomologicalComplex.homologyFunctor A _ n).Additive

/-- The diagram of Čech cohomologies is additive in the coefficient presheaf. -/
instance cechCohomologyDiagram_flip_additive :
    (cechCohomologyDiagram A E hE n).flip.Additive where
  map_add {P Q} {f g} := by
    ext j
    exact Functor.map_add ((cechCohomologyDiagram A E hE n).obj j)

/-! ### The colimit -/

variable [HasColimitsOfShape J A]

variable (A) in
/-- The degree `n` Čech cohomology for the system of families `E`, as a functor of the presheaf:
the colimit over `J` of the degree `n` Čech cohomologies `Hⁿ(Č(E j, P))`. The body is exposed so
that its values unfold to colimits in `A`. -/
@[expose]
def cechCohomology : (Cᵒᵖ ⥤ A) ⥤ A :=
  (cechCohomologyDiagram A E hE n).flip ⋙ colim

/-- Čech cohomology is additive in the coefficient presheaf. -/
instance cechCohomology_additive : (cechCohomology A E hE n).Additive :=
  inferInstanceAs ((cechCohomologyDiagram A E hE n).flip ⋙ colim).Additive

/-- The Čech cohomology of `P` for the system `E` is the colimit of the Čech cohomologies of `P`
for the families of the system. -/
theorem cechCohomology_obj (P : Cᵒᵖ ⥤ A) :
    (cechCohomology A E hE n).obj P = colimit ((cechCohomologyDiagram A E hE n).flip.obj P) :=
  (rfl)

/-- The structure map from the degree `n` Čech cohomology for the family `E j` to the Čech
cohomology for the system, natural in the presheaf. -/
def cechCohomologyι (j : J) :
    (cechCohomologyDiagram A E hE n).obj j ⟶ cechCohomology A E hE n where
  app P := colimit.ι ((cechCohomologyDiagram A E hE n).flip.obj P) j
  naturality _ _ α := (colimit.ι_map ((cechCohomologyDiagram A E hE n).flip.map α) j).symm

/-- The component of the structure map at `P` is the colimit insertion. -/
theorem cechCohomologyι_app (j : J) (P : Cᵒᵖ ⥤ A) :
    (cechCohomologyι E hE n j).app P = colimit.ι ((cechCohomologyDiagram A E hE n).flip.obj P) j :=
  (rfl)

/-- The structure maps commute with the transition maps of the diagram. -/
@[reassoc (attr := simp)]
theorem cechCohomologyDiagram_map_comp_cechCohomologyι {i j : J} (f : i ⟶ j) :
    (cechCohomologyDiagram A E hE n).map f ≫ cechCohomologyι E hE n j =
      cechCohomologyι E hE n i := by
  ext P
  exact colimit.w ((cechCohomologyDiagram A E hE n).flip.obj P) f

variable (A) in
/-- The structure maps are compatible with the map on Čech cohomology induced by any morphism of
families `E j ⟶ E i`, for `i ≤ j`. -/
@[reassoc]
theorem cechComplexHomologyMap_comp_cechCohomologyι {i j : J} (h : i ≤ j) (φ : E j ⟶ E i) :
    cechComplexHomologyMap A n φ ≫ cechCohomologyι E hE n j = cechCohomologyι E hE n i :=
  (congrArg (· ≫ cechCohomologyι E hE n j)
    (cechCohomologyDiagram_map A E hE n (homOfLE h) φ)).symm.trans
      (cechCohomologyDiagram_map_comp_cechCohomologyι E hE n (homOfLE h))

variable (A) in
/-- The Čech cohomology for the system, as a cocone over the diagram of functors of the presheaf
whose legs are the structure maps. The body is exposed so that its cocone point unfolds to
`cechCohomology A E hE n`, which maps built from `isColimitCechCohomologyCocone` need. -/
@[expose, simps]
def cechCohomologyCocone : Cocone (cechCohomologyDiagram A E hE n) where
  pt := cechCohomology A E hE n
  ι :=
    { app := cechCohomologyι E hE n
      naturality _ _ f := (cechCohomologyDiagram_map_comp_cechCohomologyι E hE n f).trans
        (Category.comp_id _).symm }

variable (A) in
/-- The Čech cohomology for the system is the colimit of the diagram of functors of the presheaf,
since colimits of functors are computed pointwise. -/
def isColimitCechCohomologyCocone : IsColimit (cechCohomologyCocone A E hE n) :=
  pointwiseIsColimit (cechCohomologyDiagram A E hE n)

variable (A) in
/-- Two maps out of the Čech cohomology for the system agree as soon as they agree after every
structure map. -/
theorem cechCohomology_hom_ext {G : (Cᵒᵖ ⥤ A) ⥤ A} {f g : cechCohomology A E hE n ⟶ G}
    (h : ∀ j, cechCohomologyι E hE n j ≫ f = cechCohomologyι E hE n j ≫ g) : f = g :=
  (isColimitCechCohomologyCocone A E hE n).hom_ext h

variable {E hE n} in
/-- Two maps out of the Čech cohomology of `P` for the system agree as soon as they agree after
every structure map. -/
@[ext]
theorem cechCohomology_obj_hom_ext {P : Cᵒᵖ ⥤ A} {Y : A}
    {g g' : (cechCohomology A E hE n).obj P ⟶ Y}
    (h : ∀ j, (cechCohomologyι E hE n j).app P ≫ g = (cechCohomologyι E hE n j).app P ≫ g') :
    g = g' :=
  colimit.hom_ext h

/-- If every family of the system is empty, then all Čech complexes vanish, and so does the Čech
cohomology for the system. -/
theorem isZero_cechCohomology_obj (hE₀ : ∀ j, IsEmpty (E j).I) (P : Cᵒᵖ ⥤ A) :
    IsZero ((cechCohomology A E hE n).obj P) := by
  refine (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun j ↦ ?_)
  -- the degree `n` Čech cochains of an empty family form an empty product
  have : IsZero (((cechComplexFunctor (E j).obj).obj P).X n) :=
    (IsZero.iff_id_eq_zero _).2 <| Pi.hom_ext _ _ fun a ↦ (hE₀ j).elim (a 0)
  exact (ShortComplex.isZero_homology_of_isZero_X₂ _ this).eq_of_src _ _

/-! ### Maps out of the colimit -/

/-- The map out of the Čech cohomology of `P` for the system induced by a family of maps out of the
Čech cohomologies `Hⁿ(Č(E j, P))` that is compatible with the maps induced by morphisms of families
between comparable members of the system. -/
def cechCohomologyDesc {P : Cᵒᵖ ⥤ A} {Y : A}
    (f : ∀ j, ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ Y)
    (hf : ∀ ⦃i j : J⦄, i ≤ j → ∀ φ : E j ⟶ E i,
      HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ f j = f i) :
    (cechCohomology A E hE n).obj P ⟶ Y :=
  colimit.desc ((cechCohomologyDiagram A E hE n).flip.obj P)
    { pt := Y
      ι :=
        { app := f
          naturality _ j h :=
            -- the transition map at `P` is the map induced by any morphism of families
            ((NatTrans.congr_app (cechCohomologyDiagram_map A E hE n h (hE (leOfHom h)).some)
              P).trans (cechComplexHomologyMap_app ..) =≫ f j).trans
                ((hf (leOfHom h) _).trans (Category.comp_id _).symm) } }

/-- The map out of the Čech cohomology induced by a compatible family restricts to that family
along each structure map. -/
@[reassoc (attr := simp)]
theorem cechCohomologyι_app_cechCohomologyDesc {P : Cᵒᵖ ⥤ A} {Y : A}
    (f : ∀ j, ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ Y)
    (hf : ∀ ⦃i j : J⦄, i ≤ j → ∀ φ : E j ⟶ E i,
      HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ f j = f i) (j : J) :
    (cechCohomologyι E hE n j).app P ≫ cechCohomologyDesc E hE n f hf = f j :=
  colimit.ι_desc _ j

/-! ### Degree zero -/

section Zero

variable {T : C} (hT : IsTerminal T) [HasZeroObject A] [IsConnected J] (P : Cᵒᵖ ⥤ A)

/-- The augmentations `P(T) ⟶ H⁰(Č(E j, P))`, as a natural transformation from the constant
diagram. -/
private def cechCohomologyZeroAugmentation :
    (Functor.const J).obj (P.obj (op T)) ⟶ (cechCohomologyDiagram A E hE 0).flip.obj P where
  app j := (HomologicalComplex.singleObjHomologySelfIso _ 0 _).inv ≫
    HomologicalComplex.homologyMap (cechAugmentation (E j).obj hT P) 0
  naturality {i j} f := by
    rw [Functor.flip_obj_map, cechCohomologyDiagram_map A E hE 0 f (hE (leOfHom f)).some,
      cechComplexHomologyMap_app]
    -- the augmentations are compatible with the maps induced by morphisms of families
    exact (Category.id_comp _).trans <| (_ ≫= ((congrArg (HomologicalComplex.homologyMap · 0)
      (cechAugmentation_comp_cechComplexMap hT P _)).symm.trans
        (HomologicalComplex.homologyMap_comp _ _ 0))).trans (Category.assoc _ _ _).symm

/-- If `P` satisfies the sheaf condition for every family of the connected system `E`, so that the
augmentation identifies `P(T)` with each degree `0` Čech cohomology
(`quasiIsoAt_cechAugmentation_zero_iff`), then the degree `0` Čech cohomology of `P` for the
system is `P(T)`. -/
def cechCohomologyZeroIso (h : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0) :
    P.obj (op T) ≅ (cechCohomology A E hE 0).obj P :=
  have (j : J) : IsIso ((cechCohomologyZeroAugmentation E hE hT P).app j) :=
    IsIso.comp_isIso' inferInstance ((quasiIsoAt_iff_isIso_homologyMap _ 0).1 (h j))
  have : IsIso (cechCohomologyZeroAugmentation E hE hT P) := NatIso.isIso_of_isIso_app _
  (colimit.isoColimitCocone ⟨_, isColimitConstCocone J (P.obj (op T))⟩).symm ≪≫
    HasColimit.isoOfNatIso (asIso (cechCohomologyZeroAugmentation E hE hT P))

/-- The identification of degree `0` Čech cohomology with `P(T)` is the augmentation of the Čech
complex of any family of the system, followed by its structure map. -/
theorem cechCohomologyZeroIso_hom (h : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (j : J) : (cechCohomologyZeroIso E hE hT P h).hom =
      (HomologicalComplex.singleObjHomologySelfIso _ 0 _).inv ≫
        HomologicalComplex.homologyMap (cechAugmentation (E j).obj hT P) 0 ≫
          (cechCohomologyι E hE 0 j).app P :=
  -- the inverse of the identification of `P(T)` with the colimit of the constant diagram is the
  -- insertion at `j`, whose composite with the induced map of colimits is the component at `j`
  (Category.id_comp _).symm.trans <| (Category.assoc _ _ _).symm.trans <|
    (colimit.isoColimitCocone_ι_inv ⟨_, isColimitConstCocone J (P.obj (op T))⟩ j =≫ _).trans <|
      (HasColimit.ι_isoOfNatIso_hom _ j).trans (Category.assoc _ _ _)

/-- The identification of degree `0` Čech cohomology with `P(T)` is natural in `P`. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (hQ : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT Q) 0) :
    α.app (op T) ≫ (cechCohomologyZeroIso E hE hT Q hQ).hom =
      (cechCohomologyZeroIso E hE hT P hP).hom ≫ (cechCohomology A E hE 0).map α := by
  obtain ⟨j⟩ : Nonempty J := inferInstance
  rw [cechCohomologyZeroIso_hom E hE hT P hP j, cechCohomologyZeroIso_hom E hE hT Q hQ j]
  -- the augmentation and the structure map at `j` are both natural in the presheaf
  exact (HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc _ _ _ _).symm.trans <|
    (_ ≫= ((HomologicalComplex.homologyMap_comp_assoc _ _ 0 _).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · 0 ≫ _)
        (cechAugmentation_naturality _ hT P α).symm).trans <|
          (HomologicalComplex.homologyMap_comp_assoc _ _ 0 _).trans <|
            (_ ≫= (cechCohomologyι E hE 0 j).naturality α).trans
              (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm

end Zero

end TauCeti.CategoryTheory
