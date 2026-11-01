/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.CategoryTheory.cechCohomologyDesc E hE n f hf`: the map out of the Čech cohomology
  induced by a compatible family of maps out of the Čech cohomologies of the families of the
  system.
* `TauCeti.CategoryTheory.cechCohomologyιOfRefinement E hE n G hG`: the structure map from the Čech
  cohomology of a family `G` refined by some member of the system.
* `TauCeti.CategoryTheory.cechCohomologyZeroIso`: the identification of degree `0` Čech
  cohomology with `P(T)` when `P` satisfies the sheaf condition for every family of the system.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyDiagram_map_app`: the transition map is the map induced by
  any morphism of families.
* `TauCeti.CategoryTheory.homologyMap_cechComplexMap_comp_cechCohomologyι_app`: the structure maps
  are compatible with the maps induced by morphisms of families.
* `TauCeti.CategoryTheory.isZero_cechCohomology_obj`: the Čech cohomology vanishes if every family
  of the system is empty.
* `TauCeti.CategoryTheory.cechCohomologyιOfRefinement_app_eq`: for a directed system, the structure
  map from a refined family agrees with the map through any member of the system refining it.
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
(`cechCohomologyDiagram_map_app`). The body is exposed so that the values of the diagram unfold to
Čech cohomology objects, which the statements about its maps need. -/
@[expose, simps obj]
def cechCohomologyDiagram : J ⥤ (Cᵒᵖ ⥤ A) ⥤ A where
  obj j := cechComplexFunctor (E j).obj ⋙ HomologicalComplex.homologyFunctor A _ n
  map {i j} f :=
    { app P := HomologicalComplex.homologyMap (cechComplexMap P (hE (leOfHom f)).some) n
      naturality P Q α := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
        (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_naturality P α _)).trans
          (HomologicalComplex.homologyMap_comp _ _ n) }
  map_id j := by
    ext P
    exact ((cechComplexMapHomotopy P _ (𝟙 _)).homologyMap_eq n).trans <|
      (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_id P)).trans
        (HomologicalComplex.homologyMap_id _ n)
  map_comp {i j k} f g := by
    ext P
    exact ((cechComplexMapHomotopy P _
      ((hE (leOfHom g)).some ≫ (hE (leOfHom f)).some)).homologyMap_eq n).trans <|
        (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_comp P _ _)).trans
          (HomologicalComplex.homologyMap_comp _ _ n)

/-- **The transition maps do not depend on the refinement maps.** For `i ≤ j`, the transition map
of the diagram is the map on Čech cohomology induced by any morphism of families `E j ⟶ E i`. -/
theorem cechCohomologyDiagram_map_app {i j : J} (f : i ⟶ j) (φ : E j ⟶ E i) (P : Cᵒᵖ ⥤ A) :
    ((cechCohomologyDiagram A E hE n).map f).app P =
      HomologicalComplex.homologyMap (cechComplexMap P φ) n :=
  (cechComplexMapHomotopy P _ φ).homologyMap_eq n

/-! ### The colimit -/

variable [HasColimitsOfShape J A]

variable (A) in
/-- The degree `n` Čech cohomology for the system of families `E`, as a functor of the presheaf:
the colimit over `J` of the degree `n` Čech cohomologies `Hⁿ(Č(E j, P))`. The body is exposed so
that its values unfold to colimits in `A`. -/
@[expose]
def cechCohomology : (Cᵒᵖ ⥤ A) ⥤ A :=
  (cechCohomologyDiagram A E hE n).flip ⋙ colim

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

/-- The structure maps are compatible with the map on Čech cohomology induced by any morphism of
families `E j ⟶ E i`, for `i ≤ j`. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_cechCohomologyι_app {i j : J} (h : i ≤ j)
    (φ : E j ⟶ E i) (P : Cᵒᵖ ⥤ A) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ (cechCohomologyι E hE n j).app P =
      (cechCohomologyι E hE n i).app P :=
  (congrArg (· ≫ (cechCohomologyι E hE n j).app P)
    (cechCohomologyDiagram_map_app E hE n (homOfLE h) φ P)).symm.trans
      (NatTrans.congr_app (cechCohomologyDiagram_map_comp_cechCohomologyι E hE n (homOfLE h)) P)

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
            (cechCohomologyDiagram_map_app E hE n h (hE (leOfHom h)).some P =≫ f j).trans
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

/-! ### Maps from refined families

A family `G` that is refined by some member `E i` of the system, but need not belong to the system
itself, also has a structure map from its Čech cohomology to the Čech cohomology for the system.
For open covers, this is the map from the Čech cohomology of an arbitrary cover. -/

/-- The structure map from the degree `n` Čech cohomology of a family `G` refined by some member of
the system, natural in the presheaf. It is the map induced by a chosen morphism of families
`E i ⟶ G`, followed by the structure map at `i`; when `J` is directed, it does not depend on the
choice (`cechCohomologyιOfRefinement_app_eq`). -/
def cechCohomologyιOfRefinement (G : FormalCoproduct.{w} C) (hG : ∃ i, Nonempty (E i ⟶ G)) :
    cechComplexFunctor G.obj ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechCohomology A E hE n where
  app P := HomologicalComplex.homologyMap (cechComplexMap P hG.choose_spec.some) n ≫
    (cechCohomologyι E hE n hG.choose).app P
  naturality P _ α :=
    -- the map induced by the refinement and the structure map are both natural in the presheaf
    (HomologicalComplex.homologyMap_comp_assoc _ _ n _).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · n ≫ _) (cechComplexMap_naturality P α _)).trans <|
        (HomologicalComplex.homologyMap_comp_assoc _ _ n _).trans <|
          (_ ≫= (cechCohomologyι E hE n hG.choose).naturality α).trans (Category.assoc _ _ _).symm

/-- Passing from a member `E i` refining a family `G` to a finer member `E j` does not change the
composite of the induced map on cohomology with the structure map. -/
private lemma homologyMap_comp_cechCohomologyι_app_eq_of_le (P : Cᵒᵖ ⥤ A)
    {G : FormalCoproduct.{w} C} {i j : J} (hij : i ≤ j) (ψ : E j ⟶ E i) (φ : E i ⟶ G) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ (cechCohomologyι E hE n i).app P =
      HomologicalComplex.homologyMap (cechComplexMap P (ψ ≫ φ)) n ≫
        (cechCohomologyι E hE n j).app P :=
  (_ ≫= homologyMap_cechComplexMap_comp_cechCohomologyι_app E hE n hij ψ P).symm.trans <|
    (HomologicalComplex.homologyMap_comp_assoc _ _ n _).symm.trans <|
      congrArg (HomologicalComplex.homologyMap · n ≫ _) (cechComplexMap_comp P ψ φ).symm

section Directed

variable [IsDirected J (· ≤ ·)]

/-- Any two members of a directed system refining a family `G` give the same composite of the
induced map on cohomology with the structure map. -/
private lemma homologyMap_comp_cechCohomologyι_app_eq (P : Cᵒᵖ ⥤ A) {G : FormalCoproduct.{w} C}
    {i₁ i₂ : J} (φ₁ : E i₁ ⟶ G) (φ₂ : E i₂ ⟶ G) :
    HomologicalComplex.homologyMap (cechComplexMap P φ₁) n ≫ (cechCohomologyι E hE n i₁).app P =
      HomologicalComplex.homologyMap (cechComplexMap P φ₂) n ≫
        (cechCohomologyι E hE n i₂).app P := by
  -- compare both on a common upper bound `j` of `i₁` and `i₂`
  obtain ⟨j, h₁, h₂⟩ := exists_ge_ge i₁ i₂
  rw [homologyMap_comp_cechCohomologyι_app_eq_of_le E hE n P h₁ (hE h₁).some,
    homologyMap_comp_cechCohomologyι_app_eq_of_le E hE n P h₂ (hE h₂).some,
    (cechComplexMapHomotopy P _ _).homologyMap_eq n]

/-- The structure map from the Čech cohomology of a refined family `G` is the map induced by any
morphism of families `E i ⟶ G`, followed by the structure map at `i`. -/
theorem cechCohomologyιOfRefinement_app_eq (G : FormalCoproduct.{w} C)
    (hG : ∃ i, Nonempty (E i ⟶ G)) (i : J) (φ : E i ⟶ G) (P : Cᵒᵖ ⥤ A) :
    (cechCohomologyιOfRefinement E hE n G hG).app P =
      HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ (cechCohomologyι E hE n i).app P :=
  homologyMap_comp_cechCohomologyι_app_eq E hE n P _ _

/-- On a member of the system, the structure map for refined families is the structure map of the
colimit. -/
@[simp]
theorem cechCohomologyιOfRefinement_app_self (j : J) (hG : ∃ i, Nonempty (E i ⟶ E j))
    (P : Cᵒᵖ ⥤ A) :
    (cechCohomologyιOfRefinement E hE n (E j) hG).app P = (cechCohomologyι E hE n j).app P := by
  rw [cechCohomologyιOfRefinement_app_eq E hE n (E j) hG j (𝟙 _), cechComplexMap_id,
    HomologicalComplex.homologyMap_id]
  exact Category.id_comp _

/-- The structure maps from the Čech cohomology of refined families are compatible with morphisms
of families: for `φ : H ⟶ G`, the map induced by `φ` on cohomology followed by the structure map
from `H` is the structure map from `G`. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_cechCohomologyιOfRefinement_app
    {G H : FormalCoproduct.{w} C} (hG : ∃ i, Nonempty (E i ⟶ G)) (hH : ∃ i, Nonempty (E i ⟶ H))
    (φ : H ⟶ G) (P : Cᵒᵖ ⥤ A) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫
        (cechCohomologyιOfRefinement E hE n H hH).app P =
      (cechCohomologyιOfRefinement E hE n G hG).app P := by
  obtain ⟨i, ⟨ψ⟩⟩ := hH
  rw [cechCohomologyιOfRefinement_app_eq E hE n H _ i ψ,
    cechCohomologyιOfRefinement_app_eq E hE n G hG i (ψ ≫ φ)]
  exact ((congrArg (HomologicalComplex.homologyMap · n ≫ _) (cechComplexMap_comp P ψ φ)).trans
    (HomologicalComplex.homologyMap_comp_assoc _ _ n _)).symm

end Directed

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
    rw [Functor.flip_obj_map, cechCohomologyDiagram_map_app E hE 0 f (hE (leOfHom f)).some]
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
