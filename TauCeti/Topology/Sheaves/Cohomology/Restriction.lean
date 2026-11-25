/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.Topology.Sheaves.ExtensionByZero
public import Mathlib.Topology.Sheaves.Over
public import TauCeti.Topology.Sheaves.Over
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
public import TauCeti.CategoryTheory.Sites.Over

/-!
# Cohomology depends only on the restricted sheaf

The sheaf cohomology `Hⁿ(U, F)` of an abelian sheaf `F` on an open subset `U` of a topological
space `X` is naturally isomorphic to the global cohomology `Hⁿ(U, F|_U)` of its restriction
`U.sheafRestrict.obj F` (`TopologicalSpace.Opens.cohomologyPresheafObjIsoSheafRestrictH`). In
particular, an isomorphism between the restrictions of two abelian sheaves to `U` induces an
isomorphism on their cohomology over `U` (`TopologicalSpace.Opens.cohomologyIsoOfRestrictIso`),
allowing local trivializations and open-subset structure theorems to transport acyclicity without
requiring an isomorphism on the whole space.

The construction uses the localized-site comparison
`CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH` together with site
invariance along `TopologicalSpace.Opens.overEquivalence`.

For module sheaves, native derived restriction commutes with the top and nested opens;
the chosen-resolution formula uses the original module section carriers.
-/

public noncomputable section

open CategoryTheory Limits Opposite

namespace TopologicalSpace.Opens

universe u

variable {X : TopCat.{u}}

/-- The cohomology of an abelian sheaf at an open subset `U` is naturally isomorphic to the global
cohomology of its restriction `U.sheafRestrict.obj F` on the open subspace `U`. -/
def cohomologyPresheafEvaluationIsoSheafRestrictFunctorH (U : Opens X) (n : ℕ) :
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      U.sheafRestrict ⋙ Sheaf.functorH (Opens.grothendieckTopology U) n := by
  let J := Opens.grothendieckTopology X
  let JU := Opens.grothendieckTopology U
  let P := J.overPullback AddCommGrpCat.{u} U
  let E := (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor
  let CU := Sheaf.cohomologyPresheafFunctor JU n ⋙
    (evaluation (Opens U)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  exact J.cohomologyPresheafEvaluationIsoFunctorOverH U n ≪≫
    Functor.isoWhiskerLeft P
      ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).symm ≪≫
      (TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr (J.over U) JU
        U.overEquivalence n (⊤ : Opens U)).symm) ≪≫
    (Functor.associator P E CU).symm ≪≫
    Functor.isoWhiskerRight (U.overPullbackSheafEquivOver (A := AddCommGrpCat.{u})) CU ≪≫
    Functor.isoWhiskerLeft U.sheafRestrict
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH JU n isTerminalTop)

/-- The cohomology `Hⁿ(U, F)` of an abelian sheaf `F` on an open subset `U` is isomorphic to the
global cohomology `Hⁿ(U, F|_U)` of the restricted sheaf `U.sheafRestrict.obj F`. -/
def cohomologyPresheafObjIsoSheafRestrictH (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H' F n U ≅ AddCommGrpCat.of (Sheaf.H (U.sheafRestrict.obj F) n) :=
  (U.cohomologyPresheafEvaluationIsoSheafRestrictFunctorH n).app F

/-- An isomorphism of sheaves after restriction to `U` induces an isomorphism on cohomology
on `U`, in every degree. -/
def cohomologyIsoOfRestrictIso (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (e : U.sheafRestrict.obj F ≅ U.sheafRestrict.obj G) (n : ℕ) :
    Sheaf.H' F n U ≅ Sheaf.H' G n U :=
  (U.cohomologyPresheafEvaluationIsoSheafRestrictFunctorH n).app F ≪≫
    (Sheaf.functorH (Opens.grothendieckTopology U) n).mapIso e ≪≫
    ((U.cohomologyPresheafEvaluationIsoSheafRestrictFunctorH n).app G).symm

/-- The identity of the restricted sheaf induces the identity on cohomology. -/
@[simp]
theorem cohomologyIsoOfRestrictIso_refl (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    U.cohomologyIsoOfRestrictIso (Iso.refl _) n = Iso.refl (Sheaf.H' F n U) :=
  Iso.ext <| by simp [cohomologyIsoOfRestrictIso]

/-- Composing isomorphisms of restricted sheaves composes the induced cohomology isomorphisms. -/
theorem cohomologyIsoOfRestrictIso_trans (U : Opens X) {F G H : X.Sheaf AddCommGrpCat.{u}}
    (e₁ : U.sheafRestrict.obj F ≅ U.sheafRestrict.obj G)
    (e₂ : U.sheafRestrict.obj G ≅ U.sheafRestrict.obj H) (n : ℕ) :
    U.cohomologyIsoOfRestrictIso (e₁ ≪≫ e₂) n =
      U.cohomologyIsoOfRestrictIso e₁ n ≪≫ U.cohomologyIsoOfRestrictIso e₂ n :=
  Iso.ext <| by simp [cohomologyIsoOfRestrictIso]

end TopologicalSpace.Opens

/-! ### Resolution classes and native derived global-sections restriction -/

open CategoryTheory.Abelian TauCeti.CategoryTheory
namespace TopologicalSpace.Opens
private abbrev ambientTopology {X : TopCat.{u}} := Opens.grothendieckTopology X
private abbrev overTopology {X : TopCat.{u}} (U : Opens X) := (Opens.grothendieckTopology X).over U
private abbrev overRestriction {X : TopCat.{u}} (U : Opens X) :=
  (Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U
private abbrev subspaceTopology {X : TopCat.{u}} (U : Opens X) := Opens.grothendieckTopology U
variable {X : TopCat.{u}} (U : Opens X)
private lemma cohomologyPresheafObjIsoSheafRestrictH_hom_apply (F : X.Sheaf AddCommGrpCat.{u})
    (n : ℕ) (x : F.H' n U) :
    (U.cohomologyPresheafObjIsoSheafRestrictH F n).hom x =
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (subspaceTopology U) n isTerminalTop).hom.app
        (U.sheafRestrict.obj F)
        ((cohomologyPresheafEvaluationIsoSheafCongr (overTopology U) (subspaceTopology U)
          U.overEquivalence n (⊤ : Opens U)).inv.app ((overRestriction U).obj F)
          ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (overTopology U) n
            (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).inv.app
            ((overRestriction U).obj F)
            (((ambientTopology (X := X)).cohomologyPresheafEvaluationIsoFunctorOverH U
              n).hom.app F x))) := by
  let z := (cohomologyPresheafEvaluationIsoSheafCongr (overTopology U) (subspaceTopology U)
    U.overEquivalence n (⊤ : Opens U)).inv.app ((overRestriction U).obj F)
    ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (overTopology U) n
      (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).inv.app ((overRestriction U).obj F)
      (((ambientTopology (X := X)).cohomologyPresheafEvaluationIsoFunctorOverH U n).hom.app F x))
  let b := (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (subspaceTopology U) n
    isTerminalTop).hom.app (U.sheafRestrict.obj F)
  let CU := Sheaf.cohomologyPresheafFunctor (subspaceTopology U) n ⋙
    (evaluation (Opens U)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  -- The over-site/restriction comparison has identity components on underlying presheaves.
  change b ((CU.map (𝟙 (U.sheafRestrict.obj F))) z) = b z
  erw [CU.map_id, ConcreteCategory.id_apply]

open CochainComplex
private abbrev overTop := U.overEquivalence.inverse.obj (⊤ : Opens U)
variable {F : X.Sheaf AddCommGrpCat.{u}}
  (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ)
  (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1))
/-- The abelian open-comparison isomorphism preserves the class of a resolution cocycle. -/
lemma cohomologyPresheafObjIsoSheafRestrictH_resolutionClass {n : ℕ} (s : (K.X n).obj.obj (op U))
    (hs : (K.d n (n + 1)).hom.app (op U) s = 0) :
    (U.cohomologyPresheafObjIsoSheafRestrictH F n).hom
      (Sheaf.H'.resolutionClass ι hι hι' hK U s hs) =
    (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (Opens.grothendieckTopology U) n
      isTerminalTop).hom.app
      (U.sheafRestrict.obj F)
      (Sheaf.H'.resolutionClass (U.sheafRestrict.map ι)
        (CochainComplex.map_augmentation_comp_d U.sheafRestrict K ι hι)
        (CochainComplex.map_augmentation_exact U.sheafRestrict K ι hι hι')
        (CochainComplex.map_exactAt_succ U.sheafRestrict K hK) (⊤ : Opens U)
        ((K.X n).obj.map (overTopMap U).left.op s)
        (HomologicalComplex.d_app_map_eq_zero
          (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj K)
          (overTopMap U).left.op s hs)) := by
  let G := overRestriction U
  let KG := ((G.mapHomologicalComplex (.up ℕ)).obj K)
  let ιG := G.map ι
  let hG := CochainComplex.map_augmentation_comp_d G K ι hι
  let hG' := CochainComplex.map_augmentation_exact G K ι hι hι'
  let hKG := CochainComplex.map_exactAt_succ G K hK
  let xG := Sheaf.H'.resolutionClass ιG hG hG' hKG (Over.mk (𝟙 U)) s hs
  let t : (KG.X n).obj.obj (op (overTop U)) := (KG.X n).obj.map (overTopMap U).op s
  have ht : (KG.d n (n + 1)).hom.app (op (overTop U)) t = 0 :=
    HomologicalComplex.d_app_map_eq_zero
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj KG)
      (overTopMap U).op s hs
  have hOver := GrothendieckTopology.cohomologyPresheafObjIsoOver_resolutionClass (ambientTopology
    (X := X)) U K ι hι hι' hK s hs
  have hTerm := (G.obj F).cohomologyPresheafObjIsoH_terminal_change
    (isTerminalTop.isTerminalObj U.overEquivalence.inverse) (Over.mkIdTerminal (X := U))
    (overTopMap U) n xG
  have hRestr := Sheaf.H'.cohomologyPresheaf_map_resolutionClass
    ιG hG hG' hKG (Over.mk (𝟙 U)) (overTopMap U) s hs
  let E := (U.overEquivalence.sheafCongr (overTopology U) (subspaceTopology U)
    AddCommGrpCat.{u}).functor
  let : Mono ιG := inferInstance
  let y : (E.obj (G.obj F)).H' n (⊤ : Opens U) :=
    Sheaf.H'.resolutionClass (E.map ιG) (CochainComplex.map_augmentation_comp_d E KG ιG hG)
      (CochainComplex.map_augmentation_exact E KG ιG hG hG') (CochainComplex.map_exactAt_succ E KG
        hKG)
      (⊤ : Opens U) t ht
  let xS := Sheaf.H'.resolutionClass ιG hG hG' hKG (overTop U) t ht
  let q : (E.obj (G.obj F)).H' n (⊤ : Opens U) ≅ (G.obj F).H' n (overTop U) :=
    (cohomologyPresheafEvaluationIsoSheafCongr (overTopology U) (subspaceTopology U)
      U.overEquivalence n (⊤ : Opens U)).app (G.obj F)
  have hInv : q.inv xS = y :=
    cohomologyPresheafEvaluationIsoSheafCongr_inv_resolutionClass
      (overTopology U) (subspaceTopology U) U.overEquivalence KG ιG hG hG' hKG (⊤ : Opens U) t ht
  let F0 := U.sheafRestrict.obj F
  let b := (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (subspaceTopology U) n
    isTerminalTop).hom.app F0
  let z : (E.obj (G.obj F)).H' n (⊤ : Opens U) := q.inv
    (((G.obj F).cohomologyPresheafObjIsoH n
      (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).inv
      (((G.obj F).cohomologyPresheafObjIsoH n (Over.mkIdTerminal (X := U))).hom xG))
  have hz : z = y := by simpa only [z, hTerm, xG] using (congrArg q.inv hRestr).trans hInv
  rw [cohomologyPresheafObjIsoSheafRestrictH_hom_apply, hOver]
  -- The component formula has already cancelled the identity coefficient map.
  exact congrArg b hz
end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]

end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]

/-- Derived sections on an open set are derived global sections of its restricted sheaf. -/
def rightDerivedSectionsRestrictIso (U : Opens X)
    (n : ℕ) :
    ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U)).rightDerived n ≅
      U.sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).rightDerived n := by
  exact Functor.rightDerivedPrecompIso _ U.sheafRestrict
    (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)) (sheafRestrictΓIso U) n

/-- The native all-degree restriction map, derived from ΓRes and the sections comparison. -/
def rightDerivedΓRestriction (U : Opens X)
    (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ⟶
      U.sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).rightDerived n :=
  (Sheaf.natTransΓRes (Opens.grothendieckTopology X) (ModuleCat.{u} R) (op U)).rightDerived n ≫
    (rightDerivedSectionsRestrictIso U n).hom

end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
variable (U : Opens X)

/-- The cochain restriction map for a module sheaf and any injective resolution. -/
def rightDerivedΓRestrictionComplexMap {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) :
    ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶
    ((Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
        I).cocomplex := by
  let H := U.sheafRestrict (C := ModuleCat.{u} R)
  exact (NatTrans.mapHomologicalComplex
      (Sheaf.natTransΓRes (Opens.grothendieckTopology X) (ModuleCat.{u} R) (op U) ≫
        (sheafRestrictΓIso U).hom) _).app I.cocomplex ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (H ⋙ Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R))) _).inv.app
        I.cocomplex

/-- Each cochain component is section restriction followed by the open/global comparison. -/
@[simp]
lemma rightDerivedΓRestrictionComplexMap_f {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) :
    (rightDerivedΓRestrictionComplexMap U I).f j =
      (I.cocomplex.X j).ΓRes (op U) ≫
        (sheafRestrictΓIso U).hom.app (I.cocomplex.X j) := by
  rfl

/-- Compute native derived restriction using the cochain restriction on any resolution. -/
theorem rightDerivedΓRestriction_app_injectiveResolution {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) :
    (rightDerivedΓRestriction U n).app F ≫
      (((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I).isoRightDerivedObj
        (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)) n).hom =
    (I.isoRightDerivedObj (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom ≫
      HomologicalComplex.homologyMap (rightDerivedΓRestrictionComplexMap U I) n := by
  let E := (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U)
  have hc := Functor.rightDerivedPrecompIso_app_hom E U.sheafRestrict
    (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)) (sheafRestrictΓIso U) I n
  have ha := I.rightDerived_app_eq
    (Sheaf.natTransΓRes (Opens.grothendieckTopology X) (ModuleCat.{u} R) (op U)) n
  dsimp only [rightDerivedΓRestriction, NatTrans.comp_app]
  rw [Category.assoc]
  erw [hc, ← Category.assoc, ha]
  dsimp only [E, Functor.mapInjectiveResolution]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← HomologicalComplex.homologyMap_comp]
  congr 1


end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
/-- The canonical top-open identification of native derived global sections. -/
def rightDerivedΓRestrictionTopIso (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ≅
      (⊤ : Opens X).sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology (⊤ : Opens X)) (ModuleCat.{u} R)).rightDerived n :=
  NatIso.rightDerived (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    (ModuleCat.{u} R) isTerminalTop) n ≪≫
      rightDerivedSectionsRestrictIso (⊤ : Opens X) n
/-- Restriction to the top open equals the canonical derived-sections identification. -/
@[simp]
lemma rightDerivedΓRestriction_top (n : ℕ) :
    rightDerivedΓRestriction (R := R) (⊤ : Opens X) n =
      (rightDerivedΓRestrictionTopIso (X := X) (R := R) n).hom := by
  dsimp only [rightDerivedΓRestriction, rightDerivedΓRestrictionTopIso, Iso.trans_hom]
  rw [Sheaf.natTransΓRes_eq_ΓNatIsoSheafSections_hom _ _ isTerminalTop, NatIso.rightDerived_hom]
/-- The independent canonical top-open isomorphism has the native resolution computation. -/
lemma rightDerivedΓRestrictionTopIso_app {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) :
    (rightDerivedΓRestrictionTopIso (X := X) (R := R) n).hom.app F ≫
      ((((⊤ : Opens X).sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
        I).isoRightDerivedObj
        (Sheaf.Γ (Opens.grothendieckTopology (⊤ : Opens X)) (ModuleCat.{u} R)) n).hom =
    (I.isoRightDerivedObj (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom ≫
      HomologicalComplex.homologyMap
        (rightDerivedΓRestrictionComplexMap (⊤ : Opens X) I) n := by
  rw [← rightDerivedΓRestriction_top]
  exact rightDerivedΓRestriction_app_injectiveResolution (⊤ : Opens X) I n

end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
variable (U : Opens X)
/-- Each cochain component is the native section restriction, in the section carriers. -/
@[reassoc]
lemma rightDerivedΓRestrictionComplexMap_f_ΓRes {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
      ((((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
        I).cocomplex.X j).ΓRes (op ⊤)) =
    (I.cocomplex.X j).ΓRes (op U) ≫
      (sheafRestrictSectionsTopIso U).hom.app (I.cocomplex.X j) := by
  erw [rightDerivedΓRestrictionComplexMap_f]
  -- The mapped injective resolution has the corresponding restricted terms.
  exact (Category.assoc _ _ _).trans
    (congrArg ((I.cocomplex.X j).ΓRes (op U) ≫ ·)
      (sheafRestrictΓIso_hom_app_ΓRes U (I.cocomplex.X j)))

end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
variable (U : Opens X)
/-- Each component restricts sections on every open of the open subspace. -/
@[reassoc]
lemma rightDerivedΓRestrictionComplexMap_f_ΓRes_open {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) (D : Opens U) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
        (((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
          I).cocomplex.X j).ΓRes (op D) =
      (I.cocomplex.X j).ΓRes (op (U.isOpenEmbedding.functor.obj D)) := by
  let F := I.cocomplex.X j
  erw [← Sheaf.ΓRes_map _ (homOfLE (show D ≤ ⊤ from le_top)).op,
    ← Category.assoc, rightDerivedΓRestrictionComplexMap_f_ΓRes]
  rw [sheafRestrictSectionsTopIso_hom_app]
  change F.ΓRes (op U) ≫ F.obj.map _ ≫ F.obj.map _ = _
  -- The native restriction uses the same subtype topology through the bundled opens object.
  erw [← F.obj.map_comp]
  exact Sheaf.ΓRes_map F _
end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R] {U V : Opens X}


/-- Transport derived global sections along the canonical relative-open equivalence. -/
def relativeDerivedΓIso (h : V ≤ U) (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u}
      R)).rightDerived n ≅
    (relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor ⋙
      (Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).rightDerived n := by
  exact Functor.rightDerivedPrecompIso _ (relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor
    _ (relativeΓIso h) n

private abbrev transportedInjectiveResolution (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    InjectiveResolution ((relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor.obj F) :=
  (relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor.mapInjectiveResolution I
/-- Apply the relative global-sections comparison to a chosen resolution. -/
def relativeΓComplexMap (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    ((Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶
    ((Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj
      (((relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor.mapInjectiveResolution
        I).cocomplex) := by
  let T := (relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor
  exact (NatTrans.mapHomologicalComplex (relativeΓIso h).hom _).app I.cocomplex ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (T ⋙ Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R))) _).inv.app
        I.cocomplex
/-- Components of the resolution comparison are the relative Γ comparison. -/
@[simp]
lemma relativeΓComplexMap_f (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (j : ℕ) :
    (relativeΓComplexMap h I).f j = (relativeΓIso h).hom.app (I.cocomplex.X j) :=
  Category.comp_id _

/-- The derived relative comparison is computed on any chosen injective resolution. -/
lemma relativeDerivedΓIso_app (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (n : ℕ) :
    (relativeDerivedΓIso h n).hom.app F ≫
      (((relativeSheafEquivalence (A := ModuleCat.{u} R) h).functor.mapInjectiveResolution
        I).isoRightDerivedObj
        (Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)) n).hom =
    (I.isoRightDerivedObj
      (Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u} R)) n).hom ≫
      HomologicalComplex.homologyMap (relativeΓComplexMap h I) n := by
  -- This is the chosen-resolution component of the public relative Γ comparison.
  exact Functor.rightDerivedPrecompIso_app_hom _ _ _ (relativeΓIso h) I n

private abbrev nestedResolution (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)} (I :
  InjectiveResolution F) :=
  transportedInjectiveResolution h
    ((((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
      := ModuleCat.{u} R)).mapInjectiveResolution
      ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)))
private def nestedCoefficientComplexMap (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) : (nestedResolution h I).cocomplex ⟶
    (((V.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)).cocomplex := by
  letI := Functor.preservesZeroMorphisms_of_iso
    (nestedRestrictionIso (A := ModuleCat.{u} R) h).symm
  dsimp only [nestedResolution, transportedInjectiveResolution, Functor.mapInjectiveResolution]
  exact (NatTrans.mapHomologicalComplex
    (nestedRestrictionIso (A := ModuleCat.{u} R) h).hom (.up ℕ)).app I.cocomplex

private lemma nestedCoefficientComplexMap_f (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) :
    (nestedCoefficientComplexMap h I).f j = (nestedRestrictionIso h).hom.app (I.cocomplex.X
      j) := by
  rfl

@[reassoc]
private lemma relativeΓComplexMap_allProjections (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) (D : Opens V) :
    (relativeΓComplexMap h I).f j ≫
        ((transportedInjectiveResolution h I).cocomplex.X j).ΓRes (op D) =
      (I.cocomplex.X j).ΓRes (op ((Opens.map (relativeOpenIso h).hom).obj D)) := by
  rw [relativeΓComplexMap_f]
  exact relativeΓIso_hom_app_ΓRes h (I.cocomplex.X j) D


private lemma nestedComplexComposition_allProjections (h : V ≤ U)
    {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (j : ℕ) (D : Opens V) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
      (rightDerivedΓRestrictionComplexMap (X := TopCat.of U) (relativeOpen h)
        ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)).f j ≫
      (relativeΓComplexMap h
        ((((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
          := ModuleCat.{u} R)).mapInjectiveResolution
          ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)))).f j ≫
      (Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).map
        ((nestedCoefficientComplexMap h I).f j) ≫
      ((((V.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
        I)).cocomplex.X j).ΓRes (op D) =
    (I.cocomplex.X j).ΓRes (op (V.isOpenEmbedding.functor.obj D)) := by
  let IU := ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)
  let IW := (((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
    := ModuleCat.{u} R)).mapInjectiveResolution
    IU)
  have hH := relativeΓComplexMap_allProjections h IW j D
  have hW := rightDerivedΓRestrictionComplexMap_f_ΓRes_open
    (X := TopCat.of U) (relativeOpen h) IU j ((relativeSites h).inverse.obj D)
  have hU := rightDerivedΓRestrictionComplexMap_f_ΓRes_open U I j
    ((relativeInclusionSites h).obj ((relativeSites h).inverse.obj D))
  erw [Sheaf.ΓRes_naturality, reassoc_of% hH, reassoc_of% hW, reassoc_of% hU]
  erw [nestedCoefficientComplexMap_f, nestedRestrictionIso_hom_app_hom_app]
  exact Sheaf.ΓRes_map _ _

private lemma nestedComplexComposition (h : V ≤ U)
    {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    rightDerivedΓRestrictionComplexMap U I ≫
      rightDerivedΓRestrictionComplexMap (X := TopCat.of U) (relativeOpen h)
        ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I) ≫
      relativeΓComplexMap h
        ((((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
          := ModuleCat.{u} R)).mapInjectiveResolution
          ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I))) ≫
      ((Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).mapHomologicalComplex
        (.up ℕ)).map (nestedCoefficientComplexMap h I) =
      rightDerivedΓRestrictionComplexMap V I := by
  apply HomologicalComplex.hom_ext
  intro j
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology V) (ModuleCat.{u} R) isTerminalTop).hom.app
      ((((V.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)).cocomplex.X j))).mp
  rw [CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
  rw [nestedComplexComposition_allProjections, rightDerivedΓRestrictionComplexMap_f_ΓRes_open]

/-- Direct derived restriction equals restriction through the nested open subspace. -/
theorem rightDerivedΓRestriction_nested (h : V ≤ U) (F : X.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
  (rightDerivedΓRestriction (R := R) V n).app F =
    (rightDerivedΓRestriction (R := R) U n).app F ≫
    (rightDerivedΓRestriction (X := TopCat.of U) (R := R) (relativeOpen h) n).app
      (U.sheafRestrict.obj F) ≫
    (relativeDerivedΓIso (R := R) h n).hom.app
      (((relativeOpen h).sheafRestrict (X := TopCat.of U) (C := ModuleCat.{u} R)).obj
        (U.sheafRestrict.obj F)) ≫
    ((Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).rightDerived n).map
      ((nestedRestrictionIso h).hom.app F) := by
  let I := injectiveResolution F
  let IU := ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)
  let IW := (((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
    := ModuleCat.{u} R)).mapInjectiveResolution
    IU)
  let IV := ((V.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)
  let IT := nestedResolution h I
  let ΓV := Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)
  apply (cancel_mono (IV.isoRightDerivedObj ΓV n).hom).mp
  rw [rightDerivedΓRestriction_app_injectiveResolution V I n]
  have hcomm : IT.ι.f 0 ≫ (nestedCoefficientComplexMap h I).f 0 =
      (nestedRestrictionIso h).hom.app F ≫ IV.ι.f 0 := by
    rw [nestedCoefficientComplexMap_f]
    dsimp only [IT, IV, nestedResolution, transportedInjectiveResolution]
    simp only [Functor.mapInjectiveResolution_ι_f_zero]
    exact (nestedRestrictionIso h).hom.naturality (I.ι.f 0)
  have hA := InjectiveResolution.isoRightDerivedObj_hom_naturality
    ((nestedRestrictionIso h).hom.app F) IT IV (nestedCoefficientComplexMap h I)
    hcomm ΓV n
  -- The composed section functor maps the complex map degreewise before taking homology.
  change _ = _ ≫ HomologicalComplex.homologyMap ((ΓV.mapHomologicalComplex _).map _) n at hA
  have hH := relativeDerivedΓIso_app h IW n
  have hW := rightDerivedΓRestriction_app_injectiveResolution (X := TopCat.of U) (relativeOpen h)
    IU n
  have hU := rightDerivedΓRestriction_app_injectiveResolution U I n
  have hs := (CommSq.mk hU).horiz_comp ((CommSq.mk hW).horiz_comp
    ((CommSq.mk hH).horiz_comp (CommSq.mk hA)))
  have hc := congrArg (fun f ↦ HomologicalComplex.homologyMap f n)
    (nestedComplexComposition h I)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  exact (congrArg ((I.isoRightDerivedObj _ n).hom ≫ ·) hc).symm.trans hs.w.symm

end TopologicalSpace.Opens
