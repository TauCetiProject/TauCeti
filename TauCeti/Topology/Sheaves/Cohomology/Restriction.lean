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

For module sheaves, native derived restriction commutes with the top and actual nested opens;
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
        (((Sheaf.cohomologyPresheafFunctor (subspaceTopology U) n ⋙
          (evaluation (Opens U)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
          ((U.overPullbackSheafEquivOver (A := AddCommGrpCat.{u})).hom.app F))
          ((cohomologyPresheafEvaluationIsoSheafCongr (overTopology U) (subspaceTopology U)
            U.overEquivalence n (⊤ : Opens U)).inv.app ((overRestriction U).obj F)
            ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (overTopology U) n
              (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).inv.app ((overRestriction
                U).obj F)
              (((ambientTopology (X := X)).cohomologyPresheafEvaluationIsoFunctorOverH U
                n).hom.app F x)))) := by
  rfl

open CochainComplex
private abbrev overTop := U.overEquivalence.inverse.obj (⊤ : Opens U)
private abbrev overTopMap : overTop U ⟶ Over.mk (𝟙 U) := (Over.mkIdTerminal (X := U)).from _
/-- Restriction of sheaves with preadditive values is additive. -/
instance sheafRestrict_additive {Y : Type u} [TopologicalSpace Y] (V : Opens Y)
    {A : Type*} [Category A] [Preadditive A] :
    (V.sheafRestrict (X := TopCat.of Y) (C := A)).Additive where
  map_add := by intros; rfl
local instance : (U.overEquivalence.sheafCongr
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U)
        AddCommGrpCat.{u}).functor.Additive where
  map_add := by intros; rfl
local instance : PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
  change PreservesFiniteColimits (overRestriction U ⋙ (U.overEquivalence.sheafCongr (overTopology
    U) (subspaceTopology U) AddCommGrpCat.{u}).functor)
  infer_instance
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
        ((K.X n).obj.map ((Over.mkIdTerminal (X := U)).from (U.overEquivalence.inverse.obj
          ⊤)).left.op s)
        (by
          change (K.d n (n + 1)).hom.app (op (U.overEquivalence.inverse.obj ⊤).left) _ = 0
          erw [NatTrans.naturality_apply, hs, map_zero])) := by
  let G := overRestriction U
  let KG := ((G.mapHomologicalComplex (.up ℕ)).obj K)
  let ιG := G.map ι
  let hG := CochainComplex.map_augmentation_comp_d G K ι hι
  let hG' := CochainComplex.map_augmentation_exact G K ι hι hι'
  let hKG := CochainComplex.map_exactAt_succ G K hK
  let xG := Sheaf.H'.resolutionClass ιG hG hG' hKG (Over.mk (𝟙 U)) s hs
  let t : (KG.X n).obj.obj (op (overTop U)) := (KG.X n).obj.map (overTopMap U).op s
  have ht : (KG.d n (n + 1)).hom.app (op (overTop U)) t = 0 := by
    dsimp only [t]
    erw [NatTrans.naturality_apply, hs, map_zero]
  have hOver := GrothendieckTopology.cohomologyPresheafObjIsoOver_resolutionClass (ambientTopology
    (X := X)) U K ι hι hι' hK s hs
  have hTerm := TauCeti.CategoryTheory.cohomologyPresheafObjIsoH_terminal_change (overTopology U)
    (isTerminalTop.isTerminalObj U.overEquivalence.inverse) (Over.mkIdTerminal (X := U))
    (overTopMap U) (G.obj F) n xG
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
  let CU := Sheaf.cohomologyPresheafFunctor (subspaceTopology U) n ⋙
    (evaluation (Opens U)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let b := (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (subspaceTopology U) n
    isTerminalTop).hom.app F0
  let z : (E.obj (G.obj F)).H' n (⊤ : Opens U) := q.inv
    (((G.obj F).cohomologyPresheafObjIsoH n
      (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).inv
      (((G.obj F).cohomologyPresheafObjIsoH n (Over.mkIdTerminal (X := U))).hom xG))
  have hz : z = y := by simpa only [z, hTerm, xG] using (congrArg q.inv hRestr).trans hInv
  rw [cohomologyPresheafObjIsoSheafRestrictH_hom_apply, hOver]
  change b ((CU.map (𝟙 F0)) z) = b y
  erw [CU.map_id, ConcreteCategory.id_apply]
  exact congrArg b hz
end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]

/-- Restriction preserves injective module sheaves by its exact extension-by-zero adjunction. -/
instance sheafRestrict_preservesInjectiveObjects {Y : Type u} [TopologicalSpace Y] (V : Opens Y) :
    (V.sheafRestrict (X := TopCat.of Y) (C := ModuleCat.{u} R)).PreservesInjectiveObjects := by
  let := preservesFiniteLimits_extendByZero (X := TopCat.of Y) V (ModuleCat.{u} R)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (V.extendByZeroAdjunction (X := TopCat.of Y) (ModuleCat.{u} R))
/-- Open restriction is exact on native module sheaves. -/
instance sheafRestrict_preservesHomology {Y : Type u} [TopologicalSpace Y] (V : Opens Y) :
    (V.sheafRestrict (X := TopCat.of Y) (C := ModuleCat.{u} R)).PreservesHomology := by
  let := (V.extendByZeroAdjunction (X := TopCat.of Y) (ModuleCat.{u} R)).isRightAdjoint
  let := isLeftAdjoint_sheafRestrict (X := TopCat.of Y) (A := ModuleCat.{u} R) V
  infer_instance

end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]

/-- Sections on an open set are sections at the top of the actual restricted sheaf. -/
def sheafRestrictSectionsTopIso (U : Opens X) :
    (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U) ≅
      U.sheafRestrict ⋙
        (sheafSections (Opens.grothendieckTopology U) (ModuleCat.{u} R)).obj
          (op (⊤ : Opens U)) := by
  have hU : (Topology.IsOpenEmbedding.functor (f := U.inclusion') U.isOpenEmbedding).obj
      (⊤ : Opens U) = U := by
    ext x
    change (x ∈ Subtype.val '' (Set.univ : Set U)) ↔ x ∈ U
    simp
  refine NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso hU).op) ?_
  intro F G f
  exact (f.hom.naturality (eqToIso hU).hom.op).symm

/-- Sections on an open set are the global sections of the actual restricted sheaf. -/
def sheafRestrictΓIso (U : Opens X) :
    (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U) ≅
      U.sheafRestrict ⋙ Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R) :=
  sheafRestrictSectionsTopIso U ≪≫
    Functor.isoWhiskerLeft U.sheafRestrict
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology U)
        (ModuleCat.{u} R) isTerminalTop).symm

/-- Evaluation of sections of module sheaves is additive. -/
instance sheafSections_additive (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Derived sections on an open set are derived global sections of its restricted sheaf. -/
def rightDerivedSectionsRestrictIso (U : Opens X)
    [(Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).Additive] (n : ℕ) :
    ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U)).rightDerived n ≅
      U.sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).rightDerived n := by
  let E := (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (op U)
  exact (Functor.rightUnitor (E.rightDerived n)).symm ≪≫
    Functor.rightDerivedCompIso E (𝟭 (ModuleCat.{u} R)) U.sheafRestrict
      (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R))
      (Functor.rightUnitor E ≪≫ sheafRestrictΓIso U) n

/-- The native all-degree restriction map, derived from ΓRes and the sections comparison. -/
def rightDerivedΓRestriction (U : Opens X)
    [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
    [(Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).Additive] (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ⟶
      U.sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).rightDerived n :=
  (Sheaf.natTransΓRes (Opens.grothendieckTopology X) (ModuleCat.{u} R) (op U)).rightDerived n ≫
    (rightDerivedSectionsRestrictIso U n).hom

end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
variable (U : Opens X)
variable [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [(Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).Additive]

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

/-- Compute native derived restriction using the actual cochain restriction on any resolution. -/
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
variable [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [(Sheaf.Γ (Opens.grothendieckTopology (⊤ : Opens X)) (ModuleCat.{u} R)).Additive]
/-- The canonical top-open identification of native derived global sections. -/
def rightDerivedΓRestrictionTopIso (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ≅
      (⊤ : Opens X).sheafRestrict ⋙
        (Sheaf.Γ (Opens.grothendieckTopology (⊤ : Opens X)) (ModuleCat.{u} R)).rightDerived n :=
  NatIso.rightDerived (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    (ModuleCat.{u} R) isTerminalTop) n ≪≫
      rightDerivedSectionsRestrictIso (⊤ : Opens X) n
/-- Restriction to the top open equals the canonical derived-sections identification. -/
lemma rightDerivedΓRestriction_top (n : ℕ) :
    rightDerivedΓRestriction (R := R) (⊤ : Opens X) n =
      (rightDerivedΓRestrictionTopIso (X := X) (R := R) n).hom := by
  dsimp only [rightDerivedΓRestriction, rightDerivedΓRestrictionTopIso, Iso.trans_hom]
  rw [Sheaf.natTransΓRes_eq_ΓNatIsoSheafSections_hom _ _ isTerminalTop, NatIso.rightDerived_hom]
end TopologicalSpace.Opens
namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
/-- The top-sections comparison is evaluation along the actual over-site terminal map. -/
lemma sheafRestrictSectionsTopIso_hom_app (U : Opens X) (F : X.Sheaf (ModuleCat.{u} R)) :
    (sheafRestrictSectionsTopIso U).hom.app F =
      F.obj.map ((Over.mkIdTerminal (X := U)).from (U.overEquivalence.inverse.obj ⊤)).left.op := by
  change F.obj.map _ = F.obj.map _
  congr 1
  exact Subsingleton.elim _ _
variable (U : Opens X)
variable [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [(Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).Additive]
/-- Each cochain component is the native section restriction, in the actual section carriers. -/
lemma rightDerivedΓRestrictionComplexMap_f_ΓRes {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
      ((((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
        I).cocomplex.X j).ΓRes (op ⊤)) =
    (I.cocomplex.X j).ΓRes (op U) ≫
      (sheafRestrictSectionsTopIso U).hom.app (I.cocomplex.X j) := by
  change (I.cocomplex.X j).ΓRes (op U) ≫
      (sheafRestrictΓIso U).hom.app (I.cocomplex.X j) ≫
      (U.sheafRestrict.obj (I.cocomplex.X j)).ΓRes (op ⊤) = _
  rw [← CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes _ _ isTerminalTop]
  change (I.cocomplex.X j).ΓRes (op U) ≫
    (sheafRestrictSectionsTopIso U).hom.app (I.cocomplex.X j) ≫
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).inv.app
      (U.sheafRestrict.obj (I.cocomplex.X j)) ≫
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app
      (U.sheafRestrict.obj (I.cocomplex.X j)) = _
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]

end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
variable (U : Opens X)
variable [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [(Sheaf.Γ (Opens.grothendieckTopology U) (ModuleCat.{u} R)).Additive]
@[reassoc]
private lemma rightDerivedΓRestrictionComplexMap_allProjections {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) (D : Opens U) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
        (((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution
          I).cocomplex.X j).ΓRes (op D) =
      (I.cocomplex.X j).ΓRes (op (U.isOpenEmbedding.functor.obj D)) := by
  let F := I.cocomplex.X j
  erw [← Sheaf.ΓRes_map _ (homOfLE (show D ≤ ⊤ from le_top)).op,
    ← Category.assoc, rightDerivedΓRestrictionComplexMap_f_ΓRes]
  change F.ΓRes (op U) ≫ F.obj.map _ ≫ F.obj.map _ = _
  rw [← F.obj.map_comp]
  exact Sheaf.ΓRes_map F _
end TopologicalSpace.Opens

namespace TopologicalSpace.Opens
variable {X : TopCat.{u}} {R : Type u} [CommRing R] {U V : Opens X}


private def inclusionSites (h : V ≤ U) : Opens V ⥤ Opens U :=
  Topology.IsOpenEmbedding.functor (X := TopCat.of V) (Y := TopCat.of U)
    (f := (Opens.toTopCat X).map (homOfLE h)) (isOpenEmbedding_of_le h)
private instance inclusionSites_continuous (h : V ≤ U) :
    (inclusionSites h).IsContinuous (Opens.grothendieckTopology V) (Opens.grothendieckTopology U) :=
  Topology.IsOpenEmbedding.functor_isContinuous (X := TopCat.of V) (Y := TopCat.of U)
    (f := (Opens.toTopCat X).map (homOfLE h)) (isOpenEmbedding_of_le h)

private def inclusionSitesCompIso (h : V ≤ U) :
    inclusionSites h ⋙ U.isOpenEmbedding.functor ≅ V.isOpenEmbedding.functor :=
  NatIso.ofComponents (fun T ↦ eqToIso (by
    apply Opens.ext
    change Subtype.val '' (Set.inclusion h '' (T : Set V)) = Subtype.val '' (T : Set V)
    rw [← Set.image_comp]
    rfl)) (by intro T T' f; exact Subsingleton.elim _ _)
private def restrictAlongInclusion (h : V ≤ U) :
    (TopCat.of U).Sheaf (ModuleCat.{u} R) ⥤ (TopCat.of V).Sheaf (ModuleCat.{u} R) :=
  (inclusionSites h).sheafPushforwardContinuous (ModuleCat.{u} R)
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology U)
private def sheafRestrictionCompositionIso (h : V ≤ U) :
    U.sheafRestrict ⋙ restrictAlongInclusion (R := R) h ≅
      V.sheafRestrict (C := ModuleCat.{u} R) := by
  exact @Functor.sheafPushforwardContinuousComp'
    (Opens V) _ (Opens U) _ (Opens X) _
    (inclusionSites h) U.isOpenEmbedding.functor V.isOpenEmbedding.functor
    (inclusionSitesCompIso h) (ModuleCat.{u} R) _
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)
    (inclusionSites_continuous h) U.isOpenEmbedding.functor_isContinuous
    V.isOpenEmbedding.functor_isContinuous


private abbrev relativeOpen (_h : V ≤ U) : Opens U := (Opens.map U.inclusion').obj V
private def relativeHomeomorph (h : V ≤ U) : relativeOpen h ≃ₜ V where
  toFun w := ⟨w.val.val, w.property⟩
  invFun v := ⟨⟨v.val, h v.property⟩, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
private def relativeTopIso (h : V ≤ U) : TopCat.of (relativeOpen h) ≅ TopCat.of V :=
  @TopCat.isoOfHomeo (TopCat.of (relativeOpen h)) (TopCat.of V) (relativeHomeomorph h)
private abbrev relativeSites (h : V ≤ U) : Opens (relativeOpen h) ≌ Opens V :=
  (Opens.mapMapIso (relativeTopIso h)).symm
private instance relativeSites_functor_cocontinuous (h : V ≤ U) :
    (relativeSites h).functor.IsCocontinuous
      (Opens.grothendieckTopology (relativeOpen h)) (Opens.grothendieckTopology V) := by
  apply ((relativeSites h).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
  exact coverPreserving_opens_map (relativeTopIso h).hom
private instance relativeSites_inverse_cocontinuous (h : V ≤ U) :
    (relativeSites h).inverse.IsCocontinuous
      (Opens.grothendieckTopology V) (Opens.grothendieckTopology (relativeOpen h)) := by
  apply ((relativeSites h).symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
  exact coverPreserving_opens_map (relativeTopIso h).inv
private instance relativeSites_inverse_dense (h : V ≤ U) :
    (relativeSites h).inverse.IsDenseSubsite
      (Opens.grothendieckTopology V) (Opens.grothendieckTopology (relativeOpen h)) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (relativeSites h)
/-- Transport sheaves from the relative open in U to the same open as a subspace of X. -/
def relativeSheafEquivalence (h : V ≤ U) :
    (TopCat.of ((Opens.map U.inclusion').obj V)).Sheaf (ModuleCat.{u} R) ≌
      (TopCat.of V).Sheaf (ModuleCat.{u} R) :=
  (relativeSites h).sheafCongr (Opens.grothendieckTopology (relativeOpen h))
    (Opens.grothendieckTopology V) (ModuleCat.{u} R)
private local instance relativeSheafEquivalence_additive (h : V ≤ U) :
    (relativeSheafEquivalence (R := R) h).functor.Additive where
  map_add := by intros; rfl


private lemma relativeSites_inverse_top (h : V ≤ U) :
    (relativeSites h).inverse.obj (⊤ : Opens V) = ⊤ := rfl
private def relativeSectionsTopIso (h : V ≤ U) :
    (sheafSections (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u} R)).obj (op ⊤) ≅
    (relativeSheafEquivalence (R := R) h).functor ⋙
      (sheafSections (Opens.grothendieckTopology V) (ModuleCat.{u} R)).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso (relativeSites_inverse_top h)).op)
    (fun f ↦ (f.hom.naturality (eqToIso (relativeSites_inverse_top h)).hom.op).symm)
/-- The canonical relative-open equivalence identifies the actual global-sections functors. -/
def relativeGammaIso (h : V ≤ U) :
    Sheaf.Γ (Opens.grothendieckTopology ((Opens.map U.inclusion').obj V)) (ModuleCat.{u} R) ≅
      (relativeSheafEquivalence (R := R) h).functor ⋙
        Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R) :=
  Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫ relativeSectionsTopIso h ≪≫
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).symm
private lemma relativeGammaIso_hom_app_ΓRes (h : V ≤ U)
    (F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)) :
    (relativeGammaIso h).hom.app F ≫
      ((relativeSheafEquivalence (R := R) h).functor.obj F).ΓRes (op ⊤) =
    F.ΓRes (op ⊤) ≫ F.obj.map (eqToIso (relativeSites_inverse_top h)).hom.op := by
  change (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F ≫
      F.obj.map (eqToIso (relativeSites_inverse_top h)).hom.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).inv.app
        ((relativeSheafEquivalence (R := R) h).functor.obj F) ≫
      ((relativeSheafEquivalence (R := R) h).functor.obj F).ΓRes (op ⊤) = _
  rw [← CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes _ _ isTerminalTop]
  erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes]
  rfl
local instance gamma_module_additive {Y : Type u} [TopologicalSpace Y] :
    (Sheaf.Γ (Opens.grothendieckTopology Y) (ModuleCat.{u} R)).Additive := by
  let := (constantSheafΓAdj (Opens.grothendieckTopology Y) (ModuleCat.{u} R)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _
/-- Transport derived global sections along the canonical relative-open equivalence. -/
def relativeDerivedGammaIso (h : V ≤ U) (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology ((Opens.map U.inclusion').obj V)) (ModuleCat.{u}
      R)).rightDerived n ≅
    (relativeSheafEquivalence (R := R) h).functor ⋙
      (Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).rightDerived n := by
  exact (Functor.rightUnitor _).symm ≪≫
    Functor.rightDerivedCompIso _ (𝟭 (ModuleCat.{u} R))
      (relativeSheafEquivalence (R := R) h).functor _
      (Functor.rightUnitor _ ≪≫ relativeGammaIso h) n

private def transportedInjectiveResolution (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    InjectiveResolution ((relativeSheafEquivalence (R := R) h).functor.obj F) :=
  (relativeSheafEquivalence (R := R) h).functor.mapInjectiveResolution I
private def relativeGammaComplexMap (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    ((Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶
    ((Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj (transportedInjectiveResolution h I).cocomplex := by
  let T := (relativeSheafEquivalence (R := R) h).functor
  exact (NatTrans.mapHomologicalComplex (relativeGammaIso h).hom _).app I.cocomplex ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (T ⋙ Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R))) _).inv.app
        I.cocomplex
private lemma relativeGammaComplexMap_f (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (j : ℕ) :
    (relativeGammaComplexMap h I).f j = (relativeGammaIso h).hom.app (I.cocomplex.X j) :=
  Category.comp_id _

private lemma relativeDerivedGammaIso_app (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (n : ℕ) :
    (relativeDerivedGammaIso h n).hom.app F ≫
      ((transportedInjectiveResolution h I).isoRightDerivedObj
        (Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)) n).hom =
    (I.isoRightDerivedObj
      (Sheaf.Γ (Opens.grothendieckTopology (relativeOpen h)) (ModuleCat.{u} R)) n).hom ≫
      HomologicalComplex.homologyMap (relativeGammaComplexMap h I) n := by
  let := relativeSheafEquivalence_additive (R := R) h
  dsimp only [relativeOpen, relativeDerivedGammaIso, relativeGammaComplexMap,
    transportedInjectiveResolution]
  convert Functor.rightDerivedPrecompIso_app_hom _ _ _ (relativeGammaIso h) I n using 1
  rfl

private abbrev relativeInclusionSites (h : V ≤ U) : Opens (relativeOpen h) ⥤ Opens U :=
  @Topology.IsOpenEmbedding.functor (TopCat.of (relativeOpen h)) (TopCat.of U)
    (Opens.inclusion' (X := TopCat.of U) (relativeOpen h))
    (Opens.isOpenEmbedding (X := TopCat.of U) (relativeOpen h))
private def relativeRestrictionSitesIso (h : V ≤ U) :
    Opens.map (relativeTopIso h).hom ⋙ (relativeInclusionSites h) ≅
      inclusionSites h :=
  NatIso.ofComponents (fun D ↦ eqToIso (by
    apply Opens.ext
    change Subtype.val '' ((relativeTopIso h).hom ⁻¹' (D : Set V)) = Set.inclusion h '' (D : Set V)
    have hf : (Subtype.val : relativeOpen h → U) = Set.inclusion h ∘ (relativeTopIso h).hom := rfl
    rw [hf, Set.image_comp]
    exact congrArg (Set.inclusion h '' ·)
      (Set.image_preimage_eq _ (relativeHomeomorph h).surjective)))
    (by intro D D' f; exact Subsingleton.elim _ _)
private def relativeRestrictionIso (h : V ≤ U) :
    (relativeOpen h).sheafRestrict ⋙ (relativeSheafEquivalence (R := R) h).functor ≅
      restrictAlongInclusion (R := R) h := by
  exact @Functor.sheafPushforwardContinuousComp'
    (Opens V) _ (Opens (relativeOpen h)) _ (Opens U) _
    (Opens.map (relativeTopIso h).hom) (relativeInclusionSites h)
    (inclusionSites h) (relativeRestrictionSitesIso h) (ModuleCat.{u} R) _
    (Opens.grothendieckTopology V) (Opens.grothendieckTopology (relativeOpen h))
    (Opens.grothendieckTopology U)
    (by
      apply Functor.isContinuous_of_coverPreserving
      · exact compatiblePreserving_opens_map (relativeTopIso h).hom
      · exact coverPreserving_opens_map (relativeTopIso h).hom)
    (@Topology.IsOpenEmbedding.functor_isContinuous (TopCat.of (relativeOpen h)) (TopCat.of U)
      (Opens.inclusion' (X := TopCat.of U) (relativeOpen h))
      (Opens.isOpenEmbedding (X := TopCat.of U) (relativeOpen h)))
    (inclusionSites_continuous h)
/-- The coefficient isomorphism comparing actual nested restriction with direct restriction. -/
def actualNestedRestrictionIso (h : V ≤ U) :
    U.sheafRestrict ⋙ ((Opens.map U.inclusion').obj V).sheafRestrict ⋙
      (relativeSheafEquivalence (R := R) h).functor ≅ V.sheafRestrict (C := ModuleCat.{u} R) :=
  Functor.isoWhiskerLeft U.sheafRestrict (relativeRestrictionIso h) ≪≫
    sheafRestrictionCompositionIso h

private abbrev nestedResolution (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)} (I :
  InjectiveResolution F) :=
  transportedInjectiveResolution h
    ((((relativeOpen h).sheafRestrict (X := TopCat.of U) (C
      := ModuleCat.{u} R)).mapInjectiveResolution
      ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)))
private def nestedCoefficientComplexMap (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) : (nestedResolution h I).cocomplex ⟶
    (((V.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)).cocomplex := by
  letI := Functor.preservesZeroMorphisms_of_iso (actualNestedRestrictionIso (R := R) h).symm
  dsimp only [nestedResolution, transportedInjectiveResolution, Functor.mapInjectiveResolution]
  exact (NatTrans.mapHomologicalComplex
    (actualNestedRestrictionIso (R := R) h).hom (.up ℕ)).app I.cocomplex

private lemma nestedCoefficientComplexMap_f (h : V ≤ U) {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) :
    (nestedCoefficientComplexMap h I).f j = (actualNestedRestrictionIso h).hom.app (I.cocomplex.X
      j) := by
  rfl

@[reassoc]
private lemma relativeGammaComplexMap_allProjections (h : V ≤ U)
    {F : (TopCat.of (relativeOpen h)).Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (j : ℕ) (D : Opens V) :
    (relativeGammaComplexMap h I).f j ≫
        ((transportedInjectiveResolution h I).cocomplex.X j).ΓRes (op D) =
      (I.cocomplex.X j).ΓRes (op ((relativeSites h).inverse.obj D)) := by
  let F := I.cocomplex.X j
  erw [relativeGammaComplexMap_f,
    ← Sheaf.ΓRes_map _ (homOfLE (show D ≤ ⊤ from le_top)).op,
    ← Category.assoc, relativeGammaIso_hom_app_ΓRes]
  change F.ΓRes (op ⊤) ≫ F.obj.map _ ≫ F.obj.map _ = _
  rw [← F.obj.map_comp]
  exact Sheaf.ΓRes_map F _

private def totalNestedSitesIso (h : V ≤ U) :
    (relativeSites h).inverse ⋙ relativeInclusionSites h ⋙ U.isOpenEmbedding.functor ≅
      V.isOpenEmbedding.functor :=
  Functor.isoWhiskerRight (relativeRestrictionSitesIso h) U.isOpenEmbedding.functor ≪≫
    inclusionSitesCompIso h
private lemma actualNestedRestrictionIso_component (h : V ≤ U)
    (F : X.Sheaf (ModuleCat.{u} R)) (D : Opens V) :
    ((actualNestedRestrictionIso h).hom.app F).hom.app (op D) =
      F.obj.map ((totalNestedSitesIso h).inv.app D).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  erw [← CategoryTheory.Functor.map_comp]
  congr 1

private lemma nestedComplexComposition_allProjections (h : V ≤ U)
    {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) (j : ℕ) (D : Opens V) :
    (rightDerivedΓRestrictionComplexMap U I).f j ≫
      (rightDerivedΓRestrictionComplexMap (X := TopCat.of U) (relativeOpen h)
        ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I)).f j ≫
      (relativeGammaComplexMap h
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
  have hH := relativeGammaComplexMap_allProjections h IW j D
  have hW := rightDerivedΓRestrictionComplexMap_allProjections
    (X := TopCat.of U) (relativeOpen h) IU j ((relativeSites h).inverse.obj D)
  have hU := rightDerivedΓRestrictionComplexMap_allProjections U I j
    ((relativeInclusionSites h).obj ((relativeSites h).inverse.obj D))
  erw [Sheaf.ΓRes_naturality, reassoc_of% hH, reassoc_of% hW, reassoc_of% hU]
  erw [nestedCoefficientComplexMap_f, actualNestedRestrictionIso_component]
  exact Sheaf.ΓRes_map _ _

private lemma nestedComplexComposition (h : V ≤ U)
    {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    rightDerivedΓRestrictionComplexMap U I ≫
      rightDerivedΓRestrictionComplexMap (X := TopCat.of U) (relativeOpen h)
        ((U.sheafRestrict (C := ModuleCat.{u} R)).mapInjectiveResolution I) ≫
      relativeGammaComplexMap h
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
  rw [nestedComplexComposition_allProjections, rightDerivedΓRestrictionComplexMap_allProjections]

/-- Direct derived restriction equals restriction through the actual nested open subspace. -/
theorem rightDerivedΓRestriction_nested (h : V ≤ U) (F : X.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
  (rightDerivedΓRestriction (R := R) V n).app F =
    (rightDerivedΓRestriction (R := R) U n).app F ≫
    (rightDerivedΓRestriction (X := TopCat.of U) (R := R) ((Opens.map U.inclusion').obj V) n).app
      (U.sheafRestrict.obj F) ≫
    (relativeDerivedGammaIso h n).hom.app (((Opens.map U.inclusion').obj V).sheafRestrict.obj
      (U.sheafRestrict.obj F)) ≫
    ((Sheaf.Γ (Opens.grothendieckTopology V) (ModuleCat.{u} R)).rightDerived n).map
      ((actualNestedRestrictionIso h).hom.app F) := by
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
  have hA := InjectiveResolution.isoRightDerivedObj_hom_naturality
    ((actualNestedRestrictionIso h).hom.app F) IT IV (nestedCoefficientComplexMap h I)
    (by
      rw [nestedCoefficientComplexMap_f]
      change (U.sheafRestrict ⋙ ((Opens.map U.inclusion').obj V).sheafRestrict ⋙
        (relativeSheafEquivalence (R := R) h).functor).map (I.ι.f 0) ≫
          (actualNestedRestrictionIso h).hom.app (I.cocomplex.X 0) =
        (actualNestedRestrictionIso h).hom.app F ≫ V.sheafRestrict.map (I.ι.f 0)
      exact (actualNestedRestrictionIso h).hom.naturality (I.ι.f 0)) ΓV n
  change _ = _ ≫ HomologicalComplex.homologyMap ((ΓV.mapHomologicalComplex _).map _) n at hA
  have hH := relativeDerivedGammaIso_app h IW n
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
