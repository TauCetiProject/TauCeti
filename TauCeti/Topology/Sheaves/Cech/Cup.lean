/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Colimit
public import TauCeti.Topology.Sheaves.Cech.Functoriality
public import TauCeti.Topology.Sheaves.LocallyConstant.Module

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Cup product and graded algebra structure on topological Čech cohomology

This file specializes the directed-colimit Čech cup product
(`TauCeti.CategoryTheory.cechCohomologyCup`) to Čech cohomology of presheaves of `R`-modules on a
topological space (`TauCeti.Topology.cechCohomology`), proves its compatibility with pullbacks
along continuous maps (`TopCat.Hom.cechCohomologyPullback`) and open restrictions, and equips the
constant-coefficient Čech cohomology `⨁ n, Ȟⁿ(X; S)` with a graded `R`-algebra structure
(`DirectSum.GRing`, `DirectSum.GAlgebra`) for any `R`-algebra `S`.

## Main definitions

* `TauCeti.Topology.cechCohomologyCup`: the cup product on topological Čech cohomology for any
  natural `R`-bilinear pairing of presheaves of `R`-modules.
* `TauCeti.Topology.cechCohomologyConst X R M n`: the degree `n` Čech cohomology of `X` with
  constant coefficients in an `R`-module `M`, via `TopCat.locallyConstantModulePresheaf`.
* `TauCeti.Topology.cechCohomologyConstOne`, `TauCeti.Topology.cechCohomologyConstCup`: the
  degree-`0` unit and cup product on constant-coefficient Čech cohomology for an `R`-algebra `S`.
* `DirectSum.GRing (TauCeti.Topology.cechCohomologyConst X R S)` and
  `DirectSum.GAlgebra R (TauCeti.Topology.cechCohomologyConst X R S)`: the graded `R`-algebra
  structure on `⨁ n, Ȟⁿ(X; S)`.
* `TauCeti.Topology.cechCohomologyConstZeroAlgHom`: the canonical `R`-algebra homomorphism
  embedding `LocallyConstant X S` as the degree-`0` summand of `⨁ n, Ȟⁿ(X; S)`.
* `TopCat.Hom.cechCohomologyAlgebraPullback`: pullback along a continuous map `f : X ⟶ Y` as a
  graded `R`-algebra homomorphism `(⨁ n, Ȟⁿ(Y; S)) →ₐ[R] (⨁ n, Ȟⁿ(X; S))`.

## Main results

* `TauCeti.Topology.cechCohomologyCup_toCechCohomology`: compatibility of the topological cup
  product with the canonical map `toCechCohomology` from every small open cover.
* `TopCat.Hom.cechCohomologyPullback_cechCohomologyCup`: pullback along a continuous map commutes
  with the Čech cup product.
* `TopologicalSpace.Opens.cechCohomologyRestrict_cechCohomologyCup`: open restriction commutes
  with the Čech cup product.
* `TauCeti.Topology.cechCohomologyConst_of_mul_of_comm`,
  `TauCeti.Topology.two_smul_cechCohomologyConst_of_mul_self_of_odd`,
  `TauCeti.Topology.cechCohomologyConst_of_mul_self_of_odd`: graded commutativity and odd-degree
  square vanishing in `⨁ n, Ȟⁿ(X; S)` when `S` is commutative.
* `TopCat.Hom.cechCohomologyAlgebraPullback_id`,
  `TopCat.Hom.cechCohomologyAlgebraPullback_comp`: functoriality of the pullback algebra
  homomorphism.
* `TauCeti.Topology.cechCupCochain_bool_front_back`: explicit front-face / back-face cochain
  calculation on the two-point discrete space `TopCat.of Bool`, exhibiting noncommutativity at the
  cochain level.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY) and §20.31 (tag 01FP).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.CategoryTheory
open TauCeti.Topology (PointOpenCover)
open scoped DirectSum

universe u uR u' v w

/-! ### Topological Čech cup product -/

namespace TauCeti.Topology

section General

variable {X : TopCat.{u}} {R : Type uR} [CommRing R]
  [HasProducts.{u} (ModuleCat.{u'} R)]
  [HasColimitsOfShape (PointOpenCover X) (ModuleCat.{u'} R)]
  {P Q S : X.Presheaf (ModuleCat.{u'} R)}

/-- The Čech cup product on topological Čech cohomology `Ȟᵖ(X, P) × Ȟ^q(X, Q) ⟶ Ȟⁿ(X, S)` for a
natural `R`-bilinear pairing `μ` and `p + q = n`. -/
abbrev cechCohomologyCup
    (μ : ∀ V : (Opens X)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : (Opens X)ᵒᵖ⦄ (f : V ⟶ W) x y,
      S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (p q n : ℕ) (h : p + q = n) :
    (cechCohomology X (ModuleCat.{u'} R) p).obj P →ₗ[R]
      (cechCohomology X (ModuleCat.{u'} R) q).obj Q →ₗ[R]
        (cechCohomology X (ModuleCat.{u'} R) n).obj S :=
  TauCeti.CategoryTheory.cechCohomologyCup PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    μ hμ p q n h

/-- On classes coming from any `u`-small open cover `U` of `X`, the topological Čech cup product
agrees with the fixed-cover cup product `cechCup` along `toCechCohomology`. -/
@[simp]
theorem cechCohomologyCup_toCechCohomology
    (μ : ∀ V : (Opens X)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : (Opens X)ᵒᵖ⦄ (f : V ⟶ W) x y,
      S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    dsimp% only [Functor.comp_obj]
      (cechCohomologyCup μ hμ p q n h
          ((toCechCohomology (ModuleCat.{u'} R) p U hU).app P x)
          ((toCechCohomology (ModuleCat.{u'} R) q U hU).app Q y) =
        (toCechCohomology (ModuleCat.{u'} R) n U hU).app S (cechCup U μ hμ p q n h x y)) := by
  obtain ⟨V, ⟨φ⟩⟩ := PointOpenCover.exists_refinement U hU
  have hcomp {K : X.Presheaf (ModuleCat.{u'} R)} (m : ℕ)
      (z : ((cechComplexFunctor U).obj K).homology m) :
      (toCechCohomology (ModuleCat.{u'} R) m U hU).app K z =
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) m V).app K
          (HomologicalComplex.homologyMap (cechComplexMap K φ) m z) := by
    have hEq := NatTrans.congr_app (toCechCohomology_eq (ModuleCat.{u'} R) m U hU V φ) K
    have hEq' : (toCechCohomology (ModuleCat.{u'} R) m U hU).app K =
        (cechComplexHomologyMap (ModuleCat.{u'} R) m φ).app K ≫
          (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) m V).app K := hEq
    rw [cechComplexHomologyMap_app] at hEq'
    exact ConcreteCategory.congr_hom hEq' z
  rw [hcomp p x, hcomp q y, hcomp n _, cechCohomologyCup, cechCohomologyCup_cechCohomologyι,
    cechCup_cechComplexHomologyMap]

/-- **Degree-`0` compatibility with `cechCohomologyZeroIso`**: for sheaves `F`, `G`, `H` of
`R`-modules on `X`, the degree-`0` Čech cup product agrees with the pairing on global sections. -/
theorem cechCohomologyCup_zero_zero_cechCohomologyZeroIso
    (F G H : X.Sheaf (ModuleCat.{u'} R))
    (μ : ∀ V : (Opens X)ᵒᵖ, F.obj.obj V →ₗ[R] G.obj.obj V →ₗ[R] H.obj.obj V)
    (hμ : ∀ ⦃V W : (Opens X)ᵒᵖ⦄ (f : V ⟶ W) x y,
      H.obj.map f (μ V x y) = μ W (F.obj.map f x) (G.obj.map f y))
    (s : F.obj.obj (op ⊤)) (t : G.obj.obj (op ⊤)) :
    cechCohomologyCup μ hμ 0 0 0 rfl
        ((cechCohomologyZeroIso F).hom s) ((cechCohomologyZeroIso G).hom t) =
      (cechCohomologyZeroIso H).hom (μ (op ⊤) s t) := by
  let U : PointOpenCover X := default
  have hcomp (K : X.Sheaf (ModuleCat.{u'} R)) (z : K.obj.obj (op ⊤)) :
      (cechCohomologyZeroIso K).hom z =
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 U).app K.obj
          (HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop K.obj) 0
            ((HomologicalComplex.singleObjHomologySelfIso _ 0 (K.obj.obj (op ⊤))).inv z)) :=
    congrArg (·.hom z) (cechCohomologyZeroIso_hom K U)
  rw [hcomp F s, hcomp G t, hcomp H (μ (op ⊤) s t), cechCohomologyCup,
    cechCohomologyCup_cechCohomologyι, cechCup_zero_zero_augmentation]

end General

end TauCeti.Topology

/-! ### Functoriality and pullback compatibility of the Čech cup product -/

namespace TopCat.Hom

section Functoriality

variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]

/-- Pullback of a Čech complex along the identity continuous map and identity coefficient morphism
is the identity. -/
@[simp]
theorem cechComplexPullback_id {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
    (P : X.Presheaf A) :
    cechComplexPullback (𝟙 X) U (𝟙 P) = 𝟙 ((cechComplexFunctor U).obj P) := by
  ext n : 2
  refine Limits.Pi.hom_ext _ _ fun (a : Fin (n + 1) → ι) ↦ ?_
  have hπ := cechComplexPullback_f_π (𝟙 X) U (𝟙 P) n a
  have hmap : P.map (inv (piComparison (Opens.map (𝟙 X)) (fun j ↦ U (a j)))).op = 𝟙 _ :=
    (congrArg (fun φ : (∏ᶜ fun j ↦ U (a j)) ⟶ (∏ᶜ fun j ↦ U (a j)) ↦ P.map φ.op)
      (Subsingleton.elim _ (𝟙 _))).trans (P.map_id _)
  have hid : (𝟙 P : P ⟶ (TopCat.Presheaf.pushforward A (𝟙 X)).obj P).app
      (op (∏ᶜ fun j ↦ U (a j))) = 𝟙 _ := rfl
  exact hπ.trans <|
    (Pi.π _ a ≫= ((hid =≫ _) |>.trans <| (Category.id_comp _).trans hmap)).trans <|
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- Pullback of a Čech complex is contravariantly functorial in the continuous map and
compatible coefficient morphisms. -/
theorem cechComplexPullback_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {ι : Type u}
    (U : ι → Opens Z) {P : Z.Presheaf A} {Q : Y.Presheaf A} {S : X.Presheaf A}
    (β : P ⟶ (TopCat.Presheaf.pushforward A g).obj Q)
    (α : Q ⟶ (TopCat.Presheaf.pushforward A f).obj S) :
    cechComplexPullback (f ≫ g) U (β ≫ (TopCat.Presheaf.pushforward A g).map α) =
      cechComplexPullback g U β ≫
        cechComplexPullback f (fun i ↦ (Opens.map g).obj (U i)) α := by
  ext n : 2
  refine Limits.Pi.hom_ext _ _ fun (a : Fin (n + 1) → ι) ↦ ?_
  have hL := cechComplexPullback_f_π (f ≫ g) U (β ≫ (TopCat.Presheaf.pushforward A g).map α) n a
  have hR1 := cechComplexPullback_f_π f (fun i ↦ (Opens.map g).obj (U i)) α n a
  have hR2 := cechComplexPullback_f_π g U β n a
  have hR : ((cechComplexPullback g U β ≫
      cechComplexPullback f (fun i ↦ (Opens.map g).obj (U i)) α).f n) ≫ Pi.π _ a =
      Pi.π _ a ≫ β.app _ ≫ Q.map (inv (piComparison (Opens.map g) (fun j ↦ U (a j)))).op ≫
        α.app _ ≫ S.map (inv (piComparison (Opens.map f)
          (fun j ↦ (Opens.map g).obj (U (a j))))).op :=
    (Category.assoc _ _ _).trans <|
      (((cechComplexPullback g U β).f n) ≫= hR1).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (hR2 =≫ _).trans <|
      (Category.assoc _ _ _).trans <|
      (Pi.π _ a ≫= (Category.assoc _ _ _))
  let u₁ : (∏ᶜ fun j ↦ (Opens.map f).obj ((Opens.map g).obj (U (a j)))) ⟶
      (Opens.map f).obj (∏ᶜ fun j ↦ (Opens.map g).obj (U (a j))) :=
    inv (piComparison (Opens.map f) (fun j ↦ (Opens.map g).obj (U (a j))))
  let u₂ : (Opens.map f).obj (∏ᶜ fun j ↦ (Opens.map g).obj (U (a j))) ⟶
      (Opens.map f).obj ((Opens.map g).obj (∏ᶜ fun j ↦ U (a j))) :=
    (Opens.map f).map (inv (piComparison (Opens.map g) (fun j ↦ U (a j))))
  have hnat1 := α.naturality (inv (piComparison (Opens.map g) (fun j ↦ U (a j)))).op
  have hnat2 : S.map u₂.op ≫ S.map u₁.op =
      S.map (inv (piComparison (Opens.map (f ≫ g)) (fun j ↦ U (a j)))).op :=
    (S.map_comp u₂.op u₁.op).symm.trans <|
      congrArg (fun φ : (∏ᶜ fun j ↦ (Opens.map f).obj ((Opens.map g).obj (U (a j)))) ⟶
        (Opens.map f).obj ((Opens.map g).obj (∏ᶜ fun j ↦ U (a j))) ↦ S.map φ.op)
        (Subsingleton.elim (u₁ ≫ u₂) _)
  have hnat : Q.map (inv (piComparison (Opens.map g) (fun j ↦ U (a j)))).op ≫
      α.app (op (∏ᶜ fun j ↦ (Opens.map g).obj (U (a j)))) ≫ S.map u₁.op =
      α.app (op ((Opens.map g).obj (∏ᶜ fun j ↦ U (a j)))) ≫
        S.map (inv (piComparison (Opens.map (f ≫ g)) (fun j ↦ U (a j)))).op :=
    (Category.assoc _ _ _).symm.trans <| (hnat1 =≫ _).trans <|
      (Category.assoc _ _ _).trans (α.app _ ≫= hnat2)
  exact hL.trans <|
    (Pi.π _ a ≫= ((Category.assoc _ _ _).trans (β.app _ ≫= hnat.symm))).trans hR.symm

variable [CategoryWithHomology A]

/-- Pullback on Čech cohomology along the identity continuous map and identity coefficient morphism
is the identity. -/
@[simp]
theorem cechCohomologyPullback_id {X : TopCat.{u}} [HasColimitsOfShape (PointOpenCover X) A]
    (n : ℕ) (P : X.Presheaf A) :
    cechCohomologyPullback (𝟙 X) n (𝟙 P) = 𝟙 ((TauCeti.Topology.cechCohomology X A n).obj P) := by
  refine cechCohomology_obj_hom_ext fun U ↦ ?_
  have hto : (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n U).app P =
      (TauCeti.Topology.toCechCohomology A n U.opens U.isOpenCover).app P :=
    NatTrans.congr_app (TauCeti.Topology.toCechCohomology_opens A n U).symm P
  have h := toCechCohomology_app_comp_cechCohomologyPullback (𝟙 X) n (𝟙 P) U.opens U.isOpenCover
  have hid : HomologicalComplex.homologyMap (cechComplexPullback (𝟙 X) U.opens (𝟙 P)) n = 𝟙 _ :=
    (congrArg (HomologicalComplex.homologyMap · n) (cechComplexPullback_id U.opens P)).trans
      (HomologicalComplex.homologyMap_id _ n)
  exact (hto =≫ _).trans <| h.trans <| (hid =≫ _).trans <|
    (Category.id_comp _).trans <| hto.symm.trans (Category.comp_id _).symm

/-- Pullback on Čech cohomology is contravariantly functorial in the continuous map and
compatible coefficient morphisms. -/
theorem cechCohomologyPullback_comp {X Y Z : TopCat.{u}}
    [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]
    [HasColimitsOfShape (PointOpenCover Z) A]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    {P : Z.Presheaf A} {Q : Y.Presheaf A} {S : X.Presheaf A}
    (β : P ⟶ (TopCat.Presheaf.pushforward A g).obj Q)
    (α : Q ⟶ (TopCat.Presheaf.pushforward A f).obj S) :
    cechCohomologyPullback (f ≫ g) n (β ≫ (TopCat.Presheaf.pushforward A g).map α) =
      cechCohomologyPullback g n β ≫ cechCohomologyPullback f n α := by
  refine cechCohomology_obj_hom_ext fun U ↦ ?_
  have hto : (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n U).app P =
      (TauCeti.Topology.toCechCohomology A n U.opens U.isOpenCover).app P :=
    NatTrans.congr_app (TauCeti.Topology.toCechCohomology_opens A n U).symm P
  have h₁ := toCechCohomology_app_comp_cechCohomologyPullback (f ≫ g) n
    (β ≫ (TopCat.Presheaf.pushforward A g).map α) U.opens U.isOpenCover
  have h₂ := toCechCohomology_app_comp_cechCohomologyPullback g n β U.opens U.isOpenCover
  have h₃ := toCechCohomology_app_comp_cechCohomologyPullback f n α
    (fun i ↦ (Opens.map g).obj (U.opens i)) (U.isOpenCover.comap g.hom)
  have hcomp : HomologicalComplex.homologyMap
      (cechComplexPullback (f ≫ g) U.opens (β ≫ (TopCat.Presheaf.pushforward A g).map α)) n =
      HomologicalComplex.homologyMap (cechComplexPullback g U.opens β) n ≫
        HomologicalComplex.homologyMap
          (cechComplexPullback f (fun i ↦ (Opens.map g).obj (U.opens i)) α) n :=
    (congrArg (HomologicalComplex.homologyMap · n)
      (cechComplexPullback_comp f g U.opens β α)).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  exact (hto =≫ _).trans <| h₁.trans <| (hcomp =≫ _).trans <| (Category.assoc _ _ _).trans <|
    (HomologicalComplex.homologyMap (cechComplexPullback g U.opens β) n ≫= h₃.symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (h₂.symm =≫ _).trans <|
    (Category.assoc _ _ _).trans (hto.symm =≫ _)

private lemma cechAugmentation_homologyMap_comp_pullback {X Y : TopCat.{u}}
    [HasZeroObject A] (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)
    {P : Y.Presheaf A} {Q : X.Presheaf A}
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) :
    HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop P) 0 ≫
        HomologicalComplex.homologyMap (cechComplexPullback f U α) 0 =
      HomologicalComplex.homologyMap
          ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map
            (α.app (op ⊤) : P.obj (op ⊤) ⟶ Q.obj (op ⊤))) 0 ≫
        HomologicalComplex.homologyMap
          (cechAugmentation (fun i ↦ (Opens.map f).obj (U i)) isTerminalTop Q) 0 :=
  (HomologicalComplex.homologyMap_comp _ _ 0).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · 0)
      (cechAugmentation_comp_cechComplexPullback f U α)).trans
    (HomologicalComplex.homologyMap_comp
      ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map
        (α.app (op ⊤) : P.obj (op ⊤) ⟶ Q.obj (op ⊤)))
      (cechAugmentation (fun i ↦ (Opens.map f).obj (U i)) isTerminalTop Q) 0)

private lemma cechAugmentation_homologyMap_comp_toCechCohomology {X Y : TopCat.{u}}
    [HasZeroObject A] [HasColimitsOfShape (PointOpenCover X) A]
    (f : X ⟶ Y) (U : PointOpenCover Y) (G : X.Sheaf A) :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (G.obj.obj (op ⊤))).inv ≫
        HomologicalComplex.homologyMap
          (cechAugmentation (fun i ↦ (Opens.map f).obj (U.opens i)) isTerminalTop G.obj) 0 ≫
        (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
          (U.isOpenCover.comap f.hom)).app G.obj =
      (TauCeti.Topology.cechCohomologyZeroIso G).hom := by
  let V : PointOpenCover X := ⟨fun x ↦ (Opens.map f).obj (U.opens (f x)), fun x ↦ U.mem_opens (f x)⟩
  let φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk Y (fun i ↦ (Opens.map f).obj (U.opens i)) :=
    ⟨f, fun _ ↦ 𝟙 _⟩
  have hto : (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
        (U.isOpenCover.comap f.hom)).app G.obj =
      HomologicalComplex.homologyMap (cechComplexMap G.obj φ) 0 ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 V).app G.obj := by
    have h' : (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
        (U.isOpenCover.comap f.hom)).app G.obj =
        (cechComplexHomologyMap A 0 φ).app G.obj ≫
          (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 V).app G.obj :=
      NatTrans.congr_app
        (TauCeti.Topology.toCechCohomology_eq A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
          (U.isOpenCover.comap f.hom) V φ) G.obj
    rwa [cechComplexHomologyMap_app] at h'
  have hmap : HomologicalComplex.homologyMap
        (cechAugmentation (fun i ↦ (Opens.map f).obj (U.opens i)) isTerminalTop G.obj) 0 ≫
      HomologicalComplex.homologyMap (cechComplexMap G.obj φ) 0 =
      HomologicalComplex.homologyMap (cechAugmentation V.opens isTerminalTop G.obj) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, cechAugmentation_comp_cechComplexMap]
  refine (_ ≫= ((_ ≫= hto).trans <| (Category.assoc _ _ _).symm.trans (hmap =≫ _))).trans ?_
  exact (TauCeti.Topology.cechCohomologyZeroIso_hom G V).symm

/-- Pullback on degree-`0` Čech cohomology agrees with the global-sections map under
`TauCeti.Topology.cechCohomologyZeroIso`. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyPullback {X Y : TopCat.{u}}
    [HasZeroObject A] [HasColimitsOfShape (PointOpenCover X) A]
    [HasColimitsOfShape (PointOpenCover Y) A]
    (f : X ⟶ Y) (F : Y.Sheaf A) (G : X.Sheaf A)
    (α : F.obj ⟶ (TopCat.Presheaf.pushforward A f).obj G.obj) :
    (TauCeti.Topology.cechCohomologyZeroIso F).hom ≫ cechCohomologyPullback f 0 α =
      α.app (op ⊤) ≫ (TauCeti.Topology.cechCohomologyZeroIso G).hom := by
  let U : PointOpenCover Y := default
  have hU : (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 U).app F.obj ≫
      cechCohomologyPullback f 0 α =
      HomologicalComplex.homologyMap (cechComplexPullback f U.opens α) 0 ≫
        (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
          (U.isOpenCover.comap f.hom)).app G.obj := by
    have h := toCechCohomology_app_comp_cechCohomologyPullback f 0 α U.opens U.isOpenCover
    rw [TauCeti.Topology.toCechCohomology_opens] at h
    exact h
  have hsingle : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        (F.obj.obj (op ⊤))).inv ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map
          (α.app (op ⊤) : F.obj.obj (op ⊤) ⟶ G.obj.obj (op ⊤))) 0 =
      (α.app (op ⊤) : F.obj.obj (op ⊤) ⟶ G.obj.obj (op ⊤)) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          (G.obj.obj (op ⊤))).inv :=
    HomologicalComplex.singleObjHomologySelfIso_inv_naturality _ _ _
  calc
    (TauCeti.Topology.cechCohomologyZeroIso F).hom ≫ cechCohomologyPullback f 0 α
      = (HomologicalComplex.singleObjHomologySelfIso _ 0 (F.obj.obj (op ⊤))).inv ≫
          (HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop F.obj) 0 ≫
            HomologicalComplex.homologyMap (cechComplexPullback f U.opens α) 0) ≫
          (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
            (U.isOpenCover.comap f.hom)).app G.obj :=
        (TauCeti.Topology.cechCohomologyZeroIso_hom F U =≫ _).trans <|
          (Category.assoc _ _ _).trans <|
          (_ ≫= ((Category.assoc _ _ _).trans <| (_ ≫= hU).trans (Category.assoc _ _ _).symm))
    _ = ((HomologicalComplex.singleObjHomologySelfIso _ 0 (F.obj.obj (op ⊤))).inv ≫
          HomologicalComplex.homologyMap
            ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map
              (α.app (op ⊤) : F.obj.obj (op ⊤) ⟶ G.obj.obj (op ⊤))) 0) ≫
          HomologicalComplex.homologyMap
            (cechAugmentation (fun i ↦ (Opens.map f).obj (U.opens i)) isTerminalTop G.obj) 0 ≫
          (TauCeti.Topology.toCechCohomology A 0 (fun i ↦ (Opens.map f).obj (U.opens i))
            (U.isOpenCover.comap f.hom)).app G.obj :=
        (_ ≫= (cechAugmentation_homologyMap_comp_pullback f U.opens α =≫ _)).trans <|
          (_ ≫= Category.assoc _ _ _).trans (Category.assoc _ _ _).symm
    _ = α.app (op ⊤) ≫ (TauCeti.Topology.cechCohomologyZeroIso G).hom :=
        (hsingle =≫ _).trans <| (Category.assoc _ _ _).trans <|
          _ ≫= cechAugmentation_homologyMap_comp_toCechCohomology f U G

end Functoriality

section CupCompatibility

variable {R : Type uR} [CommRing R] [HasProducts.{u} (ModuleCat.{u'} R)]
  {X Y : TopCat.{u}} (f : X ⟶ Y)
  {P Q S : Y.Presheaf (ModuleCat.{u'} R)} {P' Q' S' : X.Presheaf (ModuleCat.{u'} R)}
  (μY : ∀ V : (Opens Y)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
  (hμY : ∀ ⦃V W : (Opens Y)ᵒᵖ⦄ (g : V ⟶ W) x y,
    S.map g (μY V x y) = μY W (P.map g x) (Q.map g y))
  (μX : ∀ V : (Opens X)ᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
  (hμX : ∀ ⦃V W : (Opens X)ᵒᵖ⦄ (g : V ⟶ W) x y,
    S'.map g (μX V x y) = μX W (P'.map g x) (Q'.map g y))
  (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u'} R) f).obj P')
  (β : Q ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u'} R) f).obj Q')
  (γ : S ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u'} R) f).obj S')
  (hγ : ∀ (V : (Opens Y)ᵒᵖ) (x : P.obj V) (y : Q.obj V),
    γ.app V (μY V x y) = μX (op ((Opens.map f).obj V.unop)) (α.app V x) (β.app V y))

private lemma cechComplexPullback_comp_compIso {A : Type v} [Category.{w} A] [Preadditive A]
    [HasProducts.{u} A] {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)
    {K : Y.Presheaf A} {K' : X.Presheaf A}
    (η : K ⟶ (TopCat.Presheaf.pushforward A f).obj K') :
    cechComplexPullback f U η ≫
        (cechComplexCompIso (Opens.map f) U K' (fun _ _ ↦ inferInstance)).hom =
      (cechComplexFunctor U).map η := by
  ext n : 2
  refine Limits.Pi.hom_ext _ _ fun a ↦ ?_
  have h1 := cechComplexCompIso_hom_f_π (Opens.map f) U K' (fun _ _ ↦ inferInstance) n a
  have h2 := cechComplexPullback_f_π f U η n a
  have h3 := cechComplexFunctor_map_f_π U K η n a
  have hinv : K'.map (inv (piComparison (Opens.map f) (fun j ↦ U (a j)))).op ≫
      K'.map (piComparison (Opens.map f) (fun j ↦ U (a j))).op = 𝟙 _ := by
    rw [← K'.map_comp, ← op_comp, IsIso.hom_inv_id, op_id, K'.map_id]
  exact (Category.assoc _ _ _).trans <|
    (((cechComplexPullback f U η).f n) ≫= h1).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (h2 =≫ _).trans <|
    (Category.assoc _ _ _).trans <|
    (Pi.π _ a ≫= ((Category.assoc _ _ _).trans <|
      (η.app _ ≫= hinv).trans (Category.comp_id _))).trans h3.symm

include hγ in
/-- Fixed-cover pullback along a continuous map and compatible coefficient morphisms preserves the
Čech cup product on cohomology. -/
theorem cechCup_cechComplexPullback {ι : Type u} (U : ι → Opens Y) (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    HomologicalComplex.homologyMap (cechComplexPullback f U γ) n (cechCup U μY hμY p q n h x y) =
      cechCup (fun i ↦ (Opens.map f).obj (U i)) μX hμX p q n h
        (HomologicalComplex.homologyMap (cechComplexPullback f U α) p x)
        (HomologicalComplex.homologyMap (cechComplexPullback f U β) q y) := by
  let eS := cechComplexCompIso (Opens.map f) U S' (fun _ _ ↦ inferInstance)
  have hcomp {K : Y.Presheaf (ModuleCat.{u'} R)} {K' : X.Presheaf (ModuleCat.{u'} R)}
      (η : K ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u'} R) f).obj K') (m : ℕ)
      (z : ((cechComplexFunctor U).obj K).homology m) :
      HomologicalComplex.homologyMap
          (cechComplexCompIso (Opens.map f) U K' (fun _ _ ↦ inferInstance)).hom m
          (HomologicalComplex.homologyMap (cechComplexPullback f U η) m z) =
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map η) m z := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      cechComplexPullback_comp_compIso]
  have hinj : Function.Injective (HomologicalComplex.homologyMap eS.hom n) := by
    intro u v huv
    have hinv := congrArg (HomologicalComplex.homologyMap eS.inv n) huv
    simpa only [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      Iso.hom_inv_id, HomologicalComplex.homologyMap_id, ModuleCat.id_apply] using hinv
  apply hinj
  rw [hcomp γ n, ← cechCup_homologyMap_cechComplexCompIso_hom U (Opens.map f)
    (fun _ _ ↦ inferInstance) μX hμX p q n h, hcomp α p, hcomp β q]
  exact (cechCup_homologyMap_cechComplexFunctor_map U μY hμY
    (fun V ↦ μX (op ((Opens.map f).obj V.unop)))
    (fun _ _ g u v ↦ hμX ((Opens.map f).map g.unop).op u v)
    α β γ hγ p q n h x y).symm

include hγ in
/-- **Pullback compatibility of the topological Čech cup product**: for any continuous map
`f : X ⟶ Y` and coefficient morphisms `α, β, γ` compatible with bilinear pairings `μY, μX`,
pullback along `f` commutes with `TauCeti.Topology.cechCohomologyCup`. -/
theorem cechCohomologyPullback_cechCohomologyCup
    [HasColimitsOfShape (PointOpenCover X) (ModuleCat.{u'} R)]
    [HasColimitsOfShape (PointOpenCover Y) (ModuleCat.{u'} R)]
    (p q n : ℕ) (h : p + q = n)
    (a : (TauCeti.Topology.cechCohomology Y (ModuleCat.{u'} R) p).obj P)
    (b : (TauCeti.Topology.cechCohomology Y (ModuleCat.{u'} R) q).obj Q) :
    cechCohomologyPullback f n γ (TauCeti.Topology.cechCohomologyCup μY hμY p q n h a b) =
      TauCeti.Topology.cechCohomologyCup μX hμX p q n h
        (cechCohomologyPullback f p α a) (cechCohomologyPullback f q β b) := by
  let B₁ := (TauCeti.Topology.cechCohomologyCup μY hμY p q n h).compr₂
    (cechCohomologyPullback f n γ).hom
  let B₂ := (LinearMap.compl₂ (TauCeti.Topology.cechCohomologyCup μX hμX p q n h)
      (cechCohomologyPullback f q β).hom).comp (cechCohomologyPullback f p α).hom
  refine cechCohomology_bilinear_ext PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    (B₁ := B₁) (B₂ := B₂) (fun U x y ↦ ?_) a b
  have hU' : IsOpenCover (fun i ↦ (Opens.map f).obj (U.opens i)) := U.isOpenCover.comap f.hom
  have hpb {K : Y.Presheaf (ModuleCat.{u'} R)} {K' : X.Presheaf (ModuleCat.{u'} R)}
      (η : K ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u'} R) f).obj K') (m : ℕ)
      (z : ((cechComplexFunctor U.opens).obj K).homology m) :
      cechCohomologyPullback f m η
          ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) m U).app K z) =
        (TauCeti.Topology.toCechCohomology (ModuleCat.{u'} R) m
          (fun i ↦ (Opens.map f).obj (U.opens i)) hU').app K'
          (HomologicalComplex.homologyMap (cechComplexPullback f U.opens η) m z) := by
    have hEq := toCechCohomology_app_comp_cechCohomologyPullback f m η U.opens U.isOpenCover
    rw [TauCeti.Topology.toCechCohomology_opens] at hEq
    exact ConcreteCategory.congr_hom hEq z
  simp only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  rw [TauCeti.Topology.cechCohomologyCup, cechCohomologyCup_cechCohomologyι,
    hpb γ n, hpb α p, hpb β q,
    cechCup_cechComplexPullback f μY hμY μX hμX α β γ hγ U.opens p q n h x y,
    ← TauCeti.Topology.cechCohomologyCup_toCechCohomology]

end CupCompatibility

end TopCat.Hom

namespace TopologicalSpace.Opens

variable {R : Type uR} [CommRing R] [HasProducts.{u} (ModuleCat.{u'} R)]
  {X : TopCat.{u}} (W : Opens X)
  [HasColimitsOfShape (PointOpenCover X) (ModuleCat.{u'} R)]
  [HasColimitsOfShape (PointOpenCover ((Opens.toTopCat X).obj W)) (ModuleCat.{u'} R)]
  {P Q S : X.Presheaf (ModuleCat.{u'} R)}

private lemma cechCohomologyRestrict_eq_pullback (n : ℕ) (K : X.Presheaf (ModuleCat.{u'} R)) :
    cechCohomologyRestrict W n K =
      TopCat.Hom.cechCohomologyPullback (Q := W.isOpenEmbedding.isOpenMap.functor.op ⋙ K)
        W.inclusion' n
        (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) K) := by
  refine cechCohomology_obj_hom_ext fun U ↦ ?_
  have hto := NatTrans.congr_app
    (TauCeti.Topology.toCechCohomology_opens (ModuleCat.{u'} R) n U).symm K
  have h1 := toCechCohomology_app_comp_cechCohomologyRestrict W n K U.opens U.isOpenCover
  rw [cechComplexRestrict_eq] at h1
  have h2 := TopCat.Hom.toCechCohomology_app_comp_cechCohomologyPullback
    (Q := W.isOpenEmbedding.isOpenMap.functor.op ⋙ K) W.inclusion' n
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) K)
    U.opens U.isOpenCover
  exact (hto =≫ _).trans <| h1.trans <| h2.symm.trans (hto.symm =≫ _)

/-- **Open restriction preserves the Čech cup product.** -/
theorem cechCohomologyRestrict_cechCohomologyCup
    (μ : ∀ V : (Opens X)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V V' : (Opens X)ᵒᵖ⦄ (g : V ⟶ V') x y,
      S.map g (μ V x y) = μ V' (P.map g x) (Q.map g y))
    (p q n : ℕ) (h : p + q = n)
    (a : (TauCeti.Topology.cechCohomology X (ModuleCat.{u'} R) p).obj P)
    (b : (TauCeti.Topology.cechCohomology X (ModuleCat.{u'} R) q).obj Q) :
    cechCohomologyRestrict W n S (TauCeti.Topology.cechCohomologyCup μ hμ p q n h a b) =
      TauCeti.Topology.cechCohomologyCup
        (fun V ↦ μ (op (W.isOpenEmbedding.isOpenMap.functor.obj V.unop)))
        (fun _ _ g x y ↦ hμ (W.isOpenEmbedding.isOpenMap.functor.map g.unop).op x y) p q n h
        (cechCohomologyRestrict W p P a) (cechCohomologyRestrict W q Q b) := by
  rw [cechCohomologyRestrict_eq_pullback, cechCohomologyRestrict_eq_pullback,
    cechCohomologyRestrict_eq_pullback]
  exact TopCat.Hom.cechCohomologyPullback_cechCohomologyCup
    (P' := W.isOpenEmbedding.isOpenMap.functor.op ⋙ P)
    (Q' := W.isOpenEmbedding.isOpenMap.functor.op ⋙ Q)
    (S' := W.isOpenEmbedding.isOpenMap.functor.op ⋙ S)
    W.inclusion' μ hμ
    (fun V ↦ μ (op (W.isOpenEmbedding.isOpenMap.functor.obj V.unop)))
    (fun _ _ g x y ↦ hμ (W.isOpenEmbedding.isOpenMap.functor.map g.unop).op x y)
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) P)
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) Q)
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) S)
    (fun V x y ↦ hμ (W.isOpenEmbedding.isOpenMap.adjunction.counit.app V.unop).op x y) p q n h a b

end TopologicalSpace.Opens

/-! ### Graded `R`-algebra structure on constant-coefficient Čech cohomology -/

namespace TauCeti.Topology

section ConstantCoefficients

variable (X : TopCat.{u}) (R : Type uR) [Ring R]

/-- The degree `n` Čech cohomology of `X` with constant coefficients in an `R`-module `M`,
defined as the Čech cohomology of the sheaf of locally constant `M`-valued functions. -/
abbrev cechCohomologyConst (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Type (max u v) :=
  (cechCohomology X (ModuleCat.{max u v} R) n).obj (TopCat.locallyConstantModulePresheaf X R M)

/-- The unit element `1 ∈ Ȟ⁰(X; S)` corresponding to the constant function `1 : X → S`. -/
def cechCohomologyConstOne (S : Type v) [AddCommGroup S] [Module R S] [One S] :
    cechCohomologyConst X R S 0 :=
  (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom
    (1 : LocallyConstant (⊤ : Opens X) S)

end ConstantCoefficients

section GradedAlgebra

variable (X : TopCat.{u}) (R : Type uR) [CommRing R] (S : Type v) [Ring S] [Algebra R S]

/-- Pointwise multiplication of locally constant `S`-valued functions, as a natural bilinear
pairing of presheaves on `X`. -/
private def lcMul (V : (Opens X)ᵒᵖ) :
    (TopCat.locallyConstantModulePresheaf X R S).obj V →ₗ[R]
      (TopCat.locallyConstantModulePresheaf X R S).obj V →ₗ[R]
        (TopCat.locallyConstantModulePresheaf X R S).obj V :=
  LinearMap.mul R (LocallyConstant V.unop S)

private lemma lcMul_natural ⦃V W : (Opens X)ᵒᵖ⦄ (f : V ⟶ W)
    (x y : (TopCat.locallyConstantModulePresheaf X R S).obj V) :
    (TopCat.locallyConstantModulePresheaf X R S).map f (lcMul X R S V x y) =
      lcMul X R S W ((TopCat.locallyConstantModulePresheaf X R S).map f x)
        ((TopCat.locallyConstantModulePresheaf X R S).map f y) :=
  rfl

/-- The Čech cup product on constant-coefficient Čech cohomology
`Ȟᵖ(X; S) × Ȟ^q(X; S) ⟶ Ȟ^{p+q}(X; S)` for an `R`-algebra `S`. -/
def cechCohomologyConstCup (p q : ℕ) :
    cechCohomologyConst X R S p →ₗ[R]
      cechCohomologyConst X R S q →ₗ[R]
        cechCohomologyConst X R S (p + q) :=
  cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) p q (p + q) rfl

private lemma sigma_mk_cechCohomologyCup_eq {p q n₁ n₂ : ℕ} (h₁ : p + q = n₁) (h₂ : p + q = n₂)
    (α : cechCohomologyConst X R S p) (β : cechCohomologyConst X R S q) :
    GradedMonoid.mk (A := cechCohomologyConst X R S) n₁
        (cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) p q n₁ h₁ α β) =
      GradedMonoid.mk (A := cechCohomologyConst X R S) n₂
        (cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) p q n₂ h₂ α β) := by
  subst h₁; subst h₂; rfl

private lemma cechCohomologyConstOne_eq_augmentation (U : PointOpenCover X) :
    cechCohomologyConstOne X R S =
      (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 U).app
        (TopCat.locallyConstantModulePresheaf X R S)
        (HomologicalComplex.homologyMap
          (cechAugmentation U.opens isTerminalTop (TopCat.locallyConstantModulePresheaf X R S)) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((TopCat.locallyConstantModulePresheaf X R S).obj (op ⊤))).inv
            (1 : LocallyConstant (⊤ : Opens X) S))) :=
  congrArg (·.hom (1 : LocallyConstant (⊤ : Opens X) S))
    (cechCohomologyZeroIso_hom (TopCat.locallyConstantModuleSheaf X R S) U)

private lemma cechCohomologyCup_one_left (q : ℕ) (β : cechCohomologyConst X R S q) :
    cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) 0 q q (Nat.zero_add q)
        (cechCohomologyConstOne X R S) β = β := by
  rw [cechCohomologyConstOne_eq_augmentation X R S default]
  exact cechCohomologyCup_left_unit PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    isTerminalTop (lcMul X R S) (lcMul_natural X R S)
    (1 : LocallyConstant (⊤ : Opens X) S)
    (fun V (y : LocallyConstant V.unop S) ↦ one_mul y) default q β

private lemma cechCohomologyCup_one_right (p : ℕ) (α : cechCohomologyConst X R S p) :
    cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) p 0 p (Nat.add_zero p)
        α (cechCohomologyConstOne X R S) = α := by
  rw [cechCohomologyConstOne_eq_augmentation X R S default]
  exact cechCohomologyCup_right_unit PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    isTerminalTop (lcMul X R S) (lcMul_natural X R S)
    (1 : LocallyConstant (⊤ : Opens X) S)
    (fun V (x : LocallyConstant V.unop S) ↦ mul_one x) default p α

instance instGOneCechCohomologyConst : GradedMonoid.GOne (cechCohomologyConst X R S) where
  one := cechCohomologyConstOne X R S

instance instGMulCechCohomologyConst : GradedMonoid.GMul (cechCohomologyConst X R S) where
  mul x y := cechCohomologyConstCup X R S _ _ x y

instance instGMonoidCechCohomologyConst : GradedMonoid.GMonoid (cechCohomologyConst X R S) where
  one_mul x := by
    obtain ⟨q, β⟩ := x
    exact (sigma_mk_cechCohomologyCup_eq X R S rfl (Nat.zero_add q) _ β).trans <|
      congrArg (GradedMonoid.mk (A := cechCohomologyConst X R S) q)
        (cechCohomologyCup_one_left X R S q β)
  mul_one x := by
    obtain ⟨p, α⟩ := x
    exact (sigma_mk_cechCohomologyCup_eq X R S rfl (Nat.add_zero p) α _).trans <|
      congrArg (GradedMonoid.mk (A := cechCohomologyConst X R S) p)
        (cechCohomologyCup_one_right X R S p α)
  mul_assoc x y z := by
    obtain ⟨p, α⟩ := x
    obtain ⟨q, β⟩ := y
    obtain ⟨r, γ⟩ := z
    have hassoc := cechCohomologyCup_assoc PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
      (lcMul X R S) (lcMul_natural X R S) (lcMul X R S) (lcMul_natural X R S)
      (lcMul X R S) (lcMul_natural X R S) (lcMul X R S) (lcMul_natural X R S)
      (fun V (a b c : LocallyConstant V.unop S) ↦ mul_assoc a b c)
      (rfl : p + q = p + q) (rfl : p + q + r = p + q + r)
      (rfl : q + r = q + r) (Nat.add_assoc p q r).symm α β γ
    refine (congrArg (GradedMonoid.mk (A := cechCohomologyConst X R S) (p + q + r)) hassoc).trans ?_
    exact sigma_mk_cechCohomologyCup_eq X R S (Nat.add_assoc p q r).symm rfl α _

/-- The constant-coefficient Čech cohomology groups `Ȟⁿ(X; S)` form a graded ring under the cup
product, endowing `⨁ n, Ȟⁿ(X; S)` with a `Ring` structure. -/
instance instGRingCechCohomologyConst : DirectSum.GRing (cechCohomologyConst X R S) where
  mul_zero a := map_zero (cechCohomologyConstCup X R S _ _ a)
  zero_mul {i j} b :=
    congrArg (fun f : cechCohomologyConst X R S j →ₗ[R] cechCohomologyConst X R S (i + j) ↦ f b)
      (map_zero (cechCohomologyConstCup X R S i j))
  mul_add a b c := map_add (cechCohomologyConstCup X R S _ _ a) b c
  add_mul {i j} a b c :=
    congrArg (fun f : cechCohomologyConst X R S j →ₗ[R] cechCohomologyConst X R S (i + j) ↦ f c)
      (map_add (cechCohomologyConstCup X R S i j) a b)
  natCast n := (n : R) • cechCohomologyConstOne X R S
  natCast_zero := by simp
  natCast_succ n := by
    change ((n + 1 : ℕ) : R) • cechCohomologyConstOne X R S =
      (n : R) • cechCohomologyConstOne X R S + cechCohomologyConstOne X R S
    rw [Nat.cast_succ, add_smul, one_smul]
  intCast z := (z : R) • cechCohomologyConstOne X R S
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    change (Int.negSucc n : R) • cechCohomologyConstOne X R S =
      -(((n + 1 : ℕ) : R) • cechCohomologyConstOne X R S)
    rw [Int.cast_negSucc, neg_smul, Nat.cast_succ]

/-- The constant-coefficient Čech cohomology groups `Ȟⁿ(X; S)` form a graded `R`-algebra under the
cup product, endowing `⨁ n, Ȟⁿ(X; S)` with an `Algebra R` structure. -/
instance instGAlgebraCechCohomologyConst : DirectSum.GAlgebra R (cechCohomologyConst X R S) where
  toFun := (LinearMap.toSpanSingleton R _ (cechCohomologyConstOne X R S)).toAddMonoidHom
  map_one := one_smul R _
  map_mul r s := by
    change GradedMonoid.mk (A := cechCohomologyConst X R S) 0
        ((r * s) • cechCohomologyConstOne X R S) =
      GradedMonoid.mk (A := cechCohomologyConst X R S) (0 + 0)
        (cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) 0 0 0 rfl
          (r • cechCohomologyConstOne X R S) (s • cechCohomologyConstOne X R S))
    congr 1
    rw [map_smul, map_smul, LinearMap.smul_apply, cechCohomologyCup_one_left, smul_smul, mul_comm]
  commutes r x := by
    obtain ⟨n, α⟩ := x
    have hL1 : cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) 0 n n (Nat.zero_add n)
        (r • cechCohomologyConstOne X R S) α = r • α := by
      rw [map_smul, LinearMap.smul_apply, cechCohomologyCup_one_left]
    have hR1 : cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) n 0 n (Nat.add_zero n)
        α (r • cechCohomologyConstOne X R S) = r • α := by
      rw [map_smul, cechCohomologyCup_one_right]
    exact (sigma_mk_cechCohomologyCup_eq X R S (p := 0) (q := n) rfl (Nat.zero_add n) _ α).trans <|
      (congrArg (GradedMonoid.mk (A := cechCohomologyConst X R S) n) (hL1.trans hR1.symm)).trans
        (sigma_mk_cechCohomologyCup_eq X R S (p := n) (q := 0) rfl (Nat.add_zero n) α _).symm
  smul_def r x := by
    obtain ⟨n, α⟩ := x
    have hL1 : cechCohomologyCup (lcMul X R S) (lcMul_natural X R S) 0 n n (Nat.zero_add n)
        (r • cechCohomologyConstOne X R S) α = r • α := by
      rw [map_smul, LinearMap.smul_apply, cechCohomologyCup_one_left]
    exact (congrArg (GradedMonoid.mk (A := cechCohomologyConst X R S) n) hL1.symm).trans
      (sigma_mk_cechCohomologyCup_eq X R S (p := 0) (q := n) rfl (Nat.zero_add n) _ α).symm

variable {X R S} in
/-- The product in `⨁ n, Ȟⁿ(X; S)` of two homogeneous Čech cohomology classes is their cup
product. -/
@[simp]
theorem cechCohomologyConst_of_mul_of {p q : ℕ}
    (α : cechCohomologyConst X R S p) (β : cechCohomologyConst X R S q) :
    DirectSum.of (cechCohomologyConst X R S) p α * DirectSum.of (cechCohomologyConst X R S) q β =
      DirectSum.of (cechCohomologyConst X R S) (p + q) (cechCohomologyConstCup X R S p q α β) :=
  DirectSum.of_mul_of α β

/-- Degree-`0` Čech cohomology with constant coefficients `S` matches the ring multiplication on
global locally constant functions `LocallyConstant (⊤ : Opens X) S`. -/
theorem cechCohomologyZeroIso_hom_const_mul (s t : LocallyConstant (⊤ : Opens X) S) :
    cechCohomologyConstCup X R S 0 0
        ((cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom s)
        ((cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom t) =
      (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom (s * t) :=
  cechCohomologyCup_zero_zero_cechCohomologyZeroIso
    (TopCat.locallyConstantModuleSheaf X R S) (TopCat.locallyConstantModuleSheaf X R S)
    (TopCat.locallyConstantModuleSheaf X R S) (lcMul X R S) (lcMul_natural X R S) s t

/-- The canonical `R`-algebra homomorphism identifying `LocallyConstant X S` with the degree-`0`
summand of `⨁ n, Ȟⁿ(X; S)`. -/
def cechCohomologyConstZeroAlgHom :
    LocallyConstant X S →ₐ[R] ⨁ n : ℕ, cechCohomologyConst X R S n :=
  AlgHom.ofLinearMap
    (((DirectSum.lof R ℕ (cechCohomologyConst X R S) 0).comp
        (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom.hom).comp
      (LocallyConstant.congrLeftₐ R (Homeomorph.Set.univ X)).symm.toLinearMap)
    (by
      let e : LocallyConstant X S ≃ₐ[R] LocallyConstant (⊤ : Opens X) S :=
        (LocallyConstant.congrLeftₐ R (Homeomorph.Set.univ X)).symm
      let iso := cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)
      change DirectSum.of (cechCohomologyConst X R S) 0 (iso.hom (e 1)) =
        DirectSum.of (cechCohomologyConst X R S) 0 (cechCohomologyConstOne X R S)
      exact congrArg (DirectSum.of (cechCohomologyConst X R S) 0)
        (congrArg (fun u : LocallyConstant (⊤ : Opens X) S ↦ iso.hom u) (map_one e)))
    (fun s t ↦ by
      let e : LocallyConstant X S ≃ₐ[R] LocallyConstant (⊤ : Opens X) S :=
        (LocallyConstant.congrLeftₐ R (Homeomorph.Set.univ X)).symm
      let iso := cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)
      change DirectSum.of (cechCohomologyConst X R S) 0 (iso.hom (e (s * t))) =
        DirectSum.of (cechCohomologyConst X R S) 0 (iso.hom (e s)) *
        DirectSum.of (cechCohomologyConst X R S) 0 (iso.hom (e t))
      rw [cechCohomologyConst_of_mul_of (iso.hom (e s)) (iso.hom (e t))]
      congr 1
      exact (congrArg (fun u : LocallyConstant (⊤ : Opens X) S ↦ iso.hom u) (map_mul e s t)).trans
        (cechCohomologyZeroIso_hom_const_mul X R S (e s) (e t)).symm)

/-- `cechCohomologyConstZeroAlgHom` is injective. -/
theorem cechCohomologyConstZeroAlgHom_injective :
    Function.Injective (cechCohomologyConstZeroAlgHom X R S) := by
  intro s t h
  have h0 := DirectSum.of_injective (β := cechCohomologyConst X R S) 0 h
  have h1 := congrArg (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).inv.hom h0
  have hinv (u : LocallyConstant (⊤ : Opens X) S) :
      (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).inv.hom
        ((cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom.hom u) = u :=
    congrArg (fun f ↦ f.hom u)
      (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom_inv_id
  exact (LocallyConstant.congrLeftₐ R (Homeomorph.Set.univ X)).symm.injective
    ((hinv _).symm.trans <| h1.trans (hinv _))

end GradedAlgebra

section GradedCommutative

variable {X : TopCat.{u}} {R : Type uR} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- **Graded commutativity in the constant-coefficient Čech cohomology algebra** `⨁ n, Ȟⁿ(X; S)`
when `S` is a commutative `R`-algebra. -/
theorem cechCohomologyConst_of_mul_of_comm {p q : ℕ}
    (α : cechCohomologyConst X R S p) (β : cechCohomologyConst X R S q) :
    DirectSum.of (cechCohomologyConst X R S) q β * DirectSum.of (cechCohomologyConst X R S) p α =
      (-1 : ℤ) ^ (p * q) •
        (DirectSum.of (cechCohomologyConst X R S) p α *
          DirectSum.of (cechCohomologyConst X R S) q β) := by
  rw [cechCohomologyConst_of_mul_of, cechCohomologyConst_of_mul_of, ← map_zsmul]
  have hcomm := cechCohomologyCup_gradedComm PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    (lcMul X R S) (lcMul_natural X R S) (lcMul X R S) (lcMul_natural X R S)
    (fun V (a b : LocallyConstant V.unop S) ↦ mul_comm b a) (rfl : p + q = p + q) α β
  have hsig := sigma_mk_cechCohomologyCup_eq X R S (p := q) (q := p) rfl (Nat.add_comm q p) β α
  rw [hcomm] at hsig
  exact DFinsupp.single_eq_of_sigma_eq hsig

/-- **Twice the square of an odd-degree homogeneous class vanishes** in `⨁ n, Ȟⁿ(X; S)`. -/
theorem two_smul_cechCohomologyConst_of_mul_self_of_odd {p : ℕ} (hp : Odd p)
    (α : cechCohomologyConst X R S p) :
    (2 : R) • (DirectSum.of (cechCohomologyConst X R S) p α *
      DirectSum.of (cechCohomologyConst X R S) p α) = 0 := by
  have hcomm := cechCohomologyConst_of_mul_of_comm (X := X) (R := R) (S := S) α α
  rw [(hp.mul hp).neg_one_pow, neg_one_smul] at hcomm
  rw [two_smul]
  nth_rw 1 [hcomm]
  exact neg_add_cancel _

/-- **Odd-degree homogeneous classes square to zero** in `⨁ n, Ȟⁿ(X; S)` whenever `2` is
invertible in `R`. -/
theorem cechCohomologyConst_of_mul_self_of_odd [Invertible (2 : R)] {p : ℕ} (hp : Odd p)
    (α : cechCohomologyConst X R S p) :
    DirectSum.of (cechCohomologyConst X R S) p α *
      DirectSum.of (cechCohomologyConst X R S) p α = 0 := by
  rw [← one_smul R (DirectSum.of (cechCohomologyConst X R S) p α *
      DirectSum.of (cechCohomologyConst X R S) p α),
    ← invOf_mul_self (2 : R), mul_smul,
    two_smul_cechCohomologyConst_of_mul_self_of_odd hp α, smul_zero]

end GradedCommutative

end TauCeti.Topology

/-! ### Pullback as a graded `R`-algebra homomorphism -/

namespace TopCat.Hom

open TauCeti.Topology

variable {X Y Z : TopCat.{u}}

/-- Pullback along a continuous map `f : X ⟶ Y` on constant-coefficient Čech cohomology, as a
graded `R`-algebra homomorphism `(⨁ n, Ȟⁿ(Y; S)) →ₐ[R] (⨁ n, Ȟⁿ(X; S))`. -/
def cechCohomologyAlgebraPullback (f : X ⟶ Y) (R : Type uR) [CommRing R] (S : Type v) [Ring S]
    [Algebra R S] :
    (⨁ n : ℕ, cechCohomologyConst Y R S n) →ₐ[R]
      (⨁ n : ℕ, cechCohomologyConst X R S n) :=
  DirectSum.toAlgebra R (cechCohomologyConst Y R S)
    (fun n ↦ (DirectSum.lof R ℕ (cechCohomologyConst X R S) n).comp
      (cechCohomologyPullback f n (f.locallyConstantModulePullback R S)).hom)
    (by
      change DirectSum.of (cechCohomologyConst X R S) 0
        (cechCohomologyPullback f 0 (f.locallyConstantModulePullback R S)
          (cechCohomologyConstOne Y R S)) =
        DirectSum.of (cechCohomologyConst X R S) 0 (cechCohomologyConstOne X R S)
      congr 1
      have h0 := ConcreteCategory.congr_hom
        (cechCohomologyZeroIso_hom_comp_cechCohomologyPullback f
          (TopCat.locallyConstantModuleSheaf Y R S) (TopCat.locallyConstantModuleSheaf X R S)
          (f.locallyConstantModulePullback R S)) (1 : LocallyConstant (⊤ : Opens Y) S)
      exact h0.trans <| congrArg
        (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R S)).hom
        (locallyConstantModulePullback_app_one f R (op ⊤)))
    (fun {p q} α β ↦ by
      change DirectSum.of (cechCohomologyConst X R S) (p + q)
          (cechCohomologyPullback f (p + q) (f.locallyConstantModulePullback R S)
            (cechCohomologyConstCup Y R S p q α β)) =
        DirectSum.of (cechCohomologyConst X R S) p
          (cechCohomologyPullback f p (f.locallyConstantModulePullback R S) α) *
        DirectSum.of (cechCohomologyConst X R S) q
          (cechCohomologyPullback f q (f.locallyConstantModulePullback R S) β)
      rw [cechCohomologyConst_of_mul_of]
      congr 1
      exact cechCohomologyPullback_cechCohomologyCup f
        (fun V ↦ LinearMap.mul R (LocallyConstant V.unop S)) (fun _ _ _ _ _ ↦ rfl)
        (fun V ↦ LinearMap.mul R (LocallyConstant V.unop S)) (fun _ _ _ _ _ ↦ rfl)
        (f.locallyConstantModulePullback R S) (f.locallyConstantModulePullback R S)
        (f.locallyConstantModulePullback R S)
        (fun V x y ↦ locallyConstantModulePullback_app_mul f R V x y) p q (p + q) rfl α β)

/-- On a homogeneous class of degree `n`, `f.cechCohomologyAlgebraPullback R S` acts by
`cechCohomologyPullback f n`. -/
@[simp]
theorem cechCohomologyAlgebraPullback_of (f : X ⟶ Y) (R : Type uR) [CommRing R] (S : Type v)
    [Ring S] [Algebra R S] (n : ℕ) (α : cechCohomologyConst Y R S n) :
    f.cechCohomologyAlgebraPullback R S (DirectSum.of (cechCohomologyConst Y R S) n α) =
      DirectSum.of (cechCohomologyConst X R S) n
        (cechCohomologyPullback f n (f.locallyConstantModulePullback R S) α) :=
  DirectSum.toAddMonoid_of
    (fun i ↦ ((DirectSum.lof R ℕ (cechCohomologyConst X R S) i).comp
      (cechCohomologyPullback f i (f.locallyConstantModulePullback R S)).hom).toAddMonoidHom) n α

/-- Pullback along the identity map is the identity algebra homomorphism. -/
@[simp]
theorem cechCohomologyAlgebraPullback_id (X : TopCat.{u}) (R : Type uR) [CommRing R] (S : Type v)
    [Ring S] [Algebra R S] :
    cechCohomologyAlgebraPullback (𝟙 X) R S = AlgHom.id R _ := by
  refine DirectSum.algHom_ext R (cechCohomologyConst X R S) fun n α ↦ ?_
  rw [cechCohomologyAlgebraPullback_of, AlgHom.id_apply, locallyConstantModulePullback_id,
    cechCohomologyPullback_id, ModuleCat.id_apply]

/-- Pullback of constant-coefficient Čech cohomology algebras is contravariantly functorial. -/
@[simp]
theorem cechCohomologyAlgebraPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (R : Type uR) [CommRing R]
    (S : Type v) [Ring S] [Algebra R S] :
    cechCohomologyAlgebraPullback (f ≫ g) R S =
      (f.cechCohomologyAlgebraPullback R S).comp (g.cechCohomologyAlgebraPullback R S) := by
  refine DirectSum.algHom_ext R (cechCohomologyConst Z R S) fun n α ↦ ?_
  have hpb : cechCohomologyPullback (f ≫ g) n ((f ≫ g).locallyConstantModulePullback R S) =
      cechCohomologyPullback g n (g.locallyConstantModulePullback R S) ≫
        cechCohomologyPullback f n (f.locallyConstantModulePullback R S) :=
    (congrArg (cechCohomologyPullback (f ≫ g) n)
      (locallyConstantModulePullback_comp f g R S)).trans
      (cechCohomologyPullback_comp f g n _ _)
  rw [AlgHom.comp_apply, cechCohomologyAlgebraPullback_of, cechCohomologyAlgebraPullback_of,
    cechCohomologyAlgebraPullback_of]
  exact congrArg (DirectSum.of (cechCohomologyConst X R S) n)
    (ConcreteCategory.congr_hom hpb α)

end TopCat.Hom

/-! ### Explicit front-face / back-face cochain calculation on two discrete points -/

namespace TauCeti.Topology

section TwoPointCochainCheck

variable (R : Type uR) [CommRing R]

/-- **Front-face versus back-face check on the two-point discrete space.** On `X = TopCat.of Bool`
with the trivial two-member cover `U 0 = U 1 = ⊤`, let `f` be the `0`-cochain with
`f(0) = 1_{false}`, `f(1) = 1_{true}`, and `c` be the `1`-cochain with `c(0, 1) = 1`. Then on the
`1`-simplex `(0, 1)`, the cup product `f ⌣ c` evaluates to `1_{false}` (using the front vertex `0`),
while `c ⌣ f` evaluates to `1_{true}` (using the back vertex `1`). In particular, for any nontrivial
commutative ring `R`, the cochain-level Čech cup product is not commutative even when `0 * 1 = 0`.
-/
theorem cechCupCochain_bool_front_back [Nontrivial R] :
    let X : TopCat.{0} := TopCat.of Bool
    let U : Fin 2 → Opens X := fun _ ↦ ⊤
    let P := TopCat.locallyConstantModulePresheaf X R R
    let μ : ∀ V : (Opens X)ᵒᵖ, P.obj V →ₗ[R] P.obj V →ₗ[R] P.obj V :=
      fun V ↦ LinearMap.mul R (LocallyConstant V.unop R)
    let ind : Bool → P.obj (op ⊤) :=
      fun b ↦ (⟨fun x ↦ if x.1 = b then 1 else 0, IsLocallyConstant.of_discrete _⟩ :
        LocallyConstant (⊤ : Opens X) R)
    let f : ↥(∏ᶜ fun a : Fin 1 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) :=
      (ModuleCat.piIsoPi _).inv fun a ↦
        P.map (homOfLE le_top : (∏ᶜ fun j : Fin 1 ↦ U (a j)) ⟶ ⊤).op
          (if a 0 = 0 then ind false else ind true)
    let c : ↥(∏ᶜ fun a : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) :=
      (ModuleCat.piIsoPi (fun a : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))))).inv
        fun a ↦ ((1 : LocallyConstant _ R) : P.obj (op (∏ᶜ fun j ↦ U (a j))))
    let k : Fin 2 → Fin 2 := ![0, 1]
    (Pi.π (fun b : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) k
        (cechCupCochain U μ 0 1 1 rfl f c) =
      P.map (homOfLE le_top : (∏ᶜ fun j ↦ U (k j)) ⟶ ⊤).op (ind false)) ∧
    (Pi.π (fun b : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) k
        (cechCupCochain U μ 1 0 1 rfl c f) =
      P.map (homOfLE le_top : (∏ᶜ fun j ↦ U (k j)) ⟶ ⊤).op (ind true)) ∧
    cechCupCochain U μ 0 1 1 rfl f c ≠ cechCupCochain U μ 1 0 1 rfl c f := by
  intro X U P μ ind f c k
  have hpi {n : ℕ} (g : ∀ b : Fin (n + 1) → Fin 2, P.obj (op (∏ᶜ fun j ↦ U (b j))))
      (b : Fin (n + 1) → Fin 2) :
      Pi.π (fun a : Fin (n + 1) → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b
        ((ModuleCat.piIsoPi _).inv g) = g b := by
    have h := ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_inv_kernel_ι
        (fun a : Fin (n + 1) → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b) g
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.proj_apply] using h
  have hf (b : Fin 1 → Fin 2) :
      Pi.π (fun a : Fin 1 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b f =
        P.map (homOfLE le_top : (∏ᶜ fun j ↦ U (b j)) ⟶ ⊤).op
          (if b 0 = 0 then ind false else ind true) := hpi _ b
  have hc (b : Fin 2 → Fin 2) :
      Pi.π (fun a : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b c =
        ((1 : LocallyConstant _ R) : P.obj (op (∏ᶜ fun j ↦ U (b j)))) := hpi _ b
  have hfc : Pi.π (fun b : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) k
      (cechCupCochain U μ 0 1 1 rfl f c) =
      P.map (homOfLE le_top : (∏ᶜ fun j ↦ U (k j)) ⟶ ⊤).op (ind false) := by
    rw [π_cechCupCochain U μ 0 1 1 rfl f c k, hf, hc]
    exact LocallyConstant.ext (X := ↥(∏ᶜ fun j ↦ U (k j))) (Y := R) fun _ ↦ mul_one _
  have hcf : Pi.π (fun b : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) k
      (cechCupCochain U μ 1 0 1 rfl c f) =
      P.map (homOfLE le_top : (∏ᶜ fun j ↦ U (k j)) ⟶ ⊤).op (ind true) := by
    rw [π_cechCupCochain U μ 1 0 1 rfl c f k, hc, hf]
    exact LocallyConstant.ext (X := ↥(∏ᶜ fun j ↦ U (k j))) (Y := R) fun _ ↦ one_mul _
  refine ⟨hfc, hcf, fun hne ↦ ?_⟩
  have hval := congrArg
    (Pi.π (fun b : Fin 2 → Fin 2 ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) k) hne
  rw [hfc, hcf] at hval
  have htop : (∏ᶜ fun j : Fin 2 ↦ U (k j)) = ⊤ :=
    le_antisymm le_top (leOfHom (Pi.lift fun _ ↦ 𝟙 ⊤))
  have hmem : false ∈ (∏ᶜ fun j : Fin 2 ↦ U (k j)) := by rw [htop]; trivial
  have hpt := DFunLike.congr_fun
    (F := LocallyConstant ↥(∏ᶜ fun j : Fin 2 ↦ U (k j)) R) hval ⟨false, hmem⟩
  change (if false = false then (1 : R) else 0) = (if false = true then (1 : R) else 0) at hpt
  simp at hpt

end TwoPointCochainCheck

end TauCeti.Topology
