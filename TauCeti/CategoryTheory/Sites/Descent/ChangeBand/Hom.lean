/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Functor
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map

/-!
# The extended Isom torsors for change of band

Let `b` be an `A`-banding of a gerbe `F` and let `φ : A ⟶ B` be a homomorphism of abelian
sheaves. The Hom sheaves for change of band are obtained by extending the structure group of
`b.sheafHomTorsor x y` along `φ|_U`. This file constructs them as a functor of both endpoints,
using the existing `Sheaf.Torsor.map`. Their local representatives `[p, c]` are the sections
`c • [p, 0]`. Transport in either endpoint keeps `c`, and acting on `p` by `a` adds `φ a` to `c`.

Rules on pairs that respect this relation descend uniquely to sheaf morphisms out of the
extended Hom sheaf. For the identity homomorphism, these torsors are naturally isomorphic to the
original Isom
torsors, compatibly with their actions and endpoint transport. The construction is the
Hom-sheaf part of change of band; composition and the pseudofunctor structure are not
constructed here.

## References

* Martin Olsson, *Stacks* (lecture notes), Lemma 31.3 and Theorem 31.7.
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for extension of the structure
  group of a torsor.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {A B : Sheaf J AddCommGrpCat.{v'}}
  (b : F.AbelianBanding J A) [F.IsGerbe J]

variable (φ : A ⟶ B) (U : C)
  [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')]

/-- The extended Isom torsors for change of band, contravariant in the source and covariant in
the target. The coefficient group is the restriction of `B` to `J.over U`. -/
-- Exposed so that section types reduce to those of the extended torsor; a definition keeps
-- the composite object projection from simplifying inside the types of representative rules.
@[expose] def changeBandHomFunctor :
    (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U)) ⥤
      Sheaf.Torsor ((abelianSheafToGrpSheaf (J.over U)).obj
        ((J.overPullback AddCommGrpCat.{v'} U).obj B)) :=
  b.sheafHomTorsorFunctor U ⋙ Sheaf.Torsor.mapFunctor
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))

variable {U}

/-- The canonical morphism from the original Isom sheaf to the extended Hom sheaf, sending
each local section `p` to `[p, 0]`. -/
def toChangeBandHom (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⟶ ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)).toMap _

/-- The canonical map is extension of the structure group on the original Isom torsor. -/
lemma toChangeBandHom_def (x y : F.obj (.mk (op U))) :
    b.toChangeBandHom φ x y =
      (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)).toMap
        ((abelianSheafToGrpSheaf (J.over U)).map
          ((J.overPullback AddCommGrpCat.{v'} U).map φ)) := (rfl)

/-- A local contracted-product representative `[p, c]` in an extended Hom torsor. -/
def changeBandHomMk {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.obj T :=
  abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
    (.ofAdd c) • (b.toChangeBandHom φ x y).hom.app T p

/-- A representative is the translate of the canonical image by its coefficient. -/
lemma changeBandHomMk_def {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ p c =
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
        (.ofAdd c) • (b.toChangeBandHom φ x y).hom.app T p := (rfl)

/-- The representative with zero coefficient is the image of the original local isomorphism. -/
@[simp]
lemma changeBandHomMk_zero {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) :
    b.changeBandHomMk φ p 0 = (b.toChangeBandHom φ x y).hom.app T p := by
  unfold changeBandHomMk
  exact (congrArg (· • _) (map_one _)).trans (one_smul _ _)

/-- Addition in the new coefficient is the action of the new band on a representative. -/
lemma changeBandHomMk_add {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c d : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ p (c + d) =
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
        (.ofAdd c) • b.changeBandHomMk φ p d := by
  unfold changeBandHomMk
  exact (congrArg (· • (b.toChangeBandHom φ x y).hom.app T p) (map_mul
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T)
      (.ofAdd c) (.ofAdd d))).trans (mul_smul _ _ _)

/-- Restricting a local representative restricts both its local isomorphism and coefficient. -/
lemma changeBandHom_map_mk {x y : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.map f
        (b.changeBandHomMk φ p c) =
      b.changeBandHomMk φ ((F.presheafHom x y).map f p) (B.obj.map f.unop.left.op c) := by
  simp only [changeBandHomMk]
  rw [Sheaf.Torsor.map_smul, abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv]
  exact congrArg (_ • ·) (NatTrans.naturality_apply (b.toChangeBandHom φ x y).hom f p).symm

/-- The map from the old Isom sheaf is compatible with the homomorphism of bands. -/
lemma toChangeBandHom_homAct {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left)) :
    (b.toChangeBandHom φ x y).hom.app T (b.homAct p (.ofAdd a)) =
      b.changeBandHomMk φ p (φ.hom.app (op T.unop.left) a) := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  have h := P.toMap_smul
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
      (.ofAdd a)) p
  refine (congrArg ((b.toChangeBandHom φ x y).hom.app T)
    (b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a p)).symm.trans ?_
  refine h.trans ?_
  exact congrArg (· • (b.toChangeBandHom φ x y).hom.app T p)
    (abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
      ((J.overPullback AddCommGrpCat.{v'} U).map φ) T (.ofAdd a))

/-- The relation defining extension of the structure group: acting on `p` adds the image of
the acting coefficient to the new coefficient. -/
@[simp]
lemma changeBandHomMk_homAct {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left))
    (c : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ (b.homAct p (.ofAdd a)) c =
      b.changeBandHomMk φ p (c + φ.hom.app (op T.unop.left) a) := by
  rw [b.changeBandHomMk_add, changeBandHomMk, b.toChangeBandHom_homAct]

private def coefficientIso : coefficientSheaf J B U ≅
    (Sheaf.MulActionSheaf.mulRight
      ((abelianSheafToGrpSheaf (J.over U)).map
        ((J.overPullback AddCommGrpCat.{v'} U).map φ))).sheaf :=
  (fullyFaithfulSheafToPresheaf (J.over U) (Type v')).preimageIso
    (NatIso.ofComponents (fun T ↦
      ((Multiplicative.ofAdd : _ ≃ Multiplicative _).trans
        (abelianSheafToGrpSheafObjEquiv
          ((J.overPullback AddCommGrpCat.{v'} U).obj B) T).toEquiv).toIso)
      (fun f ↦ by
        ext c
        exact (abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv
          ((J.overPullback AddCommGrpCat.{v'} U).obj B) f (.ofAdd c)).symm))

/-- The morphism of sheaves taking `(p, c)` to the representative `[p, c]`. -/
def changeBandHomPairing (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶
      ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  (P.sheaf ◁ (coefficientIso φ (U := U)).hom) ≫
    P.toContractedProduct (Sheaf.MulActionSheaf.mulRight ψ) ≫
      (P.contractedProductMulRightIso ψ).hom

/-- The pairing takes a pair of sections to its contracted-product representative. -/
lemma changeBandHomPairing_hom_app (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomPairing φ x y).hom.app T (p, c) = b.changeBandHomMk φ p c := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  let a := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
    (.ofAdd c)
  refine (congrArg ((P.contractedProductMulRightIso ψ).hom.hom.app T)
    (P.toContractedProduct_hom_app (Sheaf.MulActionSheaf.mulRight ψ) (p, a))).trans ?_
  exact Sheaf.Torsor.contractedProductMulRightIso_hom_hom_app_contractedProductMk
    (φ := ψ) (P := P) p a

/-- Every section of an extended Hom torsor is locally a representative `[p, c]`. -/
instance isLocallySurjective_changeBandHomPairing (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallySurjective (b.changeBandHomPairing φ x y) := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  have he := Sheaf.isLocallySurjective_of_iso
    (P.sheaf ◁ (coefficientIso φ (U := U)).hom)
  have hi := Sheaf.isLocallySurjective_of_iso (P.contractedProductMulRightIso ψ).hom
  have hq := Sheaf.Torsor.isLocallySurjective_toContractedProduct P
    (Sheaf.MulActionSheaf.mulRight ψ)
  have hc := Sheaf.isLocallySurjective_comp
    (P.toContractedProduct (Sheaf.MulActionSheaf.mulRight ψ))
    (P.contractedProductMulRightIso ψ).hom
  exact @Sheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ he hc

/-- Maps of sheaves out of an extended Hom torsor are determined on local representatives. -/
@[ext]
lemma changeBandHom_hom_ext {x y : F.obj (.mk (op U))} {Q : Sheaf (J.over U) (Type v')}
    {f g : ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ⟶ Q}
    (h : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (c : B.obj.obj (op T.unop.left)),
      f.hom.app T (b.changeBandHomMk φ p c) = g.hom.app T (b.changeBandHomMk φ p c)) :
    f = g := by
  apply (cancel_epi (b.changeBandHomPairing φ x y)).1
  ext T ⟨p, c⟩
  -- Evaluate composition in the category of sheaves sectionwise.
  change f.hom.app T ((b.changeBandHomPairing φ x y).hom.app T (p, c)) =
    g.hom.app T ((b.changeBandHomPairing φ x y).hom.app T (p, c))
  rw [b.changeBandHomPairing_hom_app φ x y T p c]
  exact h T p c

/-- A rule on pairs descends to the extended Hom sheaf when acting on the original
isomorphism adds the image of the acting coefficient to the new coefficient. -/
def changeBandHomDesc {x y : F.obj (.mk (op U))} {Q : Sheaf (J.over U) (Type v')}
    (u : F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶ Q)
    (hu : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (a : A.obj.obj (op T.unop.left)) (c : B.obj.obj (op T.unop.left)),
      u.hom.app T (b.homAct p (.ofAdd a), c) =
        u.hom.app T (p, c + φ.hom.app (op T.unop.left) a)) :
    ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ⟶ Q :=
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  (P.contractedProductMulRightIso ψ).inv ≫
    Sheaf.Torsor.contractedProductDesc (P := P) (X := Sheaf.MulActionSheaf.mulRight ψ)
      (P.sheaf ◁ (coefficientIso φ (U := U)).inv ≫ u)
      (fun T g p c ↦ by
        let EA : Multiplicative (A.obj.obj (op T.unop.left)) ≃* _ :=
          abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
        let E : Multiplicative (B.obj.obj (op T.unop.left)) ≃* _ :=
          abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
        obtain ⟨a, rfl⟩ := EA.surjective g
        obtain ⟨c, rfl⟩ := E.surjective c
        have he (d) : (coefficientIso φ (U := U)).inv.hom.app T (E d) = d.toAdd :=
          congrArg (fun k ↦ k.hom.app T d.toAdd) (coefficientIso φ (U := U)).hom_inv_id
        have hp : @Eq ((F.presheafHom x y).obj T) _ (b.homAct p a) :=
          b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a.toAdd p
        have hφ : ψ.hom.app T (EA a) = E (.ofAdd (φ.hom.app _ a.toAdd)) :=
          abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
            ((J.overPullback AddCommGrpCat.{v'} U).map φ) T a
        have hmul : E c * (ψ.hom.app T (EA a))⁻¹ =
            E (c * (.ofAdd (φ.hom.app _ a.toAdd))⁻¹) := by rw [hφ, map_mul, map_inv]
        have hc := (Sheaf.MulActionSheaf.mulRight_smul ψ (EA a) (E c)).trans hmul
        have hi : @Eq (B.obj.obj (op T.unop.left)) _
            (c.toAdd - φ.hom.app _ a.toAdd) :=
          (congrArg ((coefficientIso φ (U := U)).inv.hom.app T) hc).trans
            ((he _).trans (by simp [sub_eq_add_neg]; rfl))
        -- Form sectionwise congruences before composing them, so the function instances
        -- are inferred from the public section types.
        have hpair := congrArg₂ Prod.mk hp hi
        have h₁ := congrArg (u.hom.app T) hpair
        have h₂ := (hu T p a.toAdd _).trans (congrArg (fun d ↦ u.hom.app T (p, d))
          (sub_add_cancel c.toAdd (φ.hom.app _ a.toAdd)))
        have h₃ := congrArg (u.hom.app T) (congrArg₂ Prod.mk (Eq.refl p) (he c))
        convert h₁.trans (h₂.trans h₃.symm) using 1 <;> rfl)

/-- Descending a rule on pairs and then composing with the pairing recovers that rule. -/
@[reassoc (attr := simp)]
lemma changeBandHomPairing_desc {x y : F.obj (.mk (op U))}
    {Q : Sheaf (J.over U) (Type v')}
    (u : F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶ Q)
    (hu : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (a : A.obj.obj (op T.unop.left)) (c : B.obj.obj (op T.unop.left)),
      u.hom.app T (b.homAct p (.ofAdd a), c) =
        u.hom.app T (p, c + φ.hom.app (op T.unop.left) a)) :
    b.changeBandHomPairing φ x y ≫ b.changeBandHomDesc φ u hu = u := by
  -- The torsor's sheaf is the original Hom sheaf; `erw` lets categorical rewriting use
  -- that exposed projection without unfolding the contracted-product constructions.
  dsimp only [changeBandHomPairing, changeBandHomDesc]
  erw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Sheaf.Torsor.toContractedProduct_contractedProductDesc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The descended morphism evaluates on `[p, c]` by the original rule on pairs. -/
lemma changeBandHomDesc_hom_app_mk {x y : F.obj (.mk (op U))}
    {Q : Sheaf (J.over U) (Type v')}
    (u : F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶ Q)
    (hu : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (a : A.obj.obj (op T.unop.left)) (c : B.obj.obj (op T.unop.left)),
      u.hom.app T (b.homAct p (.ofAdd a), c) =
        u.hom.app T (p, c + φ.hom.app (op T.unop.left) a))
    (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
    (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomDesc φ u hu).hom.app T (b.changeBandHomMk φ p c) =
      u.hom.app T (p, c) := by
  rw [← b.changeBandHomPairing_hom_app φ x y T p c]
  exact congrArg (fun k ↦ k.hom.app T (p, c)) (b.changeBandHomPairing_desc φ u hu)

/-- The canonical images of the original Isom sheaves commute with transport in the endpoints. -/
@[reassoc]
lemma toChangeBandHom_naturality {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) :
    b.toChangeBandHom φ p.1.unop p.2 ≫ ((b.changeBandHomFunctor φ U).map f).hom =
      ((b.sheafHomTorsorFunctor U).map f).hom ≫ b.toChangeBandHom φ q.1.unop q.2 :=
  Sheaf.Torsor.toMap_mapFunctor_map _ _

/-- Transport in either endpoint keeps the new coefficient of a representative. -/
lemma changeBandHomFunctor_map_mk {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) (T : (Over U)ᵒᵖ) (h : (F.presheafHom p.1.unop p.2).obj T)
    (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).map f).hom.hom.app T (b.changeBandHomMk φ h c) =
      b.changeBandHomMk φ ((F.map T.unop.hom.op.toLoc).toFunctor.map f.1.unop ≫ h ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map f.2) c := by
  refine (Sheaf.Torsor.mapFunctor_map_hom_app_smul_toMap
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))
    ((b.sheafHomTorsorFunctor U).map f) T h _).trans ?_
  exact congrArg (fun k ↦ b.changeBandHomMk φ k c)
    (b.sheafHomTorsorFunctor_map_hom_app f T h)

variable (U)

/-- Change of band along the identity recovers the original Isom torsors, naturally in both
endpoints and equivariantly for their actions. -/
def changeBandHomIdIso : b.changeBandHomFunctor (𝟙 A) U ≅ b.sheafHomTorsorFunctor U := by
  exact Functor.isoWhiskerLeft (b.sheafHomTorsorFunctor U)
    (Sheaf.Torsor.mapIdIso (by simp)) ≪≫
    Functor.rightUnitor (b.sheafHomTorsorFunctor U)

variable {U}

/-- The identity-band comparison is inverse to the map from the original Isom sheaf. -/
@[reassoc (attr := simp)]
lemma toChangeBandHom_changeBandHomIdIso_hom (x y : F.obj (.mk (op U))) :
    b.toChangeBandHom (𝟙 A) x y ≫ ((b.changeBandHomIdIso U).hom.app (op x, y)).hom =
      𝟙 (F.sheafHom J x y) := by
  dsimp only [changeBandHomIdIso]
  exact Sheaf.Torsor.toMap_mapIdIso_hom (by simp) _

/-- On local representatives the identity-band comparison is the original band action. -/
lemma changeBandHomIdIso_hom_app_mk {x y : F.obj (.mk (op U))} (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left)) :
    ((b.changeBandHomIdIso U).hom.app (op x, y)).hom.hom.app T
        (b.changeBandHomMk (𝟙 A) p a) = b.homAct p (.ofAdd a) := by
  let E := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
  refine (Sheaf.Torsor.mapIdIso_hom_app_smul_toMap (by simp)
    (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)) T p (E (.ofAdd a))).trans ?_
  exact b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a p

end CategoryTheory.Pseudofunctor.AbelianBanding
