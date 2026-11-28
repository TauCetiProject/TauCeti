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

Rules on pairs that commute with restriction and respect this relation descend uniquely to
sheaf morphisms out of the extended Hom sheaf. For the identity homomorphism, these torsors
are naturally isomorphic to the
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

/-- A representative with a multiplicatively presented coefficient is its translate of the
canonical image. This converts between the additive representative API and the torsor action. -/
lemma changeBandHomMk_toAdd {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T)
    (a : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat.{v'} U).obj B)).obj.obj T) :
    b.changeBandHomMk φ p
        ((abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T).symm
          a).toAdd = a • (b.toChangeBandHom φ x y).hom.app T p := by
  exact congrArg (· • _) (MulEquiv.apply_symm_apply _ a)

/-- A chosen local isomorphism identifies the extended Hom torsor with its additive
coefficient group; the inverse extracts the unique coefficient of a section. -/
def changeBandHomEquiv {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) :
    B.obj.obj (op T.unop.left) ≃
      ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.obj T :=
  ((Multiplicative.ofAdd : _ ≃ Multiplicative _).trans
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T).toEquiv).trans
    (Equiv.ofBijective (fun a ↦ a • (b.toChangeBandHom φ x y).hom.app T p)
      ⟨((b.changeBandHomFunctor φ U).obj (op x, y)).smul_left_injective _,
        fun s ↦ MulAction.exists_smul_eq _ _ s⟩)

/-- The coefficient equivalence sends `c` to the representative `[p, c]`. -/
@[simp]
lemma changeBandHomEquiv_apply {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    b.changeBandHomEquiv φ p c = b.changeBandHomMk φ p c := (rfl)

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

/-- The morphism of sheaves taking `(p, c)` to the representative `[p, c]`. -/
def changeBandHomPairing (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶
      ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  (P.sheaf ◁ (abelianSheafToGrpSheafForgetIso ((J.overPullback AddCommGrpCat.{v'} U).obj B)).hom) ≫
    P.mulRightPairing ψ

/-- The pairing takes a pair of sections to its contracted-product representative. -/
lemma changeBandHomPairing_hom_app (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomPairing φ x y).hom.app T (p, c) = b.changeBandHomMk φ p c := by
  dsimp only [changeBandHomPairing]
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
  -- Whiskering is the product map on sections; its source uses the torsor sheaf projection.
  change (Sheaf.Torsor.mulRightPairing
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))
    (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _))).hom.app T
    (p, (abelianSheafToGrpSheafForgetIso
      ((J.overPullback AddCommGrpCat.{v'} U).obj B)).hom.hom.app T c) = _
  erw [Sheaf.Torsor.mulRightPairing_hom_app, abelianSheafToGrpSheafForgetIso_hom_app]
  rfl

/-- Every section of an extended Hom torsor is locally a representative `[p, c]`. -/
instance isLocallySurjective_changeBandHomPairing (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallySurjective (b.changeBandHomPairing φ x y) := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  let e := abelianSheafToGrpSheafForgetIso ((J.overPullback AddCommGrpCat.{v'} U).obj B)
  have he : Sheaf.IsLocallySurjective
      (P.sheaf ◁ e.hom : P.sheaf ⊗ coefficientSheaf J B U ⟶
        P.sheaf ⊗ (Sheaf.MulActionSheaf.mulRight ψ).sheaf) :=
    Sheaf.isLocallySurjective_of_iso (P.sheaf ◁ e.hom)
  have hq : Sheaf.IsLocallySurjective (P.mulRightPairing ψ) :=
    Sheaf.Torsor.isLocallySurjective_mulRightPairing ψ P
  -- Fix the tensor objects so instance search uses the same sheaf projections as `he` and `hq`.
  change Sheaf.IsLocallySurjective ((P.sheaf ◁ e.hom) ≫ P.mulRightPairing ψ)
  exact Sheaf.isLocallySurjective_comp
    (F₁ := P.sheaf ⊗ coefficientSheaf J B U)
    (F₂ := P.sheaf ⊗ (Sheaf.MulActionSheaf.mulRight ψ).sheaf)
    (F₃ := (P.map ψ).sheaf) (P.sheaf ◁ e.hom) (P.mulRightPairing ψ)

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
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  -- The tensor sections are pairs only after reducing the sheaf tensor projection.
  change f.hom.app T ((b.changeBandHomPairing φ x y).hom.app T (p, c)) =
    g.hom.app T ((b.changeBandHomPairing φ x y).hom.app T (p, c))
  rw [b.changeBandHomPairing_hom_app φ x y T p c]
  exact h T p c

omit [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')] in
private lemma coefficient_mulRight_smul (T : (Over U)ᵒᵖ)
    (a : Multiplicative (A.obj.obj (op T.unop.left)))
    (c : Multiplicative (B.obj.obj (op T.unop.left))) :
    let EA : Multiplicative (A.obj.obj (op T.unop.left)) ≃* _ :=
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
    let E : Multiplicative (B.obj.obj (op T.unop.left)) ≃* _ :=
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ)
    (abelianSheafToGrpSheafForgetIso ((J.overPullback AddCommGrpCat.{v'} U).obj B)).inv.hom.app T
        (@SMul.smul _ ((Sheaf.MulActionSheaf.mulRight ψ).sheaf.obj.obj T)
          ((Sheaf.MulActionSheaf.mulRight ψ).mulAction T).toSMul (EA a) (E c)) =
      c.toAdd - φ.hom.app (op T.unop.left) a.toAdd := by
  intro EA E ψ
  have hφ : ψ.hom.app T (EA a) = E (.ofAdd (φ.hom.app _ a.toAdd)) :=
    abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
    ((J.overPullback AddCommGrpCat.{v'} U).map φ) T a
  have hmul : E c * (ψ.hom.app T (EA a))⁻¹ =
      E (c * (.ofAdd (φ.hom.app _ a.toAdd))⁻¹) := by rw [hφ, map_mul, map_inv]
  have hc := (Sheaf.MulActionSheaf.mulRight_smul ψ (EA a) (E c)).trans hmul
  calc
    _ = (abelianSheafToGrpSheafForgetIso
        ((J.overPullback AddCommGrpCat.{v'} U).obj B)).inv.hom.app T
          (E (c * (.ofAdd (φ.hom.app _ a.toAdd))⁻¹)) := congrArg _ hc
    _ = _ := by
      erw [abelianSheafToGrpSheafForgetIso_inv_app, MulEquiv.symm_apply_apply]
      simp only [sub_eq_add_neg]
      rfl

/-- A rule on pairs that commutes with restriction descends to the extended Hom sheaf when
acting on the original isomorphism adds the image of the acting coefficient to the new
coefficient. Compatibility with restriction is encoded by the sheaf morphism `u`. -/
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
      (P.sheaf ◁
        (abelianSheafToGrpSheafForgetIso ((J.overPullback AddCommGrpCat.{v'} U).obj B)).inv ≫ u)
      (fun T g p c ↦ by
        let EA : Multiplicative (A.obj.obj (op T.unop.left)) ≃* _ :=
          abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
        let E : Multiplicative (B.obj.obj (op T.unop.left)) ≃* _ :=
          abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
        obtain ⟨a, rfl⟩ := EA.surjective g
        obtain ⟨c, rfl⟩ := E.surjective c
        -- The tensor section is a pair; explicitly select the right action on its coefficient.
        change u.hom.app T
          (EA a • p, (abelianSheafToGrpSheafForgetIso
            ((J.overPullback AddCommGrpCat.{v'} U).obj B)).inv.hom.app T
              (@SMul.smul _ ((Sheaf.MulActionSheaf.mulRight ψ).sheaf.obj.obj T)
                ((Sheaf.MulActionSheaf.mulRight ψ).mulAction T).toSMul (EA a) (E c))) =
          u.hom.app T (p, (abelianSheafToGrpSheafForgetIso
            ((J.overPullback AddCommGrpCat.{v'} U).obj B)).inv.hom.app T (E c))
        erw [coefficient_mulRight_smul,
          abelianSheafToGrpSheafForgetIso_inv_app,
          b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a.toAdd p,
          MulEquiv.symm_apply_apply, hu, sub_add_cancel]
        rfl)

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
  dsimp only [changeBandHomPairing, changeBandHomDesc]
  rw [← Sheaf.Torsor.toContractedProduct_contractedProductMulRightIso_hom]
  -- The torsor sheaf projection and the Hom sheaf have different unreduced types;
  -- association must elaborate through this projection before categorical simplification.
  erw [Category.assoc, Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  erw [Sheaf.Torsor.toContractedProduct_contractedProductDesc]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]
  exact Category.id_comp (obj := Sheaf (J.over U) (Type v')) u

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
