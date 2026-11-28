/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.ChangeBand.Composition
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor.RestrictionComparison

/-!
# Restriction of extended isomorphism torsors

Extension of an abelian band commutes with restriction to a smaller slice site.
The comparison takes a representative `[p, c]` to `[p|, c]`, where `p|` includes the
composition constraints of the original pseudofunctor. It is an isomorphism of sheaves
and preserves the coefficient action, composition and identity sections. These comparisons
allow the fixed-slice
changed-band groupoids to be related along arrows of the site.

The construction uses the torsor extension/restriction comparison, with the actual
isomorphism torsor of the pulled-back objects as the restricted torsor.

## References

* Martin Olsson, *Stacks* (lecture notes), Theorem 31.7.
* J. Giraud, *Cohomologie non abélienne*, III, §1.3.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {A B : Sheaf J AddCommGrpCat.{v'}}
  (b : F.AbelianBanding J A) [F.IsGerbe J]
  (φ : A ⟶ B) {U V : C} (f : V ⟶ U)
  (x y : F.obj (.mk (op U)))

omit [F.IsGerbe J] in
private lemma restriction_inv_homAct (T : (Over V)ᵒᵖ)
    (a : Multiplicative (A.obj.obj (op T.unop.left)))
    (p : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj x)
      ((F.map f.op.toLoc).toFunctor.obj y)).obj T) :
    (F.overMapCompPresheafHomIso x y f).inv.app T (b.homAct p a) =
      b.homAct ((F.overMapCompPresheafHomIso x y f).inv.app T p) a := by
  apply (ConcreteCategory.bijective_of_isIso
    ((F.overMapCompPresheafHomIso x y f).hom.app T)).1
  rw [b.overMapCompPresheafHomIso_hom_app_homAct]
  simp only [← types_comp_apply, ← NatTrans.comp_app, Iso.inv_hom_id]
  rfl

private lemma restriction_inv_smul (T : (Over V)ᵒᵖ)
    (a : ((abelianSheafToGrpSheaf (J.over V)).obj
      ((J.overPullback AddCommGrpCat V).obj A)).obj.obj T)
    (p : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj x)
      ((F.map f.op.toLoc).toFunctor.obj y)).obj T) :
    (F.overMapCompPresheafHomIso x y f).inv.app T
        (((b.sheafHomTorsor ((F.map f.op.toLoc).toFunctor.obj x)
          ((F.map f.op.toLoc).toFunctor.obj y) (IsGerbe.exists_covering_iso _ _)).mulAction
          T).smul a p) =
      ((b.sheafHomTorsor x y (IsGerbe.exists_covering_iso x y)).mulAction
        ((Over.map f).op.obj T)).smul a ((F.overMapCompPresheafHomIso x y f).inv.app T p) :=
  (congrArg ((F.overMapCompPresheafHomIso x y f).inv.app T)
    (b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso _ _) a p)).trans
      ((b.restriction_inv_homAct f x y T _ p).trans
        (b.sheafHomTorsor_smul (T := (Over.map f).op.obj T)
          (IsGerbe.exists_covering_iso x y) a _).symm)

variable [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')]
  [HasWeakSheafify (J.over V) (Type v')]
  [(J.over V).WEqualsLocallyBijective (Type v')]

private def restrictionComparison :=
  let e : (J.overMapPullback (Type v') f).obj (F.sheafHom J x y) ≅
      F.sheafHom J ((F.map f.op.toLoc).toFunctor.obj x)
        ((F.map f.op.toLoc).toFunctor.obj y) :=
    (fullyFaithfulSheafToPresheaf (J.over V) (Type v')).preimageIso
      (F.overMapCompPresheafHomIso x y f)
  let P' := b.sheafHomTorsor ((F.map f.op.toLoc).toFunctor.obj x)
    ((F.map f.op.toLoc).toFunctor.obj y) (IsGerbe.exists_covering_iso _ _)
  Sheaf.Torsor.mapRestrictIso (K := J.over V) (Over.map f)
    (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso x y))
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ))
    P'
    e.inv (b.restriction_inv_smul f x y)

/-- Restricting an extended isomorphism sheaf to `Over V` is the extended isomorphism
sheaf of the pulled-back objects. -/
def changeBandHomRestrictionIso :
    (J.overMapPullback (Type v') f).obj
        ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ≅
      ((b.changeBandHomFunctor φ V).obj
        (op ((F.map f.op.toLoc).toFunctor.obj x),
          (F.map f.op.toLoc).toFunctor.obj y)).sheaf :=
  { hom := (b.restrictionComparison φ f x y).inv.hom
    inv := (b.restrictionComparison φ f x y).hom.hom
    hom_inv_id := congrArg Sheaf.Torsor.Hom.hom (b.restrictionComparison φ f x y).inv_hom_id
    inv_hom_id := congrArg Sheaf.Torsor.Hom.hom (b.restrictionComparison φ f x y).hom_inv_id }

/-- The inverse comparison sends an original pulled-back arrow to the restriction of
its original representative before extension. -/
@[simp]
lemma changeBandHomRestrictionIso_inv_toMap (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj x)
      ((F.map f.op.toLoc).toFunctor.obj y)).obj T) :
    (b.changeBandHomRestrictionIso φ f x y).inv.hom.app T
        ((b.toChangeBandHom φ _ _).hom.app T p) =
      (b.toChangeBandHom φ x y).hom.app ((Over.map f).op.obj T)
        ((F.overMapCompPresheafHomIso x y f).inv.app T p) := by
  let e : (J.overMapPullback (Type v') f).obj (F.sheafHom J x y) ≅
      F.sheafHom J ((F.map f.op.toLoc).toFunctor.obj x)
        ((F.map f.op.toLoc).toFunctor.obj y) :=
    (fullyFaithfulSheafToPresheaf (J.over V) (Type v')).preimageIso
      (F.overMapCompPresheafHomIso x y f)
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso x y)
  let P' := b.sheafHomTorsor ((F.map f.op.toLoc).toFunctor.obj x)
    ((F.map f.op.toLoc).toFunctor.obj y) (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat U).map φ)
  rw [toChangeBandHom_def, toChangeBandHom_def]
  -- The sheaf lift and the sectionwise compositions are hidden behind their API;
  -- state the composite of sheaf morphisms to apply the generator equation.
  change ((P'.toMap ((J.overMapPullback GrpCat f).map ψ)) ≫
      (b.restrictionComparison φ f x y).hom.hom).hom.app T p =
    (e.inv ≫
      (J.overMapPullback (Type v') f).map (P.toMap ψ)).hom.app T p
  exact congrArg (fun k ↦ k.hom.app T p)
    (P.toMap_mapRestrictIso_hom (K := J.over V) (Over.map f) ψ P'
      e.inv (b.restriction_inv_smul f x y))

/-- The comparison commutes with the positive action of the new band. -/
lemma changeBandHomRestrictionIso_hom_smul (T : (Over V)ᵒᵖ)
    (a : Multiplicative (B.obj.obj (op T.unop.left)))
    (s : ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.obj
      ((Over.map f).op.obj T)) :
    (b.changeBandHomRestrictionIso φ f x y).hom.hom.app T
        (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B)
          ((Over.map f).op.obj T) a • s) =
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat V).obj B) T a •
        (b.changeBandHomRestrictionIso φ f x y).hom.hom.app T s :=
  (b.restrictionComparison φ f x y).inv.map_smul T _ s

/-- The inverse comparison also commutes with the positive band action. -/
lemma changeBandHomRestrictionIso_inv_smul (T : (Over V)ᵒᵖ)
    (a : Multiplicative (B.obj.obj (op T.unop.left)))
    (s : ((b.changeBandHomFunctor φ V).obj
      (op ((F.map f.op.toLoc).toFunctor.obj x),
        (F.map f.op.toLoc).toFunctor.obj y)).sheaf.obj.obj T) :
    (b.changeBandHomRestrictionIso φ f x y).inv.hom.app T
        (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat V).obj B) T a • s) =
      (((b.changeBandHomFunctor φ U).obj (op x, y)).mulAction
        ((Over.map f).op.obj T)).smul
          (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B)
            ((Over.map f).op.obj T) a)
          ((b.changeBandHomRestrictionIso φ f x y).inv.hom.app T s) :=
  (b.restrictionComparison φ f x y).hom.map_smul T _ s

/-- The comparison intertwines the two canonical maps into extension of the band. -/
@[simp]
lemma changeBandHomRestrictionIso_hom_toMap (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom x y).obj (op ((Over.map f).obj T.unop))) :
    (b.changeBandHomRestrictionIso φ f x y).hom.hom.app T
        ((b.toChangeBandHom φ x y).hom.app (op ((Over.map f).obj T.unop)) p) =
      (b.toChangeBandHom φ _ _).hom.app T
        ((F.overMapCompPresheafHomIso x y f).hom.app T p) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((b.changeBandHomRestrictionIso φ f x y).inv.hom.app T)).1
  rw [changeBandHomRestrictionIso_inv_toMap]
  have h₁ := congrArg (fun k ↦ k.hom.app T
    ((b.toChangeBandHom φ x y).hom.app ((Over.map f).op.obj T) p))
      (b.changeBandHomRestrictionIso φ f x y).hom_inv_id
  have h₂ := congrArg (fun k ↦ k.app T p)
    (F.overMapCompPresheafHomIso x y f).hom_inv_id
  exact h₁.trans (congrArg ((b.toChangeBandHom φ x y).hom.app
    ((Over.map f).op.obj T)) h₂).symm

/-- Restriction of an extended representative includes the original pseudofunctor's
composition comparison and leaves the coefficient unchanged. -/
@[simp]
lemma changeBandHomRestrictionIso_hom_mk (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom x y).obj ((Over.map f).op.obj T))
    (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomRestrictionIso φ f x y).hom.hom.app T
        (b.changeBandHomMk φ p c) =
      b.changeBandHomMk φ ((F.overMapCompPresheafHomIso x y f).hom.app T p) c := by
  rw [changeBandHomMk_def, changeBandHomMk_def]
  exact (b.changeBandHomRestrictionIso_hom_smul φ f x y T (.ofAdd c) _).trans
    (congrArg (abelianSheafToGrpSheafObjEquiv
      ((J.overPullback AddCommGrpCat V).obj B) T (.ofAdd c) • ·)
      (b.changeBandHomRestrictionIso_hom_toMap φ f x y T p))

/-- The inverse comparison has the corresponding formula on representatives. -/
@[simp]
lemma changeBandHomRestrictionIso_inv_mk (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj x)
      ((F.map f.op.toLoc).toFunctor.obj y)).obj T)
    (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomRestrictionIso φ f x y).inv.hom.app T
        (b.changeBandHomMk φ p c) =
      b.changeBandHomMk φ ((F.overMapCompPresheafHomIso x y f).inv.app T p) c := by
  rw [changeBandHomMk_def, changeBandHomMk_def]
  exact (b.changeBandHomRestrictionIso_inv_smul φ f x y T (.ofAdd c) _).trans
    (congrArg ((((b.changeBandHomFunctor φ U).obj (op x, y)).mulAction
      ((Over.map f).op.obj T)).smul
        (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B)
          ((Over.map f).op.obj T) (.ofAdd c)))
      (b.changeBandHomRestrictionIso_inv_toMap φ f x y T p))

variable (z : F.obj (.mk (op U)))

private lemma restriction_inv_comp_mk (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj x)
      ((F.map f.op.toLoc).toFunctor.obj y)).obj T)
    (q : (F.presheafHom ((F.map f.op.toLoc).toFunctor.obj y)
      ((F.map f.op.toLoc).toFunctor.obj z)).obj T)
    (c d : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomRestrictionIso φ f x z).inv.hom.app T
        ((b.changeBandComp φ _ _ _).hom.app T
          (b.changeBandHomMk φ p c, b.changeBandHomMk φ q d)) =
      (b.changeBandComp φ x y z).hom.app ((Over.map f).op.obj T)
        ((b.changeBandHomRestrictionIso φ f x y).inv.hom.app T (b.changeBandHomMk φ p c),
          (b.changeBandHomRestrictionIso φ f y z).inv.hom.app T
            (b.changeBandHomMk φ q d)) := by
  rw [b.changeBandComp_mk φ, b.changeBandHomRestrictionIso_inv_mk,
    b.changeBandHomRestrictionIso_inv_mk, b.changeBandHomRestrictionIso_inv_mk,
    b.changeBandComp_mk φ]
  congr 1
  -- Mathlib's inverse comparison is conjugation by the composition constraints.
  let e := Cat.Hom.toNatIso (F.mapComp' f.op.toLoc T.unop.hom.op.toLoc
    ((Over.map f).obj T.unop).hom.op.toLoc)
  exact Iso.homCongr_comp (e.app x).symm (e.app y).symm (e.app z).symm p q

/-- Slice restriction preserves composition of all extended arrows. -/
lemma changeBandHomRestrictionIso_inv_comp (T : (Over V)ᵒᵖ)
    (s : ((b.changeBandHomFunctor φ V).obj
      (op ((F.map f.op.toLoc).toFunctor.obj x),
        (F.map f.op.toLoc).toFunctor.obj y)).sheaf.obj.obj T)
    (t : ((b.changeBandHomFunctor φ V).obj
      (op ((F.map f.op.toLoc).toFunctor.obj y),
        (F.map f.op.toLoc).toFunctor.obj z)).sheaf.obj.obj T) :
    (b.changeBandHomRestrictionIso φ f x z).inv.hom.app T
        ((b.changeBandComp φ _ _ _).hom.app T (s, t)) =
      (b.changeBandComp φ x y z).hom.app ((Over.map f).op.obj T)
        ((b.changeBandHomRestrictionIso φ f x y).inv.hom.app T s,
          (b.changeBandHomRestrictionIso φ f y z).inv.hom.app T t) := by
  let x' := (F.map f.op.toLoc).toFunctor.obj x
  let y' := (F.map f.op.toLoc).toFunctor.obj y
  let z' := (F.map f.op.toLoc).toFunctor.obj z
  let L := b.changeBandComp φ x' y' z' ≫ (b.changeBandHomRestrictionIso φ f x z).inv
  let R := ((b.changeBandHomRestrictionIso φ f x y).inv ⊗ₘ
    (b.changeBandHomRestrictionIso φ f y z).inv) ≫
      (J.overMapPullback (Type v') f).map (b.changeBandComp φ x y z)
  have h : L = R := by
    let k := b.changeBandHomPairing φ x' y' ⊗ₘ b.changeBandHomPairing φ y' z'
    have : Sheaf.IsLocallySurjective k := by
      -- The cartesian tensor of sheaf maps has the pointwise product of their components.
      change Presheaf.IsLocallySurjective (J.over V)
        ((b.changeBandHomPairing φ x' y').hom ⊗ₘ
          (b.changeBandHomPairing φ y' z').hom)
      infer_instance
    apply (cancel_epi k).1
    ext W ⟨⟨p, c⟩, ⟨q, d⟩⟩
    -- Evaluate the tensor maps on pairs before applying the representative formula.
    change (b.changeBandHomRestrictionIso φ f x z).inv.hom.app W
        ((b.changeBandComp φ x' y' z').hom.app W
          ((b.changeBandHomPairing φ x' y').hom.app W (p, c),
            (b.changeBandHomPairing φ y' z').hom.app W (q, d))) =
      (b.changeBandComp φ x y z).hom.app ((Over.map f).op.obj W)
        ((b.changeBandHomRestrictionIso φ f x y).inv.hom.app W
          ((b.changeBandHomPairing φ x' y').hom.app W (p, c)),
          (b.changeBandHomRestrictionIso φ f y z).inv.hom.app W
            ((b.changeBandHomPairing φ y' z').hom.app W (q, d)))
    erw [b.changeBandHomPairing_hom_app, b.changeBandHomPairing_hom_app]
    exact b.restriction_inv_comp_mk φ f x y z W p q c d
  exact congrArg (fun k ↦ k.hom.app T (s, t)) h

omit y z in
/-- The inverse comparison preserves the identity section. -/
lemma changeBandHomRestrictionIso_inv_id (T : (Over V)ᵒᵖ) :
    (b.changeBandHomRestrictionIso φ f x x).inv.hom.app T
        ((b.changeBandId φ ((F.map f.op.toLoc).toFunctor.obj x)).hom.app T PUnit.unit) =
      (b.changeBandId φ x).hom.app ((Over.map f).op.obj T) PUnit.unit := by
  rw [b.changeBandId_app, b.changeBandHomRestrictionIso_inv_toMap, b.changeBandId_app]
  congr 1
  rw [overMapCompPresheafHomIso_inv_app]
  simp
  rfl

/-- The forward restriction comparison preserves composition. -/
lemma changeBandHomRestrictionIso_hom_comp (T : (Over V)ᵒᵖ)
    (s : ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.obj
      ((Over.map f).op.obj T))
    (t : ((b.changeBandHomFunctor φ U).obj (op y, z)).sheaf.obj.obj
      ((Over.map f).op.obj T)) :
    (b.changeBandHomRestrictionIso φ f x z).hom.hom.app T
        ((b.changeBandComp φ x y z).hom.app ((Over.map f).op.obj T) (s, t)) =
      (b.changeBandComp φ _ _ _).hom.app T
        ((b.changeBandHomRestrictionIso φ f x y).hom.hom.app T s,
          (b.changeBandHomRestrictionIso φ f y z).hom.hom.app T t) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((b.changeBandHomRestrictionIso φ f x z).inv.hom.app T)).1
  rw [b.changeBandHomRestrictionIso_inv_comp φ f x y z]
  have h₁ := congrArg (fun k ↦ k.hom.app T
    ((b.changeBandComp φ x y z).hom.app ((Over.map f).op.obj T) (s, t)))
      (b.changeBandHomRestrictionIso φ f x z).hom_inv_id
  have h₂ := congrArg (fun k ↦ k.hom.app T s)
    (b.changeBandHomRestrictionIso φ f x y).hom_inv_id
  have h₃ := congrArg (fun k ↦ k.hom.app T t)
    (b.changeBandHomRestrictionIso φ f y z).hom_inv_id
  exact h₁.trans (congrArg ((b.changeBandComp φ x y z).hom.app
    ((Over.map f).op.obj T)) (Prod.ext h₂ h₃)).symm

omit y z in
/-- The forward comparison preserves the identity section. -/
lemma changeBandHomRestrictionIso_hom_id (T : (Over V)ᵒᵖ) :
    (b.changeBandHomRestrictionIso φ f x x).hom.hom.app T
        ((b.changeBandId φ x).hom.app ((Over.map f).op.obj T) PUnit.unit) =
      (b.changeBandId φ ((F.map f.op.toLoc).toFunctor.obj x)).hom.app T PUnit.unit := by
  apply (ConcreteCategory.bijective_of_isIso
    ((b.changeBandHomRestrictionIso φ f x x).inv.hom.app T)).1
  rw [b.changeBandHomRestrictionIso_inv_id]
  exact congrArg (fun k ↦ k.hom.app T
    ((b.changeBandId φ x).hom.app ((Over.map f).op.obj T) PUnit.unit))
      (b.changeBandHomRestrictionIso φ f x x).hom_inv_id

end CategoryTheory.Pseudofunctor.AbelianBanding
