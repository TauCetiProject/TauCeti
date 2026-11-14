/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Substitution
public import TauCeti.CategoryTheory.Quotient.Braided

/-!
# Braided monoidal categories presented by generators and relations

A *braided presentation* consists of a tensor signature `S` (generating objects and coupons between
formal tensor words) together with a family `R : HomRel S.FreeBraided` of typed equations between
morphisms of the free braided monoidal category on `S`. Because braided monoidal categories add no
extra unary operations on morphisms beyond composition and whiskering, the least braided monoidal
congruence containing `R` is the quotient congruence of `HomRel.MonoidalClosure R` on
`S.FreeBraided`. Thus `S.PresentedBraided R` reuses
`CategoryTheory.Quotient (HomRel.MonoidalClosure R)` directly, following
`TauCeti.CategoryTheory.Monoidal.Presentation` and inheriting its `MonoidalCategory` and
`BraidedCategory` instances from `TauCeti.CategoryTheory.Quotient.Monoidal` and
`TauCeti.CategoryTheory.Quotient.Braided`.

Only the braided monoidal axioms and the equations `R` are imposed; in particular, neither symmetry
nor unstated coupon relations hold unless entailed by `R`.

## Main definitions and results

* `TauCeti.TensorSignature.PresentedBraided S R`: the braided monoidal category presented by `S`
  and `R`, with strict braided quotient functor `PresentedBraided.quotientFunctor R` and soundness
  `PresentedBraided.sound`.
* `PresentedBraided.lift fo fc h`: the strong braided functor into an arbitrary (not necessarily
  strict) braided monoidal category `D` determined by generator images satisfying `R`, together
  with the exact descent criterion `PresentedBraided.exists_braided_lift_iff`.
* `PresentedBraided.monoidalNatIso` and `PresentedBraided.natTrans_ext`: uniqueness of braided
  lifts up to a unique monoidal natural isomorphism extending given isomorphisms on generators.
* `PresentedBraided.iteratedQuotientEquiv`: quotienting `S.PresentedBraided R₁` further by the
  monoidal closure of a second family `R₂` is braided monoidally equivalent to presenting `S` by
  both families simultaneously.
* `BraidedSubstitution.mapPresented`: a braided substitution sending defining equations of `R` to
  equations holding in `T.PresentedBraided R'` descends to a strong braided functor
  `S.PresentedBraided R ⥤ T.PresentedBraided R'`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Physics 813 (2011), §3.3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (R : HomRel S.FreeBraided)

/-- The braided monoidal category presented by the tensor signature `S` and the equations `R`
between morphisms of `S.FreeBraided`: the quotient of `S.FreeBraided` by the least monoidal
congruence containing `R`, equipped with the descended braided monoidal structure. -/
abbrev PresentedBraided : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace PresentedBraided

variable {S}

/-- The quotient functor from `S.FreeBraided` onto `S.PresentedBraided R`. It is strict braided
monoidal for the descended braided monoidal structure. -/
abbrev quotientFunctor : S.FreeBraided ⥤ S.PresentedBraided R :=
  CategoryTheory.Quotient.functor _

variable {R}

/-- Every defining equation in `R` holds in `S.PresentedBraided R`. -/
theorem sound {X Y : S.FreeBraided} {f g : X ⟶ Y} (h : R f g) :
    (quotientFunctor R).map f = (quotientFunctor R).map g :=
  CategoryTheory.Quotient.sound _ (.of h)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon,
    FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
  (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g)

/-- The strong braided functor out of `S.PresentedBraided R` determined by the images `fo` of the
generating objects and `fc` of the coupons, provided the free braided interpretation respects
`R`. -/
@[expose] def lift : S.PresentedBraided R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeBraided.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (lift fo fc h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- `lift fo fc h` restricts along `quotientFunctor R` to `FreeBraided.lift fo fc`. -/
theorem quotientFunctor_comp_lift : quotientFunctor R ⋙ lift fo fc h = FreeBraided.lift fo fc :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem lift_obj (X : S.FreeBraided) :
    (lift fo fc h).obj ((quotientFunctor R).obj X) = (FreeBraided.lift fo fc).obj X := (rfl)

@[simp]
theorem lift_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (lift fo fc h).map ((quotientFunctor R).map f) = (FreeBraided.lift fo fc).map f := (rfl)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (FreeBraided.lift_ε fo fc)

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (FreeBraided.lift_η fo fc)

@[simp]
theorem lift_μ (X Y : S.PresentedBraided R) :
    Functor.LaxMonoidal.μ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (FreeBraided.lift_μ fo fc X.as Y.as)

@[simp]
theorem lift_δ (X Y : S.PresentedBraided R) :
    Functor.OplaxMonoidal.δ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (FreeBraided.lift_δ fo fc X.as Y.as)

/-- A free braided interpretation `FreeBraided.lift fo fc` factors up to monoidal natural
isomorphism through a strong braided functor out of `S.PresentedBraided R` if and only if it
respects every defining equation in `R`. -/
theorem exists_braided_lift_iff (R : HomRel S.FreeBraided) :
    (∃ (F : S.PresentedBraided R ⥤ D) (_ : F.Braided)
      (e : quotientFunctor R ⋙ F ≅ FreeBraided.lift fo fc), NatTrans.IsMonoidal e.hom) ↔
    ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g := by
  constructor
  · rintro ⟨F, _, e, _⟩ X Y f g hfg
    rw [← cancel_epi (e.hom.app X), ← e.hom.naturality, Functor.comp_map, sound hfg,
      ← Functor.comp_map, e.hom.naturality]
  · intro hR
    let H : ∀ (X Y : S.FreeBraided) (f₁ f₂ : X ⟶ Y), HomRel.MonoidalClosure R f₁ f₂ →
        (FreeBraided.lift fo fc).map f₁ = (FreeBraided.lift fo fc).map f₂ :=
      fun _ _ _ _ hfg ↦ HomRel.MonoidalClosure.map_eq hR hfg
    exact ⟨CategoryTheory.Quotient.lift _ (FreeBraided.lift fo fc) H, inferInstance,
      CategoryTheory.Quotient.lift.isLift _ _ H, inferInstance⟩

end Lift

section Uniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.PresentedBraided R`
to a lax monoidal one is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.PresentedBraided R ⥤ D} [F.Monoidal] [G.LaxMonoidal]
    {α β : F ⟶ G} [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a,
      α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeBraided.natTrans_ext h)

variable [BraidedCategory D] (F G : S.PresentedBraided R ⥤ D) [F.Braided] [G.Braided]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong braided functors out of `S.PresentedBraided R` that agree up to isomorphisms `e` on
the generating objects, compatibly with every coupon along `FreeBraided.wordIso`, are isomorphic by
a monoidal natural isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map ((quotientFunctor R).map (FreeBraided.coupon g)) ≫
        (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
        G.map ((quotientFunctor R).map (FreeBraided.coupon g))) :
    F ≅ G :=
  CategoryTheory.Quotient.natIsoLift _ (FreeBraided.monoidalNatIso he)

variable {F G e}
  (he : ∀ g, F.map ((quotientFunctor R).map (FreeBraided.coupon g)) ≫
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
    (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
      G.map ((quotientFunctor R).map (FreeBraided.coupon g)))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeBraided) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj X) =
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e X.as).hom :=
  FreeBraided.monoidalNatIso_hom_app he X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj (.of a)) = (e a).hom :=
  FreeBraided.monoidalNatIso_hom_app_of he a

noncomputable instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.natTransLift _ (FreeBraided.monoidalNatIso he).hom))

end Uniqueness

section IteratedQuotient

/-- Pushforward of a second family of relations `R₂` on `S.FreeBraided` to
`S.PresentedBraided R₁` along `quotientFunctor R₁`. -/
inductive PushforwardRel (R₁ R₂ : HomRel S.FreeBraided) : HomRel (S.PresentedBraided R₁)
  | of {X Y : S.FreeBraided} {f g : X ⟶ Y} :
      R₂ f g →
        PushforwardRel R₁ R₂ ((quotientFunctor R₁).map f) ((quotientFunctor R₁).map g)

/-- The union of two relation families on `S.FreeBraided`. -/
@[expose] def unionRel (R₁ R₂ : HomRel S.FreeBraided) : HomRel S.FreeBraided :=
  fun _ _ f g ↦ R₁ f g ∨ R₂ f g

theorem iteratedStep₁_rel (R₁ R₂ : HomRel S.FreeBraided)
    (X Y : S.FreeBraided) (f g : X ⟶ Y) (hfg : HomRel.MonoidalClosure R₁ f g) :
    (quotientFunctor (unionRel R₁ R₂)).map f = (quotientFunctor (unionRel R₁ R₂)).map g :=
  HomRel.MonoidalClosure.map_eq (fun _ _ _ _ h ↦ sound (R := unionRel R₁ R₂) (Or.inl h)) hfg

/-- Auxiliary first-step lift from `S.PresentedBraided R₁` to
`S.PresentedBraided (unionRel R₁ R₂)`. -/
@[expose] def iteratedStep₁ (R₁ R₂ : HomRel S.FreeBraided) :
    S.PresentedBraided R₁ ⥤ S.PresentedBraided (unionRel R₁ R₂) :=
  CategoryTheory.Quotient.lift (HomRel.MonoidalClosure R₁)
    (quotientFunctor (unionRel R₁ R₂)) (iteratedStep₁_rel R₁ R₂)

instance (R₁ R₂ : HomRel S.FreeBraided) : (iteratedStep₁ R₁ R₂).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance (R₁ R₂ : HomRel S.FreeBraided) : (iteratedStep₁ R₁ R₂).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

theorem iteratedToUnion_rel (R₁ R₂ : HomRel S.FreeBraided)
    (X Y : S.PresentedBraided R₁) (f g : X ⟶ Y)
    (hfg : HomRel.MonoidalClosure (PushforwardRel R₁ R₂) f g) :
    (iteratedStep₁ R₁ R₂).map f = (iteratedStep₁ R₁ R₂).map g :=
  HomRel.MonoidalClosure.map_eq (F := iteratedStep₁ R₁ R₂)
    (by rintro _ _ _ _ ⟨h⟩; exact sound (R := unionRel R₁ R₂) (Or.inr h)) hfg

/-- First quotienting `S.FreeBraided` by `R₁` and then quotienting by the monoidal closure of
`R₂` maps strictly and braided-monoidally to `S.PresentedBraided (unionRel R₁ R₂)`. -/
@[expose] def iteratedToUnion (R₁ R₂ : HomRel S.FreeBraided) :
    CategoryTheory.Quotient (HomRel.MonoidalClosure (PushforwardRel R₁ R₂)) ⥤
      S.PresentedBraided (unionRel R₁ R₂) :=
  CategoryTheory.Quotient.lift (HomRel.MonoidalClosure (PushforwardRel R₁ R₂))
    (iteratedStep₁ R₁ R₂) (iteratedToUnion_rel R₁ R₂)

instance (R₁ R₂ : HomRel S.FreeBraided) : (iteratedToUnion R₁ R₂).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance (R₁ R₂ : HomRel S.FreeBraided) : (iteratedToUnion R₁ R₂).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

theorem unionToIterated_rel (R₁ R₂ : HomRel S.FreeBraided)
    (X Y : S.FreeBraided) (f g : X ⟶ Y)
    (hfg : HomRel.MonoidalClosure (unionRel R₁ R₂) f g) :
    (quotientFunctor R₁ ⋙
      CategoryTheory.Quotient.functor (HomRel.MonoidalClosure (PushforwardRel R₁ R₂))).map f =
    (quotientFunctor R₁ ⋙
      CategoryTheory.Quotient.functor (HomRel.MonoidalClosure (PushforwardRel R₁ R₂))).map g :=
  HomRel.MonoidalClosure.map_eq
    (F := quotientFunctor R₁ ⋙
      CategoryTheory.Quotient.functor (HomRel.MonoidalClosure (PushforwardRel R₁ R₂)))
    (by
      rintro _ _ _ _ (h₁ | h₂)
      · exact congrArg
          (CategoryTheory.Quotient.functor (HomRel.MonoidalClosure (PushforwardRel R₁ R₂))).map
          (sound h₁)
      · exact CategoryTheory.Quotient.sound _ (.of (.of h₂))) hfg

/-- Presenting `S` by `unionRel R₁ R₂` maps strictly and braided-monoidally to the two-step
quotient of `S.PresentedBraided R₁` by `PushforwardRel R₁ R₂`. -/
@[expose] def unionToIterated (R₁ R₂ : HomRel S.FreeBraided) :
    S.PresentedBraided (unionRel R₁ R₂) ⥤
      CategoryTheory.Quotient (HomRel.MonoidalClosure (PushforwardRel R₁ R₂)) :=
  CategoryTheory.Quotient.lift (HomRel.MonoidalClosure (unionRel R₁ R₂))
    (quotientFunctor R₁ ⋙
      CategoryTheory.Quotient.functor (HomRel.MonoidalClosure (PushforwardRel R₁ R₂)))
    (unionToIterated_rel R₁ R₂)

instance (R₁ R₂ : HomRel S.FreeBraided) : (unionToIterated R₁ R₂).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance (R₁ R₂ : HomRel S.FreeBraided) : (unionToIterated R₁ R₂).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

theorem iteratedQuotientEquiv_unit (R₁ R₂ : HomRel S.FreeBraided)
    (X : CategoryTheory.Quotient (HomRel.MonoidalClosure (PushforwardRel R₁ R₂))) :
    (iteratedToUnion R₁ R₂).map
      ((CategoryTheory.Quotient.natIsoLift _
        (CategoryTheory.Quotient.natIsoLift _ (Iso.refl _)) :
          𝟭 _ ≅ iteratedToUnion R₁ R₂ ⋙ unionToIterated R₁ R₂).hom.app X) ≫
      ((CategoryTheory.Quotient.natIsoLift _ (Iso.refl _) :
        unionToIterated R₁ R₂ ⋙ iteratedToUnion R₁ R₂ ≅ 𝟭 _).hom.app
        ((iteratedToUnion R₁ R₂).obj X)) =
      𝟙 ((iteratedToUnion R₁ R₂).obj X) := by
  rcases X with ⟨⟨_⟩⟩
  exact Category.id_comp _

/-- Quotienting twice (first by `R₁`, then by `R₂`) is equivalent as a braided monoidal category
to adjoining both families `unionRel R₁ R₂` at once. -/
@[expose] def iteratedQuotientEquiv (R₁ R₂ : HomRel S.FreeBraided) :
    CategoryTheory.Quotient (HomRel.MonoidalClosure (PushforwardRel R₁ R₂)) ≌
      S.PresentedBraided (unionRel R₁ R₂) where
  functor := iteratedToUnion R₁ R₂
  inverse := unionToIterated R₁ R₂
  unitIso := CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.natIsoLift _ (Iso.refl _))
  counitIso := CategoryTheory.Quotient.natIsoLift _ (Iso.refl _)
  functor_unitIso_comp := iteratedQuotientEquiv_unit R₁ R₂

@[simp]
theorem iteratedQuotientEquiv_functor (R₁ R₂ : HomRel S.FreeBraided) :
    (iteratedQuotientEquiv R₁ R₂).functor = iteratedToUnion R₁ R₂ := rfl

@[simp]
theorem iteratedQuotientEquiv_inverse (R₁ R₂ : HomRel S.FreeBraided) :
    (iteratedQuotientEquiv R₁ R₂).inverse = unionToIterated R₁ R₂ := rfl

end IteratedQuotient

end PresentedBraided

namespace BraidedSubstitution

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {R : HomRel S.FreeBraided} {R' : HomRel T.FreeBraided}

/-- A braided substitution `σ : BraidedSubstitution S T` that sends every defining equation in `R`
to an equation holding in `T.PresentedBraided R'` descends to a strong braided functor
`S.PresentedBraided R ⥤ T.PresentedBraided R'`. -/
@[expose] def mapPresented (σ : BraidedSubstitution S T)
    (hσ : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) =
        (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map g)) :
    S.PresentedBraided R ⥤ T.PresentedBraided R' :=
  CategoryTheory.Quotient.lift (HomRel.MonoidalClosure R)
    (σ.toFunctor ⋙ PresentedBraided.quotientFunctor R')
    (fun _ _ _ _ hfg ↦ HomRel.MonoidalClosure.map_eq
      (F := σ.toFunctor ⋙ PresentedBraided.quotientFunctor R') hσ hfg)

section MapPresented

variable (σ : BraidedSubstitution S T)
  (hσ : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) =
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map g))

instance : (σ.mapPresented hσ).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (σ.mapPresented hσ).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- `σ.mapPresented hσ` commutes strictly with the quotient functors. -/
theorem quotientFunctor_comp_mapPresented :
    PresentedBraided.quotientFunctor R ⋙ σ.mapPresented hσ =
      σ.toFunctor ⋙ PresentedBraided.quotientFunctor R' :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem mapPresented_obj (X : S.FreeBraided) :
    (σ.mapPresented hσ).obj ((PresentedBraided.quotientFunctor R).obj X) =
      (PresentedBraided.quotientFunctor R').obj (σ.toFunctor.obj X) := (rfl)

@[simp]
theorem mapPresented_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (σ.mapPresented hσ).map ((PresentedBraided.quotientFunctor R).map f) =
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) := (rfl)

@[simp]
theorem mapPresented_ε : Functor.LaxMonoidal.ε (σ.mapPresented hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans
    ((Functor.LaxMonoidal.comp_ε σ.toFunctor (PresentedBraided.quotientFunctor R')).trans
      ((congrArg₂ (· ≫ ·) CategoryTheory.Quotient.functor_ε
        ((congrArg (PresentedBraided.quotientFunctor R').map σ.toFunctor_ε).trans
          (Functor.map_id _ _))).trans (Category.id_comp _)))

@[simp]
theorem mapPresented_η : Functor.OplaxMonoidal.η (σ.mapPresented hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans
    ((Functor.OplaxMonoidal.comp_η σ.toFunctor (PresentedBraided.quotientFunctor R')).trans
      ((congrArg₂ (· ≫ ·)
        ((congrArg (PresentedBraided.quotientFunctor R').map σ.toFunctor_η).trans
          (Functor.map_id _ _))
        CategoryTheory.Quotient.functor_η).trans (Category.comp_id _)))

@[simp]
theorem mapPresented_μ (X Y : S.PresentedBraided R) :
    Functor.LaxMonoidal.μ (σ.mapPresented hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans
    ((Functor.LaxMonoidal.comp_μ
      σ.toFunctor (PresentedBraided.quotientFunctor R') X.as Y.as).trans
      ((congrArg₂ (· ≫ ·) (CategoryTheory.Quotient.functor_μ _ _)
        ((congrArg (PresentedBraided.quotientFunctor R').map (σ.toFunctor_μ X.as Y.as)).trans
          (Functor.map_id _ _))).trans (Category.id_comp _)))

@[simp]
theorem mapPresented_δ (X Y : S.PresentedBraided R) :
    Functor.OplaxMonoidal.δ (σ.mapPresented hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans
    ((Functor.OplaxMonoidal.comp_δ
      σ.toFunctor (PresentedBraided.quotientFunctor R') X.as Y.as).trans
      ((congrArg₂ (· ≫ ·)
        ((congrArg (PresentedBraided.quotientFunctor R').map (σ.toFunctor_δ X.as Y.as)).trans
          (Functor.map_id _ _))
        (CategoryTheory.Quotient.functor_δ _ _)).trans (Category.comp_id _)))

end MapPresented

end BraidedSubstitution

end TauCeti.TensorSignature
