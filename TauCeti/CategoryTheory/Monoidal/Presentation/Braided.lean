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

Given a tensor signature `S` and a family of typed equations `R : HomRel S.FreeBraided` between
morphisms of the free braided monoidal category on `S`, the presented braided monoidal category
`TensorSignature.PresentedBraided S R` is the quotient of `S.FreeBraided` by the monoidal closure
`HomRel.MonoidalClosure R`, equipped with the descended monoidal and braided structures of
`CategoryTheory.Quotient`.

An interpretation of `S` into an arbitrary (not necessarily strict) braided monoidal category `D`
descends to a strong braided functor out of `S.PresentedBraided R` if and only if its extension
`FreeBraided.lift fo fc` identifies all pairs related by `R` (`PresentedBraided.lift` and
`PresentedBraided.factors_iff`). Two strong braided functors out of `S.PresentedBraided R` agreeing
up to isomorphism on the generating objects, compatibly with the coupons, are isomorphic by a
unique monoidal natural isomorphism (`PresentedBraided.monoidalNatIso` and
`PresentedBraided.natTrans_ext`). Finally, a braided substitution `σ : BraidedSubstitution S T`
descends to a strong braided functor `PresentedBraided.mapSubst` between braided presentations
whenever it carries each defining equation of `R` to an equation holding in `T.PresentedBraided R'`.

## Main definitions and results

* `TauCeti.TensorSignature.PresentedBraided S R` and `PresentedBraided.quotientFunctor R`: the
  braided monoidal category presented by `S` and `R`, and the strict braided quotient functor from
  `S.FreeBraided`.
* `PresentedBraided.lift` and `PresentedBraided.factors_iff`: universal property for strong braided
  functors into arbitrary braided monoidal targets.
* `PresentedBraided.natTrans_ext` and `PresentedBraided.monoidalNatIso`: uniqueness of strong
  braided functors out of `S.PresentedBraided R` up to unique monoidal natural isomorphism.
* `PresentedBraided.mapSubst`: descent of a `BraidedSubstitution` to a strong braided functor
  between presented braided monoidal categories.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §3.3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v})

/-- The braided monoidal category presented by a tensor signature `S` and a family of typed
equations `R` between morphisms of `S.FreeBraided`: the quotient of `S.FreeBraided` by the least
congruence containing `R` and closed under whiskering on either side. -/
abbrev PresentedBraided (R : HomRel S.FreeBraided) : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace PresentedBraided

variable {S}

/-- The quotient functor from the free braided monoidal category on `S` onto the braided monoidal
category presented by `S` and `R`. It is strict monoidal and braided for the descended
structures. -/
abbrev quotientFunctor (R : HomRel S.FreeBraided) : S.FreeBraided ⥤ S.PresentedBraided R :=
  CategoryTheory.Quotient.functor _

variable {R : HomRel S.FreeBraided}

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

-- Exposed so that the object part reduces on `𝟙_` and `⊗`, allowing `lift_ε`, `lift_η`, `lift_μ`
-- and `lift_δ` to be stated directly against `𝟙 _`, matching `Presented.lift`.
/-- The strong braided functor out of `S.PresentedBraided R` determined by object images `fo` and
coupon images `fc` when `FreeBraided.lift fo fc` respects every equation in `R`. -/
@[expose] def lift : S.PresentedBraided R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeBraided.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (lift fo fc h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- Restricting `lift fo fc h` along `quotientFunctor R` recovers `FreeBraided.lift fo fc`. -/
theorem quotientFunctor_comp_lift : quotientFunctor R ⋙ lift fo fc h = FreeBraided.lift fo fc :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem lift_obj (X : S.FreeBraided) :
    (lift fo fc h).obj ((quotientFunctor R).obj X) = (FreeBraided.lift fo fc).obj X :=
  (rfl)

@[simp]
theorem lift_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (lift fo fc h).map ((quotientFunctor R).map f) = (FreeBraided.lift fo fc).map f :=
  (rfl)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (FreeBraided.lift_ε fo fc)

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (FreeBraided.lift_η fo fc)

@[simp]
theorem lift_μ (X Y : S.PresentedBraided R) : Functor.LaxMonoidal.μ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (FreeBraided.lift_μ fo fc X.as Y.as)

@[simp]
theorem lift_δ (X Y : S.PresentedBraided R) : Functor.OplaxMonoidal.δ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (FreeBraided.lift_δ fo fc X.as Y.as)

/-- An interpretation `(fo, fc)` into `D` factors through `quotientFunctor R` if and only if
`FreeBraided.lift fo fc` identifies every pair of morphisms related by `R`. -/
theorem factors_iff :
    (∃ G : S.PresentedBraided R ⥤ D, quotientFunctor R ⋙ G = FreeBraided.lift fo fc) ↔
      ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g := by
  constructor
  · rintro ⟨G, hG⟩ X Y f g hfg
    rw [← hG, Functor.comp_map, Functor.comp_map, sound hfg]
  · intro hR
    exact ⟨lift fo fc hR, quotientFunctor_comp_lift fo fc hR⟩

end Lift

section Uniqueness

section Monoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.PresentedBraided R`
to a lax monoidal one is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.PresentedBraided R ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeBraided.natTrans_ext h)

end Monoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (F G : S.PresentedBraided R ⥤ D) [F.Braided] [G.Braided]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong braided functors out of `S.PresentedBraided R` that agree up to isomorphisms `e` on
the generating objects, compatibly with every coupon via `FreeBraided.wordIso`, are isomorphic by a
monoidal natural isomorphism extending `e`. -/
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

@[simp]
theorem monoidalNatIso_inv_app (X : S.FreeBraided) :
    (monoidalNatIso F G e he).inv.app ((quotientFunctor R).obj X) =
      (FreeBraided.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e X.as).inv :=
  FreeBraided.monoidalNatIso_inv_app he X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj (.of a)) = (e a).hom :=
  FreeBraided.monoidalNatIso_hom_app_of he a

theorem monoidalNatIso_inv_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).inv.app ((quotientFunctor R).obj (.of a)) = (e a).inv :=
  FreeBraided.monoidalNatIso_inv_app_of he a

instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.natTransLift _ (FreeBraided.monoidalNatIso he).hom))

end Uniqueness

section Substitution

variable {T : TensorSignature.{u', v'}} {R' : HomRel T.FreeBraided}
  (σ : BraidedSubstitution S T)
  (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (quotientFunctor R').map (σ.toFunctor.map f) = (quotientFunctor R').map (σ.toFunctor.map g))

-- Exposed so that `(mapSubst σ h).obj` reduces on `𝟙_` and `⊗`, allowing `mapSubst_ε`,
-- `mapSubst_η`, `mapSubst_μ` and `mapSubst_δ` to be stated directly against `𝟙 _`.
/-- Descend a braided substitution `σ : BraidedSubstitution S T` to a strong braided functor
`S.PresentedBraided R ⥤ T.PresentedBraided R'` when `σ` sends every defining equation in `R` to an
equation holding in `T.PresentedBraided R'`. -/
@[expose] def mapSubst : S.PresentedBraided R ⥤ T.PresentedBraided R' :=
  CategoryTheory.Quotient.lift _ (σ.toFunctor ⋙ quotientFunctor R') fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq (F := σ.toFunctor ⋙ quotientFunctor R') h hfg

instance : (mapSubst σ h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (mapSubst σ h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- `mapSubst σ h` commutes with the quotient functors and `σ.toFunctor`. -/
theorem quotientFunctor_comp_mapSubst :
    quotientFunctor R ⋙ mapSubst σ h = σ.toFunctor ⋙ quotientFunctor R' :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem mapSubst_obj (X : S.FreeBraided) :
    (mapSubst σ h).obj ((quotientFunctor R).obj X) = (quotientFunctor R').obj (σ.toFunctor.obj X) :=
  (rfl)

@[simp]
theorem mapSubst_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (mapSubst σ h).map ((quotientFunctor R).map f) = (quotientFunctor R').map (σ.toFunctor.map f) :=
  (rfl)

@[simp]
theorem mapSubst_ε : Functor.LaxMonoidal.ε (mapSubst σ h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans <| by
    simp only [Functor.LaxMonoidal.comp_ε, CategoryTheory.Quotient.functor_ε,
      BraidedSubstitution.toFunctor_ε, Category.id_comp]
    exact (quotientFunctor R').map_id _

@[simp]
theorem mapSubst_η : Functor.OplaxMonoidal.η (mapSubst σ h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans <| by
    simp only [Functor.OplaxMonoidal.comp_η, CategoryTheory.Quotient.functor_η,
      BraidedSubstitution.toFunctor_η, Category.comp_id]
    exact (quotientFunctor R').map_id _

@[simp]
theorem mapSubst_μ (X Y : S.PresentedBraided R) :
    Functor.LaxMonoidal.μ (mapSubst σ h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans <| by
    simp only [Functor.LaxMonoidal.comp_μ, CategoryTheory.Quotient.functor_μ,
      BraidedSubstitution.toFunctor_μ]
    exact (Category.id_comp _).trans ((quotientFunctor R').map_id _)

@[simp]
theorem mapSubst_δ (X Y : S.PresentedBraided R) :
    Functor.OplaxMonoidal.δ (mapSubst σ h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans <| by
    simp only [Functor.OplaxMonoidal.comp_δ, CategoryTheory.Quotient.functor_δ,
      BraidedSubstitution.toFunctor_δ, Category.comp_id]
    exact (quotientFunctor R').map_id _

end Substitution

end PresentedBraided

end TauCeti.TensorSignature
