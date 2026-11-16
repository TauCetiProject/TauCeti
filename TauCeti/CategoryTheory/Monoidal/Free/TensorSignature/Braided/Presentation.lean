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

A *braided presentation* consists of a `TauCeti.TensorSignature` `S` together with a family
`R : HomRel S.FreeBraided` of typed equations between morphisms of the free braided monoidal
category on `S`. The braided monoidal category `S.PresentedBraided R` it presents is the quotient
of `S.FreeBraided` by the least monoidal congruence containing `R`: namely
`CategoryTheory.Quotient (HomRel.MonoidalClosure R)` equipped with the descended monoidal and
braided structures from `TauCeti/CategoryTheory/Quotient/Monoidal.lean` and
`TauCeti/CategoryTheory/Quotient/Braided.lean`.

Because the braiding is a family of structural morphisms rather than a new morphism-forming
operation, closing `R` under whiskering and composition suffices for the braiding to descend and
for every braided functor respecting `R` to factor as a braided functor through the quotient.

## Main definitions and results

* `TauCeti.TensorSignature.PresentedBraided S R`: the braided monoidal category presented by `S`
  and `R`, with strict braided quotient functor `PresentedBraided.quotientFunctor R` satisfying
  `PresentedBraided.sound`.
* `PresentedBraided.lift fo fc h`: the strong braided functor into an arbitrary (not necessarily
  strict) braided monoidal category determined by object images `fo` and coupon images `fc`
  satisfying `R`, with `PresentedBraided.quotientFunctor_comp_lift` and computation rules
  `lift_obj`, `lift_map`, `lift_ε`, `lift_η`, `lift_μ`, `lift_δ`.
* `PresentedBraided.monoidalNatIso` and `PresentedBraided.natTrans_ext`: uniqueness of strong
  braided functors out of `S.PresentedBraided R` up to a unique monoidal natural isomorphism
  determined on the generating objects.
* `BraidedSubstitution.toPresentedFunctor`: descent of a braided substitution to a strong braided
  functor between presented braided monoidal categories whenever it sends each defining equation
  to an equation holding in the target presentation, strictly preserving identity and composition
  (`toPresentedFunctor_id`, `toPresentedFunctor_comp`).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
-/

public section

universe u v u' v' u'' v''

open CategoryTheory MonoidalCategory BraidedCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (R : HomRel S.FreeBraided)

/-- The braided monoidal category presented by the tensor signature `S` and the equations `R`
between morphisms of `S.FreeBraided`: the quotient of `S.FreeBraided` by the least monoidal
congruence containing `R`, with the descended braided monoidal structure. -/
abbrev PresentedBraided : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace PresentedBraided

variable {S}

/-- The quotient functor from `S.FreeBraided` onto the braided monoidal category presented by `S`
and `R`. It is strict braided for the descended braided monoidal structure. -/
abbrev quotientFunctor : S.FreeBraided ⥤ S.PresentedBraided R :=
  CategoryTheory.Quotient.functor _

variable {R}

/-- The equations `R` hold in the presented braided monoidal category. -/
theorem sound {X Y : S.FreeBraided} {f g : X ⟶ Y} (h : R f g) :
    (quotientFunctor R).map f = (quotientFunctor R).map g :=
  CategoryTheory.Quotient.sound _ (.of h)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon,
    FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
  (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (FreeBraided.lift fo fc).map f = (FreeBraided.lift fo fc).map g)

/-- The functor out of the braided monoidal category presented by `S` and `R` determined by the
images `fo` of the generating objects and `fc` of the coupons, provided the induced interpretation
of `S.FreeBraided` satisfies `R`. It is strong braided, with identity tensorator and unit
comparison. -/
-- The body is exposed so that the object part reduces, as for `FreeBraided.lift`: the statements
-- of `lift_ε` and its companions only typecheck once objects of the form `(lift fo fc h).obj X`
-- reduce to the corresponding tensor products in `D`.
@[expose] def lift : S.PresentedBraided R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeBraided.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (lift fo fc h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

/-- The functor `lift fo fc h` restricts along the quotient functor to `FreeBraided.lift fo fc`. -/
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

end Lift

section Uniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.PresentedBraided R`
to a lax monoidal one is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.PresentedBraided R ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeBraided.natTrans_ext h)

variable [BraidedCategory D] (F G : S.PresentedBraided R ⥤ D) [F.Braided] [G.Braided]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong braided functors out of the braided monoidal category presented by `S` and `R` that
agree up to isomorphisms `e` on the generating objects, compatibly with every coupon, are
isomorphic by a monoidal natural isomorphism extending `e`. The compatibility is stated with the
isomorphisms `FreeBraided.wordIso` which `e` induces on all tensor words. -/
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

end PresentedBraided

namespace BraidedSubstitution

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}}

/-- A braided substitution descends to a strong braided functor between presented braided monoidal
categories whenever it sends every defining equation of `R` to an equation holding in the target
presentation `R'`. -/
-- The body is exposed so that the object part reduces, as for `PresentedBraided.lift`: the
-- statements of `toPresentedFunctor_ε` and its companions rely on object reduction.
@[expose] def toPresentedFunctor (σ : BraidedSubstitution S T)
    (R : HomRel S.FreeBraided) (R' : HomRel T.FreeBraided)
    (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) =
        (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map g)) :
    S.PresentedBraided R ⥤ T.PresentedBraided R' :=
  CategoryTheory.Quotient.lift _ (σ.toFunctor ⋙ PresentedBraided.quotientFunctor R')
    fun _ _ _ _ hfg ↦
      HomRel.MonoidalClosure.map_eq (F := σ.toFunctor ⋙ PresentedBraided.quotientFunctor R') h hfg

section Descent

variable (σ : BraidedSubstitution S T) (R : HomRel S.FreeBraided) (R' : HomRel T.FreeBraided)
  (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) =
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map g))

instance : (σ.toPresentedFunctor R R' h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

noncomputable instance : (σ.toPresentedFunctor R R' h).Braided :=
  CategoryTheory.Quotient.liftBraided _ _ _

theorem quotientFunctor_comp_toPresentedFunctor :
    PresentedBraided.quotientFunctor R ⋙ σ.toPresentedFunctor R R' h =
      σ.toFunctor ⋙ PresentedBraided.quotientFunctor R' :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem toPresentedFunctor_obj (X : S.FreeBraided) :
    (σ.toPresentedFunctor R R' h).obj ((PresentedBraided.quotientFunctor R).obj X) =
      (PresentedBraided.quotientFunctor R').obj (σ.toFunctor.obj X) :=
  (rfl)

@[simp]
theorem toPresentedFunctor_map {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (σ.toPresentedFunctor R R' h).map ((PresentedBraided.quotientFunctor R).map f) =
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) :=
  (rfl)

@[simp]
theorem toPresentedFunctor_ε : Functor.LaxMonoidal.ε (σ.toPresentedFunctor R R' h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans <| by
    rw [Functor.LaxMonoidal.comp_ε, CategoryTheory.Quotient.functor_ε, toFunctor_ε,
      Category.id_comp]
    exact Functor.map_id _ _

@[simp]
theorem toPresentedFunctor_η : Functor.OplaxMonoidal.η (σ.toPresentedFunctor R R' h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans <| by
    rw [Functor.OplaxMonoidal.comp_η, CategoryTheory.Quotient.functor_η, toFunctor_η,
      Category.comp_id]
    exact Functor.map_id _ _

@[simp]
theorem toPresentedFunctor_μ (X Y : S.PresentedBraided R) :
    Functor.LaxMonoidal.μ (σ.toPresentedFunctor R R' h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans <| by
    rw [Functor.LaxMonoidal.comp_μ, CategoryTheory.Quotient.functor_μ, toFunctor_μ]
    exact (Category.id_comp _).trans (Functor.map_id _ _)

@[simp]
theorem toPresentedFunctor_δ (X Y : S.PresentedBraided R) :
    Functor.OplaxMonoidal.δ (σ.toPresentedFunctor R R' h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans <| by
    rw [Functor.OplaxMonoidal.comp_δ, CategoryTheory.Quotient.functor_δ, toFunctor_δ,
      Category.comp_id]
    exact Functor.map_id _ _

end Descent

/-- The identity substitution descends to the identity functor on any braided presentation. -/
theorem toPresentedFunctor_id (S : TensorSignature.{u, v}) (R : HomRel S.FreeBraided)
    (h : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (PresentedBraided.quotientFunctor R).map ((id S).toFunctor.map f) =
        (PresentedBraided.quotientFunctor R).map ((id S).toFunctor.map g)) :
    (id S).toPresentedFunctor R R h = 𝟭 (S.PresentedBraided R) := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [quotientFunctor_comp_toPresentedFunctor, toFunctor_id, Functor.id_comp, Functor.comp_id]

/-- Descent of braided substitutions strictly preserves composition. -/
theorem toPresentedFunctor_comp (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    (R : HomRel S.FreeBraided) (R' : HomRel T.FreeBraided) (R'' : HomRel U.FreeBraided)
    (hσ : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map f) =
        (PresentedBraided.quotientFunctor R').map (σ.toFunctor.map g))
    (hτ : ∀ ⦃X Y : T.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (PresentedBraided.quotientFunctor R'').map (τ.toFunctor.map f) =
        (PresentedBraided.quotientFunctor R'').map (τ.toFunctor.map g))
    (hστ : ∀ ⦃X Y : S.FreeBraided⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (PresentedBraided.quotientFunctor R'').map ((σ.comp τ).toFunctor.map f) =
        (PresentedBraided.quotientFunctor R'').map ((σ.comp τ).toFunctor.map g)) :
    (σ.comp τ).toPresentedFunctor R R'' hστ =
      σ.toPresentedFunctor R R' hσ ⋙ τ.toPresentedFunctor R' R'' hτ := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [quotientFunctor_comp_toPresentedFunctor, toFunctor_comp, Functor.assoc,
    ← Functor.assoc (PresentedBraided.quotientFunctor R),
    quotientFunctor_comp_toPresentedFunctor, Functor.assoc,
    quotientFunctor_comp_toPresentedFunctor]

end BraidedSubstitution

end TauCeti.TensorSignature
