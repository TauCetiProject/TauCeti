/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution
public import TauCeti.CategoryTheory.Quotient.Monoidal

/-!
# Monoidal categories presented by generators and relations

A *presentation* of a monoidal category consists of a tensor signature `S` (generating objects,
and generating morphisms, or coupons, between tensor words in them) together with a family
`R : HomRel S.FreeMonoidal` of typed equations between morphisms of the free monoidal category
on `S`. The monoidal category `S.Presented R` it presents is the quotient of
`TauCeti.TensorSignature.FreeMonoidal S` by the least congruence which contains `R` and is
compatible with the monoidal structure: the quotient category by the monoidal closure
`HomRel.MonoidalClosure R`, with the monoidal structure descended to it. Only the equations `R`
are imposed beyond the axioms of a monoidal category; with `R` empty, distinct composites of
coupons stay distinct.

Its universal property is that of the free monoidal category restricted to the interpretations
satisfying the equations: a choice of images of the generating objects and coupons in an
arbitrary (not necessarily strict) monoidal category `D` whose induced strong monoidal functor
`TauCeti.TensorSignature.FreeMonoidal.lift` identifies the two sides of every equation of `R`
factors through a strong monoidal functor `S.Presented R ⥤ D`, which is unique up to a unique
monoidal natural isomorphism extending given isomorphisms on the generating objects. Conversely,
any factorization of `FreeMonoidal.lift` through `S.Presented R` (even up to natural isomorphism)
forces every equation of `R` to hold in `D`.

Substitutions `Substitution S T` and signature morphisms `Hom S T` descend to strong monoidal
functors `S.Presented R ⥤ T.Presented R'` whenever the substituted images of every equation in `R`
become equal in `T.Presented R'`. Descended substitutions respect identity and composition up to
canonical monoidal natural isomorphisms (`mapSubstIdIso` and `mapSubstCompIso`), and precomposing a
presentation interpretation `Presented.lift` with a descended substitution is monoidally naturally
isomorphic to `Presented.lift` of the pulled-back generator interpretation (`mapSubstCompLiftIso`).

## Main definitions and results

* `TauCeti.TensorSignature.Presented S R`: the monoidal category presented by `S` and `R`, and
  `TauCeti.TensorSignature.Presented.quotientFunctor R` the strict monoidal quotient functor from
  the free monoidal category, which identifies the two sides of every equation of `R`
  (`TauCeti.TensorSignature.Presented.sound`).
* `TauCeti.TensorSignature.Presented.lift fo fc h`: the strong monoidal functor determined by the
  images `fo` of the generating objects and `fc` of the coupons satisfying the equations, with
  computation rules `TauCeti.TensorSignature.Presented.lift_obj` and
  `TauCeti.TensorSignature.Presented.lift_map`, the factorization
  `TauCeti.TensorSignature.Presented.quotientFunctor_comp_lift`, and the exact `↔` descent
  characterizations `TauCeti.TensorSignature.Presented.exists_lift_iff` and
  `TauCeti.TensorSignature.Presented.exists_iso_lift_iff`.
* `TauCeti.TensorSignature.Presented.monoidalNatIso`: two strong monoidal functors out of
  `S.Presented R` agreeing up to isomorphism on the generating objects, compatibly with the
  coupons, are monoidally naturally isomorphic; `TauCeti.TensorSignature.Presented.natTrans_ext`:
  monoidal natural transformations out of `S.Presented R` are determined by their components at
  the generating objects.
* `TauCeti.TensorSignature.Presented.mapSubst`, `TauCeti.TensorSignature.Presented.mapSubstOfRel`,
  and `TauCeti.TensorSignature.Presented.mapHom`: strong monoidal functors between presented
  monoidal categories descended from substitutions and signature morphisms, with exact `↔`
  characterizations `TauCeti.TensorSignature.Presented.exists_mapSubst_iff` and
  `TauCeti.TensorSignature.Presented.exists_iso_mapSubst_iff`.
* `TauCeti.TensorSignature.Presented.mapSubstIdIso`,
  `TauCeti.TensorSignature.Presented.mapSubstCompIso`, and
  `TauCeti.TensorSignature.Presented.mapSubstCompLiftIso`: canonical monoidal natural isomorphisms
  for identity substitutions, composite substitutions, and pullback of interpretations along
  descended substitutions.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (free monoidal categories on tensor schemes; presentations are their quotients).
-/

public section

universe u v u' v' u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory MonoidalCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (R : HomRel S.FreeMonoidal)

/-- The monoidal category presented by the tensor signature `S` and the equations `R` between
morphisms of the free monoidal category on `S`: the quotient of the free monoidal category by the
least monoidal congruence containing `R`. Its objects are the tensor words in the generating
objects of `S`. -/
abbrev Presented : Type u :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure R)

namespace Presented

variable {S}

/-- The quotient functor from the free monoidal category on `S` onto the monoidal category
presented by `S` and `R`. It is strict monoidal for the descended monoidal structure. -/
abbrev quotientFunctor : S.FreeMonoidal ⥤ S.Presented R :=
  CategoryTheory.Quotient.functor _

variable {R}

/-- The equations `R` hold in the presented monoidal category. -/
theorem sound {X Y : S.FreeMonoidal} {f g : X ⟶ Y} (h : R f g) :
    (quotientFunctor R).map f = (quotientFunctor R).map g :=
  CategoryTheory.Quotient.sound _ (.of h)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon,
    FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
  (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)

/-- The functor out of the monoidal category presented by `S` and `R` determined by the images
`fo` of the generating objects and `fc` of the coupons, provided the induced interpretation of the
free monoidal category satisfies the equations `R`. It is strong monoidal, with identity
tensorator and unit comparison. -/
-- The body is exposed so that the object part reduces, as for `FreeMonoidal.lift`: the statements
-- of `lift_ε` and its companions only typecheck once objects of the form `(lift fo fc h).obj X`
-- reduce to the corresponding tensor products in `D`.
@[expose] def lift : S.Presented R ⥤ D :=
  CategoryTheory.Quotient.lift _ (FreeMonoidal.lift fo fc) fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq h hfg

instance : (lift fo fc h).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

/-- The functor `lift fo fc h` restricts along the quotient functor to the interpretation
`FreeMonoidal.lift fo fc` of the free monoidal category. -/
theorem quotientFunctor_comp_lift : quotientFunctor R ⋙ lift fo fc h = FreeMonoidal.lift fo fc :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem lift_obj (X : S.FreeMonoidal) :
    (lift fo fc h).obj ((quotientFunctor R).obj X) = (FreeMonoidal.lift fo fc).obj X :=
  (rfl)

@[simp]
theorem lift_map {X Y : S.FreeMonoidal} (f : X ⟶ Y) :
    (lift fo fc h).map ((quotientFunctor R).map f) = (FreeMonoidal.lift fo fc).map f :=
  (rfl)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (FreeMonoidal.lift_ε fo fc)

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc h) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (FreeMonoidal.lift_η fo fc)

@[simp]
theorem lift_μ (X Y : S.Presented R) : Functor.LaxMonoidal.μ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (FreeMonoidal.lift_μ fo fc X.as Y.as)

@[simp]
theorem lift_δ (X Y : S.Presented R) : Functor.OplaxMonoidal.δ (lift fo fc h) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (FreeMonoidal.lift_δ fo fc X.as Y.as)

/-- Exact descent characterization: `FreeMonoidal.lift fo fc` factors strictly through the quotient
functor `quotientFunctor R` if and only if it identifies the two sides of every equation in `R`. -/
theorem exists_lift_iff :
    (∃ F : S.Presented R ⥤ D, quotientFunctor R ⋙ F = FreeMonoidal.lift fo fc) ↔
      ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g :=
  CategoryTheory.Quotient.exists_lift_monoidalClosure_iff R (FreeMonoidal.lift fo fc)

/-- Exact descent characterization up to natural isomorphism: `FreeMonoidal.lift fo fc` factors
through `quotientFunctor R` up to a natural isomorphism if and only if it identifies the two sides
of every equation in `R` (in which case `Presented.lift fo fc` gives a strong monoidal
factorization). -/
theorem exists_iso_lift_iff :
    (∃ F : S.Presented R ⥤ D, Nonempty (quotientFunctor R ⋙ F ≅ FreeMonoidal.lift fo fc)) ↔
      ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g :=
  CategoryTheory.Quotient.exists_iso_lift_monoidalClosure_iff R (FreeMonoidal.lift fo fc)

end Lift

section Uniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of the presented
monoidal category to a lax monoidal one is determined by its components at the generating
objects. -/
theorem natTrans_ext {F G : S.Presented R ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app ((quotientFunctor R).obj (.of a)) = β.app ((quotientFunctor R).obj (.of a))) :
    α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _ (FreeMonoidal.natTrans_ext h)

variable (F G : S.Presented R ⥤ D) [F.Monoidal] [G.Monoidal]
  (e : ∀ a, F.obj ((quotientFunctor R).obj (.of a)) ≅ G.obj ((quotientFunctor R).obj (.of a)))

/-- Two strong monoidal functors out of the monoidal category presented by `S` and `R` that agree
up to isomorphisms `e` on the generating objects, compatibly with every coupon, are isomorphic by
a monoidal natural isomorphism extending `e`. The compatibility is stated with the isomorphisms
`FreeMonoidal.wordIso` which `e` induces on all tensor words. -/
def monoidalNatIso
    (he : ∀ g, F.map ((quotientFunctor R).map (FreeMonoidal.coupon g)) ≫
        (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
        G.map ((quotientFunctor R).map (FreeMonoidal.coupon g))) :
    F ≅ G :=
  CategoryTheory.Quotient.natIsoLift _ (FreeMonoidal.monoidalNatIso he)

variable {F G e}
  (he : ∀ g, F.map ((quotientFunctor R).map (FreeMonoidal.coupon g)) ≫
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.tgt g)).hom =
    (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e (S.src g)).hom ≫
      G.map ((quotientFunctor R).map (FreeMonoidal.coupon g)))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeMonoidal) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj X) =
      (FreeMonoidal.wordIso (quotientFunctor R ⋙ F) (quotientFunctor R ⋙ G) e X.as).hom :=
  FreeMonoidal.monoidalNatIso_hom_app he X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app ((quotientFunctor R).obj (.of a)) = (e a).hom :=
  FreeMonoidal.monoidalNatIso_hom_app_of he a

instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.natTransLift _ (FreeMonoidal.monoidalNatIso he).hom))

end Uniqueness

/-! ### Descent of substitutions and signature morphisms -/

section MapSubst

variable {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
  {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}

/-- Descend a substitution `σ : Substitution S T` to a strong monoidal functor
`S.Presented R ⥤ T.Presented R'`, provided `σ.toFunctor` sends every generating equation of `R` to
an equality in `T.Presented R'`. -/
@[expose] def mapSubst (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g)) :
    S.Presented R ⥤ T.Presented R' :=
  CategoryTheory.Quotient.lift _ (σ.toFunctor ⋙ quotientFunctor R') fun _ _ _ _ hfg ↦
    HomRel.MonoidalClosure.map_eq (F := σ.toFunctor ⋙ quotientFunctor R') hσ hfg

section Basic

variable (σ : Substitution S T)
  (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
    (quotientFunctor R').map (σ.toFunctor.map f) =
      (quotientFunctor R').map (σ.toFunctor.map g))

instance : (mapSubst σ hσ).Monoidal :=
  CategoryTheory.Quotient.liftMonoidal _ _

theorem quotientFunctor_comp_mapSubst :
    quotientFunctor R ⋙ mapSubst σ hσ = σ.toFunctor ⋙ quotientFunctor R' :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem mapSubst_obj (X : S.FreeMonoidal) :
    (mapSubst σ hσ).obj ((quotientFunctor R).obj X) =
      (quotientFunctor R').obj (σ.toFunctor.obj X) :=
  rfl

@[simp]
theorem mapSubst_map {X Y : S.FreeMonoidal} (f : X ⟶ Y) :
    (mapSubst σ hσ).map ((quotientFunctor R).map f) =
      (quotientFunctor R').map (σ.toFunctor.map f) :=
  rfl

@[simp]
theorem mapSubst_ε : Functor.LaxMonoidal.ε (mapSubst σ hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_ε _ _).trans (by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_ε, Substitution.toFunctor_ε,
      CategoryTheory.Quotient.functor_ε, Category.id_comp]
    exact (quotientFunctor R').map_id _)

@[simp]
theorem mapSubst_η : Functor.OplaxMonoidal.η (mapSubst σ hσ) = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_η _ _).trans (by
    simp only [Functor.comp_obj, Functor.OplaxMonoidal.comp_η, Substitution.toFunctor_η,
      CategoryTheory.Quotient.functor_η, Category.comp_id]
    exact (quotientFunctor R').map_id _)

@[simp]
theorem mapSubst_μ (X Y : S.Presented R) :
    Functor.LaxMonoidal.μ (mapSubst σ hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans (by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, Substitution.toFunctor_μ,
      CategoryTheory.Quotient.functor_μ, Category.id_comp]
    exact (quotientFunctor R').map_id _)

@[simp]
theorem mapSubst_δ (X Y : S.Presented R) :
    Functor.OplaxMonoidal.δ (mapSubst σ hσ) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans (by
    simp only [Functor.comp_obj, Functor.OplaxMonoidal.comp_δ, Substitution.toFunctor_δ,
      CategoryTheory.Quotient.functor_δ, Category.comp_id]
    exact (quotientFunctor R').map_id _)

end Basic

/-- Exact descent characterization for substitutions: `σ.toFunctor ⋙ quotientFunctor R'` factors
strictly through `quotientFunctor R` if and only if every equation in `R` becomes an equality in
`T.Presented R'` after applying `σ.toFunctor`. -/
theorem exists_mapSubst_iff (σ : Substitution S T) :
    (∃ F : S.Presented R ⥤ T.Presented R',
        quotientFunctor R ⋙ F = σ.toFunctor ⋙ quotientFunctor R') ↔
      ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (quotientFunctor R').map (σ.toFunctor.map f) =
          (quotientFunctor R').map (σ.toFunctor.map g) :=
  CategoryTheory.Quotient.exists_lift_monoidalClosure_iff R (σ.toFunctor ⋙ quotientFunctor R')

/-- Exact descent characterization for substitutions up to natural isomorphism:
`σ.toFunctor ⋙ quotientFunctor R'` factors through `quotientFunctor R` up to natural isomorphism
if and only if every equation in `R` becomes an equality in `T.Presented R'` after applying
`σ.toFunctor`. -/
theorem exists_iso_mapSubst_iff (σ : Substitution S T) :
    (∃ F : S.Presented R ⥤ T.Presented R',
        Nonempty (quotientFunctor R ⋙ F ≅ σ.toFunctor ⋙ quotientFunctor R')) ↔
      ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
        (quotientFunctor R').map (σ.toFunctor.map f) =
          (quotientFunctor R').map (σ.toFunctor.map g) :=
  CategoryTheory.Quotient.exists_iso_lift_monoidalClosure_iff R (σ.toFunctor ⋙ quotientFunctor R')

/-- Descend a substitution `σ : Substitution S T` when `σ.toFunctor` maps every generating relation
in `R` directly into `R'`. -/
abbrev mapSubstOfRel (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      R' (σ.toFunctor.map f) (σ.toFunctor.map g)) :
    S.Presented R ⥤ T.Presented R' :=
  mapSubst σ fun _ _ _ _ hfg ↦ sound (hσ hfg)

/-- Descend a tensor-signature morphism `φ : Hom S T` to a strong monoidal functor
`S.Presented R ⥤ T.Presented R'`. -/
abbrev mapHom (φ : Hom S T)
    (hφ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (φ.toFunctor.map f) =
        (quotientFunctor R').map (φ.toFunctor.map g)) :
    S.Presented R ⥤ T.Presented R' :=
  mapSubst φ.toSubstitution hφ

end MapSubst

/-! ### Functoriality and pullback on presented monoidal categories -/

section Functoriality

/-- The identity substitution on `S` respects every presentation relation `R`. -/
theorem mapSubst_id_respects {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R).map ((Substitution.id S).toFunctor.map f) =
        (quotientFunctor R).map ((Substitution.id S).toFunctor.map g) :=
  fun _ _ _ _ hfg ↦ (NatIso.map_eq_iff
    (Functor.isoWhiskerRight (Substitution.toFunctorIdIso S) (quotientFunctor R))).mpr
    (sound hfg)

/-- Descended identity substitution `mapSubst (Substitution.id S) _` is monoidally naturally
isomorphic to the identity functor on `S.Presented R`. -/
def mapSubstIdIso {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    mapSubst (Substitution.id S) (mapSubst_id_respects R) ≅ 𝟭 (S.Presented R) :=
  CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.lift.isLift _ _ _ ≪≫
      Functor.isoWhiskerRight (Substitution.toFunctorIdIso S) (quotientFunctor R) ≪≫
      Functor.leftUnitor (quotientFunctor R) ≪≫
      (Functor.rightUnitor (quotientFunctor R)).symm)

@[simp]
theorem mapSubstIdIso_hom_app {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal)
    (X : S.FreeMonoidal) :
    (mapSubstIdIso R).hom.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R).obj (FreeMonoidal.projectObj_of_self X)) :=
  Eq.trans
    (show 𝟙 _ ≫ (quotientFunctor R).map ((Substitution.toFunctorIdIso S).hom.app X) ≫ 𝟙 _ ≫ 𝟙 _ =
        (quotientFunctor R).map ((Substitution.toFunctorIdIso S).hom.app X) by
      simp only [Category.id_comp, Category.comp_id])
    ((congrArg (quotientFunctor R).map (Substitution.toFunctorIdIso_hom_app S X)).trans
      (eqToHom_map (quotientFunctor R) _))

@[simp]
theorem mapSubstIdIso_inv_app {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal)
    (X : S.FreeMonoidal) :
    (mapSubstIdIso R).inv.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R).obj (FreeMonoidal.projectObj_of_self X)).symm :=
  Eq.trans
    (show ((𝟙 _ ≫ 𝟙 _) ≫ (quotientFunctor R).map ((Substitution.toFunctorIdIso S).inv.app X)) ≫
        𝟙 _ = (quotientFunctor R).map ((Substitution.toFunctorIdIso S).inv.app X) by
      simp only [Category.id_comp, Category.comp_id])
    ((congrArg (quotientFunctor R).map (Substitution.toFunctorIdIso_inv_app S X)).trans
      (eqToHom_map (quotientFunctor R) _))

instance {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    NatTrans.IsMonoidal (mapSubstIdIso R).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (CategoryTheory.Quotient.natTransLift _
    ((CategoryTheory.Quotient.lift.isLift _ _ _).hom ≫
      Functor.whiskerRight (Substitution.toFunctorIdIso S).hom (quotientFunctor R) ≫
      (Functor.leftUnitor (quotientFunctor R)).hom ≫
      (Functor.rightUnitor (quotientFunctor R)).inv)))

/-- Composition of substitutions preserves compatibility with presentation relations. -/
theorem mapSubst_comp_respects
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g)) :
    ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R'').map ((σ.comp τ).toFunctor.map f) =
        (quotientFunctor R'').map ((σ.comp τ).toFunctor.map g) :=
  fun _ _ _ _ hfg ↦ (NatIso.map_eq_iff
    (Functor.isoWhiskerRight (Substitution.toFunctorCompIso σ τ) (quotientFunctor R''))).mpr
    (congrArg (mapSubst τ hτ).map (hσ hfg))

/-- Descending a composite substitution `σ.comp τ` is monoidally naturally isomorphic to composing
the descended functors `mapSubst σ hσ ⋙ mapSubst τ hτ`. -/
def mapSubstCompIso
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g)) :
    mapSubst (σ.comp τ) (mapSubst_comp_respects hσ hτ) ≅ mapSubst σ hσ ⋙ mapSubst τ hτ :=
  CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.lift.isLift _ _ _ ≪≫
      Functor.isoWhiskerRight (Substitution.toFunctorCompIso σ τ) (quotientFunctor R'') ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CategoryTheory.Quotient.lift.isLift _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryTheory.Quotient.lift.isLift _ _ _).symm _ ≪≫
      Functor.associator _ _ _)

@[simp]
theorem mapSubstCompIso_hom_app
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g))
    (X : S.FreeMonoidal) :
    (mapSubstCompIso hσ hτ).hom.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R'').obj
        (FreeMonoidal.projectObj_projectObj_as τ.obj σ.obj X.as).symm) :=
  let Y := (quotientFunctor R'').obj ((σ.toFunctor ⋙ τ.toFunctor).obj X)
  Eq.trans
    (congrArg (fun g : Y ⟶ Y ↦
        𝟙 _ ≫ (quotientFunctor R'').map ((Substitution.toFunctorCompIso σ τ).hom.app X) ≫
          𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y ≫ g ≫ 𝟙 Y)
      (show (mapSubst τ hτ).map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) = 𝟙 Y from
        (mapSubst τ hτ).map_id _))
    (Eq.trans
      (by simp only [Y, Category.id_comp, Category.comp_id]; rfl)
      ((congrArg (quotientFunctor R'').map (Substitution.toFunctorCompIso_hom_app σ τ X)).trans
        (eqToHom_map (quotientFunctor R'') _)))

@[simp]
theorem mapSubstCompIso_inv_app
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g))
    (X : S.FreeMonoidal) :
    (mapSubstCompIso hσ hτ).inv.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R'').obj
        (FreeMonoidal.projectObj_projectObj_as τ.obj σ.obj X.as)) :=
  let Y := (quotientFunctor R'').obj ((σ.toFunctor ⋙ τ.toFunctor).obj X)
  Eq.trans
    (congrArg (fun g : Y ⟶ Y ↦
        (((((𝟙 Y ≫ g) ≫ 𝟙 Y) ≫ 𝟙 Y) ≫ 𝟙 Y) ≫
          (quotientFunctor R'').map ((Substitution.toFunctorCompIso σ τ).inv.app X)) ≫ 𝟙 _)
      (show (mapSubst τ hτ).map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) = 𝟙 Y from
        (mapSubst τ hτ).map_id _))
    (Eq.trans
      (by simp only [Y, Category.id_comp, Category.comp_id]; rfl)
      ((congrArg (quotientFunctor R'').map (Substitution.toFunctorCompIso_inv_app σ τ X)).trans
        (eqToHom_map (quotientFunctor R'') _)))

instance
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g)) :
    NatTrans.IsMonoidal (mapSubstCompIso hσ hτ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (CategoryTheory.Quotient.natTransLift _
    ((CategoryTheory.Quotient.lift.isLift _ _ _).hom ≫
      Functor.whiskerRight (Substitution.toFunctorCompIso σ τ).hom (quotientFunctor R'') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (CategoryTheory.Quotient.lift.isLift _ _ _).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (CategoryTheory.Quotient.lift.isLift _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom)))

end Functoriality

section Pullback

variable {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
  {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
  {D : Type u₃} [Category.{v₃} D] [MonoidalCategory D]

/-- Pulling back a presentation-satisfying interpretation `(fo, fc)` of `(T, R')` along a
relation-respecting substitution `σ : Substitution S T` yields an interpretation of `(S, R)`
satisfying `R`. -/
theorem pullback_respects (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc)).map f =
        (FreeMonoidal.lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc)).map g :=
  fun _ _ _ _ hfg ↦ (NatIso.map_eq_iff (σ.toFunctorCompLiftIso fo fc)).mp
    (congrArg (lift fo fc hR').map (hσ hfg))

/-- Change-of-presentation compatibility: precomposing `Presented.lift fo fc hR'` with a descended
substitution `mapSubst σ hσ` is monoidally naturally isomorphic to `Presented.lift` of the
pulled-back interpretation `(σ.pullbackObj fo, σ.pullbackCoupon fo fc)` in any monoidal category
`D`. -/
def mapSubstCompLiftIso (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    mapSubst σ hσ ⋙ lift fo fc hR' ≅
      lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc) (pullback_respects σ hσ fo fc hR') :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryTheory.Quotient.lift.isLift _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CategoryTheory.Quotient.lift.isLift _ _ _) ≪≫
      σ.toFunctorCompLiftIso fo fc ≪≫
      (CategoryTheory.Quotient.lift.isLift _ _ _).symm)

@[simp]
theorem mapSubstCompLiftIso_hom_app (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)
    (X : S.FreeMonoidal) :
    (mapSubstCompLiftIso σ hσ fo fc hR').hom.app ((quotientFunctor R).obj X) =
      eqToHom (σ.projectObj_pullbackObj fo X.as).symm :=
  let Y := (σ.toFunctor ⋙ FreeMonoidal.lift fo fc).obj X
  Eq.trans
    (congrArg (fun g : Y ⟶ Y ↦
        𝟙 Y ≫ g ≫ 𝟙 Y ≫ 𝟙 Y ≫ (σ.toFunctorCompLiftIso fo fc).hom.app X ≫ 𝟙 _)
      (show (lift fo fc hR').map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) = 𝟙 Y from
        (lift fo fc hR').map_id _))
    (Eq.trans
      (by simp only [Y, Category.id_comp, Category.comp_id]; rfl)
      (σ.toFunctorCompLiftIso_hom_app fo fc X))

@[simp]
theorem mapSubstCompLiftIso_inv_app (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)
    (X : S.FreeMonoidal) :
    (mapSubstCompLiftIso σ hσ fo fc hR').inv.app ((quotientFunctor R).obj X) =
      eqToHom (σ.projectObj_pullbackObj fo X.as) :=
  let Y := (σ.toFunctor ⋙ FreeMonoidal.lift fo fc).obj X
  Eq.trans
    (congrArg (fun g : Y ⟶ Y ↦
        ((((𝟙 _ ≫ (σ.toFunctorCompLiftIso fo fc).inv.app X) ≫ 𝟙 Y) ≫ 𝟙 Y) ≫ g) ≫ 𝟙 Y)
      (show (lift fo fc hR').map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) = 𝟙 Y from
        (lift fo fc hR').map_id _))
    (Eq.trans
      (by simp only [Y, Category.id_comp, Category.comp_id]; rfl)
      (σ.toFunctorCompLiftIso_inv_app fo fc X))

instance (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    NatTrans.IsMonoidal (mapSubstCompLiftIso σ hσ fo fc hR').hom :=
  inferInstanceAs (NatTrans.IsMonoidal (CategoryTheory.Quotient.natTransLift _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (CategoryTheory.Quotient.lift.isLift _ _ _).hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (CategoryTheory.Quotient.lift.isLift _ _ _).hom ≫
      (σ.toFunctorCompLiftIso fo fc).hom ≫
      (CategoryTheory.Quotient.lift.isLift _ _ _).inv)))

end Pullback

end Presented

end TauCeti.TensorSignature
