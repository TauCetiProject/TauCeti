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
canonical monoidal natural isomorphisms (`mapSubstIdIso` and `mapSubstCompIso`) satisfying unit
and associativity coherence (`mapSubstCompIso_id_left`, `mapSubstCompIso_id_right`,
`mapSubstCompIso_assoc`), and precomposing a presentation interpretation `Presented.lift` with a
descended substitution is monoidally naturally isomorphic to `Presented.lift` of the pulled-back
generator interpretation (`mapSubstCompLiftIso`), compatibly with identity and composite
substitutions (`mapSubstCompLiftIso_id`, `mapSubstCompLiftIso_comp`).

## Main definitions and results

* `TauCeti.TensorSignature.Presented S R`: the monoidal category presented by `S` and `R`, and
  `TauCeti.TensorSignature.Presented.quotientFunctor R` the strict monoidal quotient functor from
  the free monoidal category, which identifies the two sides of every equation of `R`
  (`TauCeti.TensorSignature.Presented.sound`).
* `TauCeti.TensorSignature.Presented.lift fo fc h`: the strong monoidal functor determined by the
  images `fo` of the generating objects and `fc` of the coupons satisfying the equations, with
  computation rules `TauCeti.TensorSignature.Presented.lift_obj` and
  `TauCeti.TensorSignature.Presented.lift_map`, functoriality in interpretation morphisms
  `TauCeti.TensorSignature.Presented.liftIso`, the factorization
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
  descended substitutions, together with their unit, associativity, and pullback coherence laws.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (free monoidal categories on tensor schemes; presentations are their quotients).
-/

public section

universe u v u' v' u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

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

private def isLiftIso {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
    (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    quotientFunctor R ⋙ lift fo fc h ≅ FreeMonoidal.lift fo fc :=
  CategoryTheory.Quotient.lift.isLift _ _ _

private lemma isLiftIso_hom_app {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
    (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)
    (X : S.FreeMonoidal) :
    (isLiftIso (R := R) fo fc h).hom.app X = 𝟙 _ :=
  rfl

private lemma isLiftIso_inv_app {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
    (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g)
    (X : S.FreeMonoidal) :
    (isLiftIso (R := R) fo fc h).inv.app X = 𝟙 _ :=
  rfl

private instance {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
    (h : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    NatTrans.IsMonoidal (isLiftIso (R := R) fo fc h).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.lift.isLift _ (FreeMonoidal.lift fo fc) _).hom)

private def liftPreIso {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {I J : Interpretation S D} (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g) :
    quotientFunctor R ⋙ lift I.obj I.coupon hI ≅
      quotientFunctor R ⋙ lift J.obj J.coupon hJ :=
  isLiftIso I.obj I.coupon hI ≪≫
    MonoidalFunctor.toFunctorIso ((Interpretation.extension S D).map α).iso ≪≫
    (isLiftIso J.obj J.coupon hJ).symm

private lemma liftPreIso_hom_app {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {I J : Interpretation S D} (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g)
    (X : S.FreeMonoidal) :
    (liftPreIso α hI hJ).hom.app X = (FreeMonoidalCategory.projectObjIso α.iso X.as).hom := by
  dsimp only [liftPreIso, isLiftIso]
  exact (Category.id_comp _).trans
    ((congrArg (· ≫ _) (Interpretation.extension_map_iso_hom_hom_hom_app α X)).trans
      (Category.comp_id _))

private instance {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {I J : Interpretation S D} (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g) :
    NatTrans.IsMonoidal (liftPreIso α hI hJ).hom where
  unit := by
    simp only [liftPreIso_hom_app, Functor.comp_obj, Functor.LaxMonoidal.comp_ε,
      lift_ε, CategoryTheory.Quotient.functor_ε, Functor.map_id]
    exact (congrArg (· ≫ _) (Category.id_comp _)).trans
      ((Category.id_comp _).trans
        ((congrArg Iso.hom (FreeMonoidalCategory.projectObjIso_tensorUnit α.iso)).trans
          ((Iso.refl_hom _).trans (Category.comp_id _).symm)))
  tensor X Y := by
    simp only [liftPreIso_hom_app, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      lift_μ, CategoryTheory.Quotient.functor_μ, Functor.map_id]
    exact (congrArg (· ≫ _) (Category.id_comp _)).trans
      ((Category.id_comp _).trans
        ((congrArg Iso.hom (FreeMonoidalCategory.projectObjIso_tensor α.iso X.as Y.as)).trans
          ((tensorIso_hom _ _).trans
            ((Category.comp_id _).symm.trans
              (congrArg (_ ≫ ·) (Category.comp_id _).symm)))))

/-- An isomorphism `α : I ⟶ J` of interpretations of `S` in `D` whose induced lifts satisfy `R`
descends to a monoidal natural isomorphism between `lift I.obj I.coupon hI` and
`lift J.obj J.coupon hJ`. -/
def liftIso {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {I J : Interpretation S D}
    (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g) :
    lift I.obj I.coupon hI ≅ lift J.obj J.coupon hJ :=
  CategoryTheory.Quotient.natIsoLift _ (liftPreIso α hI hJ)

@[simp]
theorem liftIso_hom_app {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {I J : Interpretation S D} (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g)
    (X : S.FreeMonoidal) :
    (liftIso α hI hJ).hom.app ((quotientFunctor R).obj X) =
      (FreeMonoidalCategory.projectObjIso α.iso X.as).hom :=
  (CategoryTheory.Quotient.natTransLift_app _ _ _ (liftPreIso α hI hJ).hom X).trans
    (liftPreIso_hom_app α hI hJ X)

@[simp]
theorem liftIso_inv_app {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {I J : Interpretation S D} (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g)
    (X : S.FreeMonoidal) :
    (liftIso α hI hJ).inv.app ((quotientFunctor R).obj X) =
      (FreeMonoidalCategory.projectObjIso α.iso X.as).inv := by
  refine (cancel_epi ((liftIso α hI hJ).hom.app ((quotientFunctor R).obj X))).mp ?_
  rw [Iso.hom_inv_id_app, liftIso_hom_app]
  exact (Iso.hom_inv_id (FreeMonoidalCategory.projectObjIso α.iso X.as)).symm

instance {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {I J : Interpretation S D}
    (α : I ⟶ J)
    (hI : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift I.obj I.coupon).map f = (FreeMonoidal.lift I.obj I.coupon).map g)
    (hJ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift J.obj J.coupon).map f = (FreeMonoidal.lift J.obj J.coupon).map g) :
    NatTrans.IsMonoidal (liftIso α hI hJ).hom := by
  dsimp only [liftIso]
  infer_instance

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

-- Exposed so that `(mapSubst σ hσ).obj` reduces on `𝟙_` and `⊗`, allowing `mapSubst_ε`,
-- `mapSubst_η`, `mapSubst_μ`, and `mapSubst_δ` to be stated directly against `𝟙 _`.
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

/-- `mapSubst σ hσ` preserves tensor products of objects strictly. -/
@[simp]
theorem mapSubst_obj_tensor (X Y : S.Presented R) :
    (mapSubst σ hσ).obj (X ⊗ Y) = (mapSubst σ hσ).obj X ⊗ (mapSubst σ hσ).obj Y :=
  rfl

/-- `mapSubst σ hσ` preserves the tensor unit strictly. -/
@[simp]
theorem mapSubst_obj_tensorUnit :
    (mapSubst σ hσ).obj (𝟙_ (S.Presented R)) = 𝟙_ (T.Presented R') :=
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

/-- Equal substitutions induce equal descended functors between presented categories. -/
theorem mapSubst_congr {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂)
    (hσ₁ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ₁.toFunctor.map f) =
        (quotientFunctor R').map (σ₁.toFunctor.map g))
    (hσ₂ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ₂.toFunctor.map f) =
        (quotientFunctor R').map (σ₂.toFunctor.map g)) :
    mapSubst σ₁ hσ₁ = mapSubst σ₂ hσ₂ := by
  subst h
  rfl

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

private def mapSubstIsLiftIso (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g)) :
    quotientFunctor R ⋙ mapSubst σ hσ ≅ σ.toFunctor ⋙ quotientFunctor R' :=
  CategoryTheory.Quotient.lift.isLift _ _ _

private lemma mapSubstIsLiftIso_hom_app (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (X : S.FreeMonoidal) :
    (mapSubstIsLiftIso (R := R) (R' := R') σ hσ).hom.app X = 𝟙 _ :=
  rfl

private lemma mapSubstIsLiftIso_inv_app (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (X : S.FreeMonoidal) :
    (mapSubstIsLiftIso (R := R) (R' := R') σ hσ).inv.app X = 𝟙 _ :=
  rfl

private instance (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g)) :
    NatTrans.IsMonoidal (mapSubstIsLiftIso (R := R) (R' := R') σ hσ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (CategoryTheory.Quotient.lift.isLift _ (σ.toFunctor ⋙ quotientFunctor R') _).hom)

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

private def mapSubstIdPreIso {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    quotientFunctor R ⋙ mapSubst (Substitution.id S) (mapSubst_id_respects R) ≅
      quotientFunctor R ⋙ 𝟭 (S.Presented R) :=
  mapSubstIsLiftIso (Substitution.id S) (mapSubst_id_respects R) ≪≫
    Functor.isoWhiskerRight (Substitution.toFunctorIdIso S) (quotientFunctor R) ≪≫
    Functor.leftUnitor (quotientFunctor R) ≪≫
    (Functor.rightUnitor (quotientFunctor R)).symm

private instance {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    NatTrans.IsMonoidal (mapSubstIdPreIso R).hom := by
  dsimp only [mapSubstIdPreIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- Descended identity substitution `mapSubst (Substitution.id S) _` is monoidally naturally
isomorphic to the identity functor on `S.Presented R`. -/
def mapSubstIdIso {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    mapSubst (Substitution.id S) (mapSubst_id_respects R) ≅ 𝟭 (S.Presented R) :=
  CategoryTheory.Quotient.natIsoLift _ (mapSubstIdPreIso R)

@[simp]
theorem mapSubstIdIso_hom_app {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal)
    (X : S.FreeMonoidal) :
    (mapSubstIdIso R).hom.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R).obj (Substitution.toFunctor_id_obj S X)) := by
  refine (CategoryTheory.Quotient.natTransLift_app _ _ _ (mapSubstIdPreIso R).hom X).trans ?_
  have hmid : (mapSubstIdPreIso R).hom.app X =
      𝟙 _ ≫ (quotientFunctor R).map ((Substitution.toFunctorIdIso S).hom.app X) ≫ 𝟙 _ ≫ 𝟙 _ :=
    rfl
  have hq : (quotientFunctor R).map ((Substitution.toFunctorIdIso S).hom.app X) =
      eqToHom (congrArg (quotientFunctor R).obj (Substitution.toFunctor_id_obj S X)) :=
    (congrArg (quotientFunctor R).map (Substitution.toFunctorIdIso_hom_app S X)).trans
      (eqToHom_map _ _)
  exact hmid.trans ((Category.id_comp _).trans
    ((congrArg (· ≫ _) hq).trans
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _))))

@[simp]
theorem mapSubstIdIso_inv_app {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal)
    (X : S.FreeMonoidal) :
    (mapSubstIdIso R).inv.app ((quotientFunctor R).obj X) =
      eqToHom (congrArg (quotientFunctor R).obj (Substitution.toFunctor_id_obj S X)).symm := by
  refine (cancel_epi ((mapSubstIdIso R).hom.app ((quotientFunctor R).obj X))).mp ?_
  rw [Iso.hom_inv_id_app, mapSubstIdIso_hom_app]
  exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm

instance {S : TensorSignature.{u, v}} (R : HomRel S.FreeMonoidal) :
    NatTrans.IsMonoidal (mapSubstIdIso R).hom := by
  dsimp only [mapSubstIdIso]
  infer_instance

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

private def mapSubstCompPreIso
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
    quotientFunctor R ⋙ mapSubst (σ.comp τ) (mapSubst_comp_respects hσ hτ) ≅
      quotientFunctor R ⋙ mapSubst σ hσ ⋙ mapSubst τ hτ :=
  mapSubstIsLiftIso (σ.comp τ) (mapSubst_comp_respects hσ hτ) ≪≫
    Functor.isoWhiskerRight (Substitution.toFunctorCompIso σ τ) (quotientFunctor R'') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (mapSubstIsLiftIso τ hτ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapSubstIsLiftIso σ hσ).symm _ ≪≫
    Functor.associator _ _ _

private instance
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
    NatTrans.IsMonoidal (mapSubstCompPreIso hσ hτ).hom := by
  dsimp only [mapSubstCompPreIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

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
  CategoryTheory.Quotient.natIsoLift _ (mapSubstCompPreIso hσ hτ)

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
      eqToHom (congrArg (quotientFunctor R'').obj (Substitution.toFunctor_comp_obj σ τ X)) := by
  rw [mapSubstCompIso, CategoryTheory.Quotient.natIsoLift_hom,
    CategoryTheory.Quotient.natTransLift_app, mapSubstCompPreIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, mapSubstIsLiftIso_hom_app,
    Iso.symm_hom, mapSubstIsLiftIso_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Substitution.toFunctorCompIso_hom_app,
    Functor.comp_obj, mapSubst_obj, Functor.map_id, eqToHom_map,
    Category.id_comp, Category.comp_id]

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
      eqToHom
        (congrArg (quotientFunctor R'').obj (Substitution.toFunctor_comp_obj σ τ X)).symm := by
  refine (cancel_epi ((mapSubstCompIso hσ hτ).hom.app ((quotientFunctor R).obj X))).mp ?_
  rw [Iso.hom_inv_id_app, mapSubstCompIso_hom_app]
  exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm

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
    NatTrans.IsMonoidal (mapSubstCompIso hσ hτ).hom := by
  dsimp only [mapSubstCompIso]
  infer_instance

/-- Left unit coherence for `mapSubst`: composing `mapSubstCompIso` with `mapSubstIdIso R`
agrees with `Substitution.id_comp`. -/
theorem mapSubstCompIso_id_left
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g)) :
    mapSubstCompIso (mapSubst_id_respects R) hσ ≪≫
        Functor.isoWhiskerRight (mapSubstIdIso R) (mapSubst σ hσ) ≪≫
        Functor.leftUnitor (mapSubst σ hσ) =
      eqToIso (mapSubst_congr (Substitution.id_comp σ) _ hσ) := by
  refine Iso.ext <| CategoryTheory.Quotient.natTrans_ext _ _ <| NatTrans.ext <| funext fun X ↦ ?_
  rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.trans_hom,
    NatTrans.comp_app, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app]
  have h1 := mapSubstCompIso_hom_app (mapSubst_id_respects R) hσ X
  have h2 : (mapSubst σ hσ).map ((mapSubstIdIso R).hom.app ((quotientFunctor R).obj X)) =
      eqToHom (congrArg (mapSubst σ hσ).obj
        (congrArg (quotientFunctor R).obj (Substitution.toFunctor_id_obj S X))) :=
    (congrArg (mapSubst σ hσ).map (mapSubstIdIso_hom_app R X)).trans (eqToHom_map _ _)
  exact (congrArg₂ (· ≫ ·) h1 ((congrArg (· ≫ _) h2).trans (Category.comp_id _))).trans
    (eqToHom_trans _ _)

/-- Right unit coherence for `mapSubst`: composing `mapSubstCompIso` with `mapSubstIdIso R'`
agrees with `Substitution.comp_id`. -/
theorem mapSubstCompIso_id_right
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g)) :
    mapSubstCompIso hσ (mapSubst_id_respects R') ≪≫
        Functor.isoWhiskerLeft (mapSubst σ hσ) (mapSubstIdIso R') ≪≫
        Functor.rightUnitor (mapSubst σ hσ) =
      eqToIso (mapSubst_congr (Substitution.comp_id σ) _ hσ) := by
  refine Iso.ext <| CategoryTheory.Quotient.natTrans_ext _ _ <| NatTrans.ext <| funext fun X ↦ ?_
  simp only [Functor.whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    mapSubstCompIso_hom_app, mapSubst_obj, mapSubstIdIso_hom_app, eqToHom_trans,
    Category.comp_id, eqToIso.hom, eqToHom_app]

/-- Associativity coherence (pentagon) for `mapSubstCompIso`. -/
theorem mapSubstCompIso_assoc
    {S : TensorSignature.{u₁, v₁}} {R : HomRel S.FreeMonoidal}
    {T : TensorSignature.{u₂, v₂}} {R' : HomRel T.FreeMonoidal}
    {U : TensorSignature.{u₃, v₃}} {R'' : HomRel U.FreeMonoidal}
    {V : TensorSignature.{u₄, v₄}} {R''' : HomRel V.FreeMonoidal}
    {σ : Substitution S T}
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    {τ : Substitution T U}
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g))
    {ρ : Substitution U V}
    (hρ : ∀ ⦃X Y : U.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R'' f g →
      (quotientFunctor R''').map (ρ.toFunctor.map f) =
        (quotientFunctor R''').map (ρ.toFunctor.map g)) :
    mapSubstCompIso (mapSubst_comp_respects hσ hτ) hρ ≪≫
        Functor.isoWhiskerRight (mapSubstCompIso hσ hτ) (mapSubst ρ hρ) ≪≫
        Functor.associator (mapSubst σ hσ) (mapSubst τ hτ) (mapSubst ρ hρ) =
      eqToIso (mapSubst_congr (Substitution.comp_assoc σ τ ρ) _ _) ≪≫
        mapSubstCompIso hσ (mapSubst_comp_respects hτ hρ) ≪≫
        Functor.isoWhiskerLeft (mapSubst σ hσ) (mapSubstCompIso hτ hρ) := by
  refine Iso.ext <| CategoryTheory.Quotient.natTrans_ext _ _ <| NatTrans.ext <| funext fun X ↦ ?_
  simp only [Functor.whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.comp_obj, mapSubstCompIso_hom_app, mapSubst_obj, eqToHom_map,
    eqToHom_trans, Category.comp_id, eqToIso.hom, eqToHom_app]
  exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm

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

private def mapSubstCompLiftPreIso (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    quotientFunctor R ⋙ mapSubst σ hσ ⋙ lift fo fc hR' ≅
      quotientFunctor R ⋙
        lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc) (pullback_respects σ hσ fo fc hR') :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapSubstIsLiftIso σ hσ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (isLiftIso fo fc hR') ≪≫
    σ.toFunctorCompLiftIso fo fc ≪≫
    (isLiftIso (σ.pullbackObj fo) (σ.pullbackCoupon fo fc)
      (pullback_respects σ hσ fo fc hR')).symm

private instance (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    NatTrans.IsMonoidal (mapSubstCompLiftPreIso σ hσ fo fc hR').hom := by
  dsimp only [mapSubstCompLiftPreIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

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
  CategoryTheory.Quotient.natIsoLift _ (mapSubstCompLiftPreIso σ hσ fo fc hR')

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
      eqToHom (σ.projectObj_pullbackObj fo X.as).symm := by
  refine (CategoryTheory.Quotient.natTransLift_app _ _ _
    (mapSubstCompLiftPreIso σ hσ fo fc hR').hom X).trans ?_
  have hmid : (mapSubstCompLiftPreIso σ hσ fo fc hR').hom.app X =
      𝟙 _ ≫ ((lift fo fc hR').map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) ≫
        𝟙 _ ≫ 𝟙 _ ≫ (σ.toFunctorCompLiftIso fo fc).hom.app X ≫ 𝟙 _) := rfl
  have hl : (lift fo fc hR').map (𝟙 ((quotientFunctor R').obj (σ.toFunctor.obj X))) = 𝟙 _ :=
    (lift fo fc hR').map_id _
  exact hmid.trans ((Category.id_comp _).trans
    ((congrArg (· ≫ _) hl).trans
      ((Category.id_comp _).trans
        ((Category.id_comp _).trans
          ((Category.id_comp _).trans
            ((congrArg (· ≫ _) (Substitution.toFunctorCompLiftIso_hom_app σ fo fc X)).trans
              (Category.comp_id _)))))))

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
      eqToHom (σ.projectObj_pullbackObj fo X.as) := by
  refine (cancel_epi ((mapSubstCompLiftIso σ hσ fo fc hR').hom.app ((quotientFunctor R).obj X))).mp
    ?_
  rw [Iso.hom_inv_id_app, mapSubstCompLiftIso_hom_app]
  exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm

instance (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon,
      FreeMonoidalCategory.projectObj fo (T.src h) ⟶ FreeMonoidalCategory.projectObj fo (T.tgt h))
    (hR' : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    NatTrans.IsMonoidal (mapSubstCompLiftIso σ hσ fo fc hR').hom := by
  dsimp only [mapSubstCompLiftIso]
  infer_instance

/-- Compatibility of `mapSubstCompLiftIso` with the identity substitution. -/
theorem mapSubstCompLiftIso_id (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      FreeMonoidalCategory.projectObj fo (S.src g) ⟶ FreeMonoidalCategory.projectObj fo (S.tgt g))
    (hR : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    mapSubstCompLiftIso (Substitution.id S) (mapSubst_id_respects R) fo fc hR ≪≫
        liftIso ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩)
          (pullback_respects (Substitution.id S) (mapSubst_id_respects R) fo fc hR) hR =
      Functor.isoWhiskerRight (mapSubstIdIso R) (lift fo fc hR) ≪≫
        Functor.leftUnitor (lift fo fc hR) := by
  refine Iso.ext <| CategoryTheory.Quotient.natTrans_ext _ _ <| NatTrans.ext <| funext fun X ↦ ?_
  rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app]
  have h1 : (mapSubstCompLiftIso (Substitution.id S) (mapSubst_id_respects R) fo fc hR).hom.app
        ((quotientFunctor R).obj X) =
      ((Substitution.id S).toFunctorCompLiftIso fo fc).hom.app X :=
    (mapSubstCompLiftIso_hom_app (Substitution.id S) (mapSubst_id_respects R) fo fc hR X).trans
      (Substitution.toFunctorCompLiftIso_hom_app (Substitution.id S) fo fc X).symm
  have h2 : (liftIso ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩)
        (pullback_respects (Substitution.id S) (mapSubst_id_respects R) fo fc hR) hR).hom.app
        ((quotientFunctor R).obj X) =
      (MonoidalFunctor.toFunctorIso
        ((Interpretation.extension S D).map
          ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩)).iso).hom.app X :=
    (liftIso_hom_app ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩)
      (pullback_respects (Substitution.id S) (mapSubst_id_respects R) fo fc hR) hR X).trans
      (Interpretation.extension_map_iso_hom_hom_hom_app
        ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩) X).symm
  have hLHS : (mapSubstCompLiftIso (Substitution.id S) (mapSubst_id_respects R) fo fc hR ≪≫
        liftIso ((Substitution.pullbackIdIso D).hom.app ⟨fo, fc⟩)
          (pullback_respects (Substitution.id S) (mapSubst_id_respects R) fo fc hR) hR).hom.app
        ((quotientFunctor R).obj X) =
      (Functor.isoWhiskerRight (Substitution.toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
        Functor.leftUnitor (FreeMonoidal.lift fo fc)).hom.app X :=
    (congrArg₂ (· ≫ ·) h1 h2).trans
      (congrArg (fun e ↦ e.hom.app X) (Substitution.toFunctorCompLiftIso_id fo fc))
  refine hLHS.trans ?_
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj,
    Substitution.toFunctorIdIso_hom_app, mapSubstIdIso_hom_app, eqToHom_map]
  exact ((Category.comp_id _).trans (eqToHom_map (lift fo fc hR) _).symm).trans
    (Category.comp_id _).symm

/-- Compatibility of `mapSubstCompLiftIso` with successive pullback along a composite
substitution `σ.comp τ`. -/
theorem mapSubstCompLiftIso_comp
    {U : TensorSignature.{u₄, v₄}} {R'' : HomRel U.FreeMonoidal}
    (σ : Substitution S T)
    (hσ : ∀ ⦃X Y : S.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R f g →
      (quotientFunctor R').map (σ.toFunctor.map f) =
        (quotientFunctor R').map (σ.toFunctor.map g))
    (τ : Substitution T U)
    (hτ : ∀ ⦃X Y : T.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R' f g →
      (quotientFunctor R'').map (τ.toFunctor.map f) =
        (quotientFunctor R'').map (τ.toFunctor.map g))
    (fo : U.Obj → D)
    (fc : ∀ h : U.Coupon,
      FreeMonoidalCategory.projectObj fo (U.src h) ⟶ FreeMonoidalCategory.projectObj fo (U.tgt h))
    (hR'' : ∀ ⦃X Y : U.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄, R'' f g →
      (FreeMonoidal.lift fo fc).map f = (FreeMonoidal.lift fo fc).map g) :
    mapSubstCompLiftIso (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'' ≪≫
        liftIso ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)
          (pullback_respects (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'')
          (pullback_respects σ hσ _ _ (pullback_respects τ hτ fo fc hR'')) =
      Functor.isoWhiskerRight (mapSubstCompIso hσ hτ) (lift fo fc hR'') ≪≫
        Functor.associator (mapSubst σ hσ) (mapSubst τ hτ) (lift fo fc hR'') ≪≫
        Functor.isoWhiskerLeft (mapSubst σ hσ) (mapSubstCompLiftIso τ hτ fo fc hR'') ≪≫
        mapSubstCompLiftIso σ hσ (τ.pullbackObj fo) (τ.pullbackCoupon fo fc)
          (pullback_respects τ hτ fo fc hR'') := by
  refine Iso.ext <| CategoryTheory.Quotient.natTrans_ext _ _ <| NatTrans.ext <| funext fun X ↦ ?_
  rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app]
  have h1 : (mapSubstCompLiftIso (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'').hom.app
        ((quotientFunctor R).obj X) =
      ((σ.comp τ).toFunctorCompLiftIso fo fc).hom.app X :=
    (mapSubstCompLiftIso_hom_app (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'' X).trans
      (Substitution.toFunctorCompLiftIso_hom_app (σ.comp τ) fo fc X).symm
  have h2 : (liftIso ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)
        (pullback_respects (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'')
        (pullback_respects σ hσ _ _ (pullback_respects τ hτ fo fc hR''))).hom.app
        ((quotientFunctor R).obj X) =
      (MonoidalFunctor.toFunctorIso
        ((Interpretation.extension S D).map
          ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)).iso).hom.app X :=
    (liftIso_hom_app ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)
      (pullback_respects (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'')
      (pullback_respects σ hσ _ _ (pullback_respects τ hτ fo fc hR'')) X).trans
      (Interpretation.extension_map_iso_hom_hom_hom_app
        ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩) X).symm
  have hLHS : (mapSubstCompLiftIso (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'' ≪≫
        liftIso ((Substitution.pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)
          (pullback_respects (σ.comp τ) (mapSubst_comp_respects hσ hτ) fo fc hR'')
          (pullback_respects σ hσ _ _ (pullback_respects τ hτ fo fc hR''))).hom.app
        ((quotientFunctor R).obj X) =
      (Functor.isoWhiskerRight (Substitution.toFunctorCompIso σ τ) (FreeMonoidal.lift fo fc) ≪≫
        Functor.associator σ.toFunctor τ.toFunctor (FreeMonoidal.lift fo fc) ≪≫
        Functor.isoWhiskerLeft σ.toFunctor (τ.toFunctorCompLiftIso fo fc) ≪≫
        σ.toFunctorCompLiftIso (τ.pullbackObj fo) (τ.pullbackCoupon fo fc)).hom.app X :=
    (congrArg₂ (· ≫ ·) h1 h2).trans
      (congrArg (fun e ↦ e.hom.app X) (Substitution.toFunctorCompLiftIso_comp σ τ fo fc))
  refine hLHS.trans ?_
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_obj, Substitution.toFunctorCompIso_hom_app,
    Substitution.toFunctorCompLiftIso_hom_app, mapSubstCompIso_hom_app, mapSubst_obj,
    mapSubstCompLiftIso_hom_app, eqToHom_map, Category.id_comp]
  have htrans {a b c d : D} (p : a = b) (q : b = c) (r : c = d) :
      eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom ((p.trans q).trans r) :=
    (congrArg (eqToHom p ≫ ·) (eqToHom_trans q r)).trans (eqToHom_trans p (q.trans r))
  exact (htrans _ _ _).trans (htrans _ _ _).symm

end Pullback

end Presented

end TauCeti.TensorSignature
