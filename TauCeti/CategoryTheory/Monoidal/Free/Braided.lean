/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature

/-!
# The free braided monoidal category on a tensor signature

For a tensor signature `S` (generating objects, and coupons between tensor words in them), the
free braided monoidal category `TensorSignature.FreeBraided S` has the tensor words as objects.
Its morphisms are formal composites, tensor products and whiskerings of identities, associators,
unitors, coupons and crossings `X ⊗ Y ⟶ Y ⊗ X` together with their inverses, modulo exactly the
axioms of a braided monoidal category: crossings are inverse to the inverse crossings, natural
on either side, and satisfy both hexagon identities. No equation between coupons is imposed, and
the braiding is not assumed symmetric.

The construction reuses the free monoidal category `TensorSignature.FreeMonoidal`: the signature
`S.withCrossings` adjoins to `S` a positive and a negative crossing coupon for every ordered pair of
tensor words, and `FreeBraided S` is the quotient of `S.withCrossings.FreeMonoidal` by the least
congruence `FreeBraided.HomEquiv` (closed under composition and whiskering on both sides)
containing the braiding axioms. The quotient functor `FreeBraided.quotientFunctor` is strict
monoidal, and both the lift and its uniqueness are deduced from those of
`S.withCrossings.FreeMonoidal`.

## Main definitions and results

* `TauCeti.TensorSignature.withCrossings S`: the signature `S` with crossing coupons adjoined.
* `TauCeti.TensorSignature.FreeBraided S`: the free braided monoidal category on `S`, with
  `FreeBraided.of` and `FreeBraided.coupon` for the generators.
* `FreeBraided.homMk`, `FreeBraided.homMk_eq_homMk_iff` and `FreeBraided.Hom.inductionOn`: every
  morphism is represented by a morphism of the free monoidal category on `S.withCrossings`, and
  two representatives give the same morphism exactly when they are related by the braiding axioms.
* `FreeBraided.quotientFunctor`: the strict monoidal quotient functor
  `S.withCrossings.FreeMonoidal ⥤ S.FreeBraided`.
* `FreeBraided.lift fo fc`: the strong braided monoidal functor into an arbitrary (not necessarily
  strict) braided monoidal category determined by images `fo` of the generating objects and `fc`
  of the coupons, with computation rules `FreeBraided.lift_obj_of`,
  `FreeBraided.lift_map_coupon` and `FreeBraided.lift_map_braiding_hom`.
* `FreeBraided.monoidalNatIso`: two strong braided monoidal functors that agree up to isomorphism
  on the generating objects, compatibly with the coupons, are monoidally naturally isomorphic.
  Taking one of them to be `lift fo fc`, this is the uniqueness of the lift.
* `FreeBraided.natTrans_ext`: monoidal natural transformations out of the free braided monoidal
  category are determined by their components at the generating objects.

Together these are the universal property of the free braided monoidal category on a tensor
scheme (Joyal–Street, *The geometry of tensor calculus I*), for strong braided monoidal
functors into arbitrary braided monoidal categories.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991).
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. 102 (1993).
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti

namespace TensorSignature

variable (S : TensorSignature.{u, v})

/-- The coupons of `S.withCrossings`: the coupons of `S`, together with a positive crossing
`X ⊗ Y ⟶ Y ⊗ X` and a negative crossing `Y ⊗ X ⟶ X ⊗ Y` for every ordered pair of tensor words
`X`, `Y`. -/
inductive CrossingCoupon : Type (max u v)
  /-- A coupon of `S`. -/
  | coupon (g : S.Coupon)
  /-- The positive crossing `X ⊗ Y ⟶ Y ⊗ X`. -/
  | crossing (X Y : FreeMonoidalCategory S.Obj)
  /-- The negative crossing `Y ⊗ X ⟶ X ⊗ Y`, inverse to `crossing X Y`. -/
  | crossingInv (X Y : FreeMonoidalCategory S.Obj)

/-- The tensor signature obtained from `S` by adjoining a positive crossing `X ⊗ Y ⟶ Y ⊗ X` and a
negative crossing `Y ⊗ X ⟶ X ⊗ Y` for every ordered pair of tensor words `X`, `Y`. The free
braided monoidal category on `S` is a quotient of the free monoidal category on this signature. -/
abbrev withCrossings : TensorSignature.{u, max u v} where
  Obj := S.Obj
  Coupon := S.CrossingCoupon
  src
    | .coupon g => S.src g
    | .crossing X Y => X.tensor Y
    | .crossingInv X Y => Y.tensor X
  tgt
    | .coupon g => S.tgt g
    | .crossing X Y => Y.tensor X
    | .crossingInv X Y => X.tensor Y

/-- The free braided monoidal category on a tensor signature `S`. Its objects are those of the free
monoidal category on `S.withCrossings`, that is, the formal tensor words in the generating objects
of `S`. -/
structure FreeBraided where
  /-- The object of the free monoidal category on `S.withCrossings` underlying an object of the
  free braided monoidal category. -/
  as : S.withCrossings.FreeMonoidal

namespace FreeBraided

variable {S}

/-- The object of the free braided monoidal category given by a single generating object. -/
@[expose] def of (a : S.Obj) : S.FreeBraided := ⟨FreeMonoidal.of (S := S.withCrossings) a⟩

/-- The positive crossing `X ⊗ Y ⟶ Y ⊗ X` in the free monoidal category on `S.withCrossings`. -/
@[expose] def crossing (X Y : S.withCrossings.FreeMonoidal) : X ⊗ Y ⟶ Y ⊗ X :=
  FreeMonoidal.coupon (S := S.withCrossings) (.crossing X.as Y.as)

/-- The negative crossing `Y ⊗ X ⟶ X ⊗ Y` in the free monoidal category on `S.withCrossings`. -/
@[expose] def crossingInv (X Y : S.withCrossings.FreeMonoidal) : Y ⊗ X ⟶ X ⊗ Y :=
  FreeMonoidal.coupon (S := S.withCrossings) (.crossingInv X.as Y.as)

/-- The congruence on morphisms of the free monoidal category on `S.withCrossings` generated by
the axioms of a braided monoidal category for the crossings, and closed under composition and
whiskering on either side. It imposes no equation on the coupons of `S`. -/
inductive HomEquiv :
    ∀ {X Y : S.withCrossings.FreeMonoidal}, (X ⟶ Y) → (X ⟶ Y) → Prop
  | refl {X Y} (f : X ⟶ Y) : HomEquiv f f
  | symm {X Y} {f g : X ⟶ Y} : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ Y} {g g' : Y ⟶ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f ≫ g) (f' ≫ g')
  | whiskerLeft (X) {Y Z} {f f' : Y ⟶ Z} : HomEquiv f f' → HomEquiv (X ◁ f) (X ◁ f')
  | whiskerRight {X Y} {f f' : X ⟶ Y} (Z) : HomEquiv f f' → HomEquiv (f ▷ Z) (f' ▷ Z)
  | crossing_crossingInv (X Y) : HomEquiv (crossing X Y ≫ crossingInv X Y) (𝟙 _)
  | crossingInv_crossing (X Y) : HomEquiv (crossingInv X Y ≫ crossing X Y) (𝟙 _)
  | naturality_right (X) {Y Z} (f : Y ⟶ Z) :
      HomEquiv (X ◁ f ≫ crossing X Z) (crossing X Y ≫ f ▷ X)
  | naturality_left {X Y} (f : X ⟶ Y) (Z) :
      HomEquiv (f ▷ Z ≫ crossing Y Z) (crossing X Z ≫ Z ◁ f)
  | hexagon_forward (X Y Z) :
      HomEquiv ((α_ X Y Z).hom ≫ crossing X (Y ⊗ Z) ≫ (α_ Y Z X).hom)
        (crossing X Y ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ crossing X Z)
  | hexagon_reverse (X Y Z) :
      HomEquiv ((α_ X Y Z).inv ≫ crossing (X ⊗ Y) Z ≫ (α_ Z X Y).inv)
        (X ◁ crossing Y Z ≫ (α_ X Z Y).inv ≫ crossing X Z ▷ Y)

/-- Morphisms of the free monoidal category on `S.withCrossings` are identified when the axioms
of a braided monoidal category make them equal. -/
instance setoidHom (X Y : S.withCrossings.FreeMonoidal) : Setoid (X ⟶ Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm, HomEquiv.trans⟩⟩

instance : Category.{max u v} S.FreeBraided where
  Hom X Y := Quotient (setoidHom X.as Y.as)
  id X := ⟦𝟙 X.as⟧
  comp := Quotient.map₂ (· ≫ ·) fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg
  id_comp := by
    rintro X Y ⟨f⟩
    exact congrArg (⟦·⟧) (Category.id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact congrArg (⟦·⟧) (Category.comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact congrArg (⟦·⟧) (Category.assoc f g h)

/-- The morphism of the free braided monoidal category represented by a morphism of the free
monoidal category on `S.withCrossings`. -/
abbrev homMk {X Y : S.FreeBraided} (f : X.as ⟶ Y.as) : X ⟶ Y := ⟦f⟧

theorem homMk_eq_homMk_iff {X Y : S.FreeBraided} {f g : X.as ⟶ Y.as} :
    homMk f = homMk g ↔ HomEquiv f g :=
  Quotient.eq

/-- Induction principle for morphisms of the free braided monoidal category: every morphism is
represented by a morphism of the free monoidal category on `S.withCrossings`. -/
@[elab_as_elim]
theorem Hom.inductionOn {X Y : S.FreeBraided} {motive : (X ⟶ Y) → Prop} (t : X ⟶ Y)
    (h : ∀ f, motive (homMk f)) : motive t :=
  Quotient.inductionOn t h

@[simp]
theorem homMk_id (X : S.FreeBraided) : homMk (𝟙 X.as) = 𝟙 X := rfl

@[simp]
theorem homMk_comp {X Y Z : S.FreeBraided} (f : X.as ⟶ Y.as) (g : Y.as ⟶ Z.as) :
    homMk (f ≫ g) = homMk f ≫ homMk g := rfl

instance : MonoidalCategory S.FreeBraided where
  tensorObj X Y := ⟨X.as ⊗ Y.as⟩
  tensorHom := Quotient.map₂ (· ⊗ₘ ·) fun _ _ hf _ _ hg ↦ by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def]
    exact HomEquiv.comp (HomEquiv.whiskerRight _ hf) (HomEquiv.whiskerLeft _ hg)
  whiskerLeft X _ _ := Quotient.map (X.as ◁ ·) fun _ _ ↦ HomEquiv.whiskerLeft _
  whiskerRight f Y := Quotient.map (· ▷ Y.as) (fun _ _ ↦ HomEquiv.whiskerRight _) f
  tensorHom_def := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩
    exact congrArg (⟦·⟧) (MonoidalCategory.tensorHom_def f g)
  id_tensorHom_id X Y := congrArg (⟦·⟧) (MonoidalCategory.id_tensorHom_id X.as Y.as)
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact congrArg (⟦·⟧) (MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂)
  whiskerLeft_id X Y := congrArg (⟦·⟧) (MonoidalCategory.whiskerLeft_id X.as Y.as)
  id_whiskerRight X Y := congrArg (⟦·⟧) (MonoidalCategory.id_whiskerRight X.as Y.as)
  tensorUnit := ⟨𝟙_ _⟩
  associator X Y Z :=
    ⟨⟦(α_ X.as Y.as Z.as).hom⟧, ⟦(α_ X.as Y.as Z.as).inv⟧, congrArg (⟦·⟧) (Iso.hom_inv_id _),
      congrArg (⟦·⟧) (Iso.inv_hom_id _)⟩
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact congrArg (⟦·⟧) (MonoidalCategory.associator_naturality f₁ f₂ f₃)
  leftUnitor X :=
    ⟨⟦(λ_ X.as).hom⟧, ⟦(λ_ X.as).inv⟧, congrArg (⟦·⟧) (Iso.hom_inv_id _),
      congrArg (⟦·⟧) (Iso.inv_hom_id _)⟩
  leftUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact congrArg (⟦·⟧) (MonoidalCategory.leftUnitor_naturality f)
  rightUnitor X :=
    ⟨⟦(ρ_ X.as).hom⟧, ⟦(ρ_ X.as).inv⟧, congrArg (⟦·⟧) (Iso.hom_inv_id _),
      congrArg (⟦·⟧) (Iso.inv_hom_id _)⟩
  rightUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact congrArg (⟦·⟧) (MonoidalCategory.rightUnitor_naturality f)
  pentagon W X Y Z := by exact congrArg (⟦·⟧) (MonoidalCategory.pentagon W.as X.as Y.as Z.as)
  triangle X Y := by exact congrArg (⟦·⟧) (MonoidalCategory.triangle X.as Y.as)

@[simp]
theorem mk_as (X : S.FreeBraided) : (⟨X.as⟩ : S.FreeBraided) = X := rfl

@[simp]
theorem tensorObj_as (X Y : S.FreeBraided) : (X ⊗ Y).as = X.as ⊗ Y.as := rfl

@[simp]
theorem tensorUnit_as : (𝟙_ S.FreeBraided).as = 𝟙_ S.withCrossings.FreeMonoidal := rfl

instance : BraidedCategory S.FreeBraided where
  braiding X Y :=
    ⟨⟦crossing X.as Y.as⟧, ⟦crossingInv X.as Y.as⟧,
      Quotient.sound (HomEquiv.crossing_crossingInv _ _),
      Quotient.sound (HomEquiv.crossingInv_crossing _ _)⟩
  braiding_naturality_right := by
    rintro X _ _ ⟨f⟩
    exact Quotient.sound (HomEquiv.naturality_right _ f)
  braiding_naturality_left := by
    rintro _ _ ⟨f⟩ Z
    exact Quotient.sound (HomEquiv.naturality_left f _)
  hexagon_forward _ _ _ := Quotient.sound (HomEquiv.hexagon_forward _ _ _)
  hexagon_reverse _ _ _ := Quotient.sound (HomEquiv.hexagon_reverse _ _ _)

/-- The generating morphism given by a coupon of `S`, from its source word to its target word. -/
@[expose] def coupon (g : S.Coupon) :
    (⟨⟨S.src g⟩⟩ : S.FreeBraided) ⟶ ⟨⟨S.tgt g⟩⟩ :=
  homMk (FreeMonoidal.coupon (S := S.withCrossings) (.coupon g))

@[simp]
theorem homMk_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Y₁.as ⟶ Y₂.as) :
    homMk (X := X ⊗ Y₁) (Y := X ⊗ Y₂) (X.as ◁ f) = X ◁ homMk f := rfl

@[simp]
theorem homMk_whiskerRight {X₁ X₂ : S.FreeBraided} (f : X₁.as ⟶ X₂.as) (Y : S.FreeBraided) :
    homMk (X := X₁ ⊗ Y) (Y := X₂ ⊗ Y) (f ▷ Y.as) = homMk f ▷ Y := rfl

@[simp]
theorem homMk_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁.as ⟶ Y₁.as) (g : X₂.as ⟶ Y₂.as) :
    homMk (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (f ⊗ₘ g) = homMk f ⊗ₘ homMk g := rfl

@[simp]
theorem homMk_associator_hom (X Y Z : S.FreeBraided) :
    homMk (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (α_ X.as Y.as Z.as).hom = (α_ X Y Z).hom := rfl

@[simp]
theorem homMk_associator_inv (X Y Z : S.FreeBraided) :
    homMk (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z) (α_ X.as Y.as Z.as).inv = (α_ X Y Z).inv := rfl

@[simp]
theorem homMk_leftUnitor_hom (X : S.FreeBraided) :
    homMk (X := 𝟙_ _ ⊗ X) (λ_ X.as).hom = (λ_ X).hom := rfl

@[simp]
theorem homMk_leftUnitor_inv (X : S.FreeBraided) :
    homMk (Y := 𝟙_ _ ⊗ X) (λ_ X.as).inv = (λ_ X).inv := rfl

@[simp]
theorem homMk_rightUnitor_hom (X : S.FreeBraided) :
    homMk (X := X ⊗ 𝟙_ _) (ρ_ X.as).hom = (ρ_ X).hom := rfl

@[simp]
theorem homMk_rightUnitor_inv (X : S.FreeBraided) :
    homMk (Y := X ⊗ 𝟙_ _) (ρ_ X.as).inv = (ρ_ X).inv := rfl

@[simp]
theorem homMk_crossing (X Y : S.FreeBraided) :
    homMk (X := X ⊗ Y) (Y := Y ⊗ X) (crossing X.as Y.as) = (β_ X Y).hom := rfl

@[simp]
theorem homMk_crossingInv (X Y : S.FreeBraided) :
    homMk (X := Y ⊗ X) (Y := X ⊗ Y) (crossingInv X.as Y.as) = (β_ X Y).inv := rfl

@[simp]
theorem homMk_coupon (g : S.Coupon) :
    homMk (X := ⟨⟨S.src g⟩⟩) (Y := ⟨⟨S.tgt g⟩⟩)
      (FreeMonoidal.coupon (S := S.withCrossings) (.coupon g)) = coupon g := rfl

/-! ### The quotient functor -/

section QuotientFunctor

/-- The quotient functor from the free monoidal category on `S.withCrossings` to the free braided
monoidal category on `S`. It is bijective on objects, and it is strict monoidal. -/
@[expose] def quotientFunctor : S.withCrossings.FreeMonoidal ⥤ S.FreeBraided where
  obj X := ⟨X⟩
  map f := homMk f

@[simp]
theorem quotientFunctor_obj (X : S.withCrossings.FreeMonoidal) : quotientFunctor.obj X = ⟨X⟩ :=
  rfl

@[simp]
theorem quotientFunctor_map {X Y : S.withCrossings.FreeMonoidal} (f : X ⟶ Y) :
    quotientFunctor.map f = homMk f :=
  rfl

/- The tensorator and unit comparison of the quotient functor are identities; every coherence
goal is the image of an identity of the free monoidal category on `S.withCrossings`. -/
instance : (quotientFunctor (S := S)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by intros; exact congrArg (⟦·⟧) (by simp)
      μIso_hom_natural_right := by intros; exact congrArg (⟦·⟧) (by simp)
      associativity := by intros; exact congrArg (⟦·⟧) (by simp)
      left_unitality := by intros; exact congrArg (⟦·⟧) (by simp)
      right_unitality := by intros; exact congrArg (⟦·⟧) (by simp) }

@[simp]
theorem quotientFunctor_ε : Functor.LaxMonoidal.ε (quotientFunctor (S := S)) = 𝟙 _ := rfl

@[simp]
theorem quotientFunctor_η : Functor.OplaxMonoidal.η (quotientFunctor (S := S)) = 𝟙 _ := rfl

@[simp]
theorem quotientFunctor_μ (X Y : S.withCrossings.FreeMonoidal) :
    Functor.LaxMonoidal.μ quotientFunctor X Y = 𝟙 _ :=
  rfl

@[simp]
theorem quotientFunctor_δ (X Y : S.withCrossings.FreeMonoidal) :
    Functor.OplaxMonoidal.δ quotientFunctor X Y = 𝟙 _ :=
  rfl

end QuotientFunctor

/-! ### The universal property: existence -/

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D) (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))

/-- The interpretation of the coupons of `S.withCrossings` in a braided monoidal category:
coupons of `S` act by `fc`, and the crossings act by the braiding and its inverse. -/
@[expose] def liftCoupon :
    ∀ g : S.withCrossings.Coupon,
      projectObj fo (S.withCrossings.src g) ⟶ projectObj fo (S.withCrossings.tgt g)
  | .coupon g => fc g
  | .crossing X Y => (β_ (projectObj fo X) (projectObj fo Y)).hom
  | .crossingInv X Y => (β_ (projectObj fo X) (projectObj fo Y)).inv

/-- The interpretation of morphisms of the free monoidal category on `S.withCrossings` respects
the axioms of a braided monoidal category. -/
theorem map_eq_map_of_homEquiv {X Y : S.withCrossings.FreeMonoidal} {f g : X ⟶ Y}
    (h : HomEquiv f g) :
    (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map f =
      (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map g := by
  induction h with
  | refl => rfl
  | symm _ hfg => exact hfg.symm
  | trans _ _ hfg hgh => exact hfg.trans hgh
  | comp _ _ hf hg => rw [Functor.map_comp, Functor.map_comp, hf, hg]
  | whiskerLeft _ _ hf => rw [FreeMonoidal.lift_map_whiskerLeft, hf,
      FreeMonoidal.lift_map_whiskerLeft]
  | whiskerRight _ _ hf => rw [FreeMonoidal.lift_map_whiskerRight, hf,
      FreeMonoidal.lift_map_whiskerRight]
  | crossing_crossingInv X Y =>
    simp only [crossing, crossingInv, Functor.map_comp, FreeMonoidal.lift_map_coupon,
      Functor.map_id]
    exact (β_ (projectObj fo X.as) (projectObj fo Y.as)).hom_inv_id
  | crossingInv_crossing X Y =>
    simp only [crossing, crossingInv, Functor.map_comp, FreeMonoidal.lift_map_coupon,
      Functor.map_id]
    exact (β_ (projectObj fo X.as) (projectObj fo Y.as)).inv_hom_id
  | naturality_right X f =>
    simp only [crossing, Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon]
    exact BraidedCategory.braiding_naturality_right _ _
  | naturality_left f Z =>
    simp only [crossing, Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon]
    exact BraidedCategory.braiding_naturality_left _ _
  | hexagon_forward X Y Z =>
    simp only [crossing, Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon,
      FreeMonoidal.lift_map_associator_hom]
    exact BraidedCategory.hexagon_forward _ _ _
  | hexagon_reverse X Y Z =>
    simp only [crossing, Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon,
      FreeMonoidal.lift_map_associator_inv]
    exact BraidedCategory.hexagon_reverse _ _ _

/-- The interpretation of morphisms of the free braided monoidal category on `S`, given the
images `fo` of the generating objects and `fc` of the coupons. This is the action of
`FreeBraided.lift` on morphisms; use the `lift_map_*` lemmas to compute it. -/
def liftMap {X Y : S.FreeBraided} (f : X ⟶ Y) :
    (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).obj X.as ⟶
      (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).obj Y.as :=
  Quotient.lift (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map
    (fun _ _ h ↦ map_eq_map_of_homEquiv fo fc h) f

/-- The functor out of the free braided monoidal category on `S` determined by the images `fo`
of the generating objects and `fc` of the coupons. It is strong braided monoidal, with identity
tensorator and unit comparison. -/
@[expose] def lift : S.FreeBraided ⥤ D where
  obj X := (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).obj X.as
  map := liftMap fo fc
  map_id X := by
    exact (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map_id X.as
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map_comp f g

/-- The lift out of the free braided monoidal category restricts along the quotient functor to the
lift out of the free monoidal category on `S.withCrossings`. -/
theorem quotientFunctor_comp_lift :
    quotientFunctor ⋙ lift fo fc =
      FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc) := by
  rfl

@[simp]
theorem lift_map_homMk {X Y : S.FreeBraided} (f : X.as ⟶ Y.as) :
    (lift fo fc).map (homMk f) =
      (FreeMonoidal.lift (S := S.withCrossings) fo (liftCoupon fo fc)).map f := by
  rfl

@[simp]
theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := rfl

@[simp]
theorem lift_obj_tensor (X Y : S.FreeBraided) :
    (lift fo fc).obj (X ⊗ Y) = (lift fo fc).obj X ⊗ (lift fo fc).obj Y := rfl

@[simp]
theorem lift_obj_tensorUnit : (lift fo fc).obj (𝟙_ S.FreeBraided) = 𝟙_ D := rfl

@[simp]
theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g := by
  exact FreeMonoidal.lift_map_coupon (S := S.withCrossings) fo (liftCoupon fo fc) (.coupon g)

@[simp]
theorem lift_map_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Y₁ ⟶ Y₂) :
    (lift fo fc).map (X ◁ f) = (lift fo fc).obj X ◁ (lift fo fc).map f := by
  induction f using Hom.inductionOn with | h f
  exact FreeMonoidal.lift_map_whiskerLeft _ _ X.as f

@[simp]
theorem lift_map_whiskerRight {X₁ X₂ : S.FreeBraided} (f : X₁ ⟶ X₂) (Y : S.FreeBraided) :
    (lift fo fc).map (f ▷ Y) = (lift fo fc).map f ▷ (lift fo fc).obj Y := by
  induction f using Hom.inductionOn with | h f
  exact FreeMonoidal.lift_map_whiskerRight _ _ f Y.as

@[simp]
theorem lift_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (lift fo fc).map (f ⊗ₘ g) = (lift fo fc).map f ⊗ₘ (lift fo fc).map g := by
  induction f using Hom.inductionOn with | h f
  induction g using Hom.inductionOn with | h g
  exact FreeMonoidal.lift_map_tensorHom _ _ f g

@[simp]
theorem lift_map_associator_hom (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).hom =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom := by
  exact FreeMonoidal.lift_map_associator_hom _ _ X.as Y.as Z.as

@[simp]
theorem lift_map_associator_inv (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).inv =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).inv := by
  exact FreeMonoidal.lift_map_associator_inv _ _ X.as Y.as Z.as

/- The unitor and braiding lemmas are not `@[simp]`: the Mathlib simp lemmas
`Functor.LaxMonoidal.left_unitality`, `right_unitality` and `Functor.map_braiding` rewrite their
right-hand sides back into `(lift fo fc).map` of a unitor or of the braiding. -/
theorem lift_map_leftUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).hom = (λ_ ((lift fo fc).obj X)).hom := by
  exact FreeMonoidal.lift_map_leftUnitor_hom _ _ X.as

theorem lift_map_leftUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).inv = (λ_ ((lift fo fc).obj X)).inv := by
  exact FreeMonoidal.lift_map_leftUnitor_inv _ _ X.as

theorem lift_map_rightUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).hom = (ρ_ ((lift fo fc).obj X)).hom := by
  exact FreeMonoidal.lift_map_rightUnitor_hom _ _ X.as

theorem lift_map_rightUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).inv = (ρ_ ((lift fo fc).obj X)).inv := by
  exact FreeMonoidal.lift_map_rightUnitor_inv _ _ X.as

theorem lift_map_braiding_hom (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).hom = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).hom := by
  exact FreeMonoidal.lift_map_coupon (S := S.withCrossings) fo (liftCoupon fo fc)
    (.crossing X.as.as Y.as.as)

theorem lift_map_braiding_inv (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).inv = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).inv := by
  exact FreeMonoidal.lift_map_coupon (S := S.withCrossings) fo (liftCoupon fo fc)
    (.crossingInv X.as.as Y.as.as)

/- The tensorator and unit comparison of `lift fo fc` are identities. The coherence goals mix
the objects `(lift fo fc).obj (X ⊗ Y)` and `(lift fo fc).obj X ⊗ (lift fo fc).obj Y`, which agree
only after unfolding `lift`, so `dsimp only [lift_obj_tensor, lift_obj_tensorUnit]` first aligns
them syntactically for `simp`. -/
instance : (lift fo fc).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      μIso_hom_natural_right := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      associativity := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      left_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_leftUnitor_hom]
      right_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_rightUnitor_hom] }

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := rfl

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := rfl

@[simp]
theorem lift_μ (X Y : S.FreeBraided) : Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := rfl

@[simp]
theorem lift_δ (X Y : S.FreeBraided) : Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := rfl

instance : (lift fo fc).Braided where
  braided X Y := by
    exact (Category.id_comp _).trans
      ((lift_map_braiding_hom fo fc X Y).trans (Category.comp_id _).symm)

end Lift

/-! ### The universal property: uniqueness -/

section Uniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of the free braided
monoidal category on `S` to a lax monoidal one is determined by its components at the generating
objects. -/
theorem natTrans_ext {F G : S.FreeBraided ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ a, α.app (of a) = β.app (of a)) :
    α = β := by
  have := FreeMonoidal.natTrans_ext (α := Functor.whiskerLeft quotientFunctor α)
    (β := Functor.whiskerLeft quotientFunctor β) h
  ext X
  exact congrArg (fun γ ↦ γ.app X.as) this

section WordIso

variable (F G : S.FreeBraided ⥤ D) [F.Monoidal] [G.Monoidal] (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a tensor word under two strong monoidal functors out
of the free braided monoidal category, induced by isomorphisms `e` at the generating objects
together with the tensorators and unit comparisons of the two functors. -/
def wordIso (X : S.FreeBraided) : F.obj X ≅ G.obj X :=
  FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e X.as.as

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (of a) = e a := by
  exact FreeMonoidal.wordIso_of (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e a

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeBraided)).hom = η F ≫ ε G := by
  refine (FreeMonoidal.wordIso_tensorUnit_hom (quotientFunctor ⋙ F) (quotientFunctor ⋙ G)
    e).trans ?_
  simp

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeBraided) :
    (wordIso F G e (X ⊗ Y)).hom =
      δ F X Y ≫ ((wordIso F G e X).hom ⊗ₘ (wordIso F G e Y).hom) ≫ μ G X Y := by
  refine (FreeMonoidal.wordIso_tensor_hom (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e X.as
    Y.as).trans ?_
  simp [wordIso]

end WordIso

variable [BraidedCategory D] {F G : S.FreeBraided ⥤ D} [F.Braided] [G.Braided]
  {e : ∀ a, F.obj (of a) ≅ G.obj (of a)}

/-- The isomorphisms `wordIso F G e` commute with the braidings. -/
@[reassoc]
theorem map_braiding_hom_comp_wordIso_hom (X Y : S.FreeBraided) :
    F.map (β_ X Y).hom ≫ (wordIso F G e (Y ⊗ X)).hom =
      (wordIso F G e (X ⊗ Y)).hom ≫ G.map (β_ X Y).hom := by
  simp [BraidedCategory.braiding_naturality_assoc]

/-- The isomorphisms `wordIso F G e` commute with the inverse braidings. -/
theorem map_braiding_inv_comp_wordIso_hom (X Y : S.FreeBraided) :
    F.map (β_ X Y).inv ≫ (wordIso F G e (X ⊗ Y)).hom =
      (wordIso F G e (Y ⊗ X)).hom ≫ G.map (β_ X Y).inv := by
  rw [← cancel_epi (F.map (β_ X Y).hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp, map_braiding_hom_comp_wordIso_hom_assoc,
    ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]

/-- The isomorphisms `wordIso F G e` are natural as soon as they are natural with respect to
the coupons. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e ⟨⟨S.tgt g⟩⟩).hom =
      (wordIso F G e ⟨⟨S.src g⟩⟩).hom ≫ G.map (coupon g))
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y).hom = (wordIso F G e X).hom ≫ G.map f := by
  induction f using Hom.inductionOn with | h f
  refine FreeMonoidal.map_comp_wordIso_hom (F := quotientFunctor ⋙ F) (G := quotientFunctor ⋙ G)
    (fun g ↦ ?_) f
  cases g with
  | coupon g => exact he g
  | crossing X Y => exact map_braiding_hom_comp_wordIso_hom ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩
  | crossingInv X Y => exact map_braiding_inv_comp_wordIso_hom ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩

/-- Two strong braided monoidal functors out of the free braided monoidal category on `S` that
agree up to isomorphisms `e` on the generating objects, compatibly with every coupon of `S`, are
isomorphic by a monoidal natural isomorphism extending `e`. -/
def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e ⟨⟨S.tgt g⟩⟩).hom =
      (wordIso F G e ⟨⟨S.src g⟩⟩).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ wordIso F G e X) fun f ↦ map_comp_wordIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e ⟨⟨S.tgt g⟩⟩).hom =
  (wordIso F G e ⟨⟨S.src g⟩⟩).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeBraided) :
    (monoidalNatIso he).hom.app X = (wordIso F G e X).hom := by
  rfl

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by
  rw [monoidalNatIso_hom_app, wordIso_of]

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, wordIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, wordIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

end Uniqueness

end FreeBraided

end TensorSignature

end TauCeti
