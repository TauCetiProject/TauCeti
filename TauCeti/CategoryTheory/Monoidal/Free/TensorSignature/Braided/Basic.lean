/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.CategoryTheory.Monoidal.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.Presentation

/-!
# The free braided monoidal category on a tensor signature

Given a tensor signature `S : TauCeti.TensorSignature`, the free braided monoidal category
`TauCeti.TensorSignature.FreeBraided S` has formal tensor words in `S.Obj` as objects and is
constructed by adjoining formal braiding and inverse braiding generators for every pair of words
to `S` (`S.braidedSignature`) and quotienting `S.braidedSignature.FreeMonoidal` by the braided
monoidal axioms (`BraidedRel S`), via the monoidal presentation machinery of
`TauCeti.CategoryTheory.Monoidal.Presentation`.

Its universal property characterizes strong braided functors `S.FreeBraided ⥤ D` into an arbitrary
(not necessarily strict) braided monoidal category `D`: any choice of images `fo` of the
generating objects and `fc` of the coupons extends to a strong braided functor
`FreeBraided.lift fo fc`, which is unique up to a unique monoidal natural isomorphism extending
given isomorphisms on the generating objects (`FreeBraided.monoidalNatIso` and
`FreeBraided.natTrans_ext`).

No extra equations beyond the braided monoidal axioms are imposed. In particular, the
multiplicative crossing-weight invariant `FreeBraided.crossingWeight` into
`WithZero (Multiplicative ℤ)` assigns `WithZero.exp (m * n)` to the braiding of words of lengths
`m` and `n`, `WithZero.exp (-(m * n))` to the inverse braiding, and `0` to coupons. It shows that
for every pair of generating objects `a, b : S.Obj`, the integer powers of the double braiding
`β_ (of a) (of b) ≪≫ β_ (of b) (of a)` are pairwise distinct
(`FreeBraided.doubleBraiding_zpow_injective`), so `S.FreeBraided` is never symmetric when `S.Obj`
is nonempty (`FreeBraided.not_symmetricCategory`).

## Main definitions and results

* `TauCeti.TensorSignature.BraidedCoupon S`, `TauCeti.TensorSignature.braidedSignature S`,
  `TauCeti.TensorSignature.BraidedRel S`, and `TauCeti.TensorSignature.FreeBraided S`:
  the presentation of the free braided monoidal category on `S`.
* `FreeBraided.ofWord`, `FreeBraided.of`, `FreeBraided.word`, `FreeBraided.RawHom`,
  `FreeBraided.homMk`, `FreeBraided.coupon`, and `FreeBraided.hom_inductionOn`.
* `FreeBraided.lift fo fc`: the strong braided functor into an arbitrary braided monoidal
  category determined by images of generating objects and coupons, with computation lemmas.
* `FreeBraided.natTrans_ext`, `FreeBraided.wordIso`, and `FreeBraided.monoidalNatIso`: uniqueness
  of strong braided functors out of `S.FreeBraided` up to unique monoidal natural isomorphism.
* `FreeBraided.wordLength`, `FreeBraided.crossingWeight`,
  `FreeBraided.crossingWeight_doubleBraiding`, `FreeBraided.doubleBraiding_zpow_injective`,
  `FreeBraided.doubleBraiding_ne_id`, and `FreeBraided.not_symmetricCategory`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. 102 (1993), 20–78.
* P. Selinger, *A survey of graphical languages for monoidal categories*, Lecture Notes in Physics
  813 (2011), §3.3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- The generating morphisms of the signature `S.braidedSignature`: the coupons of `S` together
with formal braiding and inverse braiding morphisms on every pair of formal tensor words. -/
inductive BraidedCoupon (S : TensorSignature.{u, v}) : Type (max u v)
  | coupon (g : S.Coupon) : BraidedCoupon S
  | β_hom (X Y : FreeMonoidalCategory S.Obj) : BraidedCoupon S
  | β_inv (X Y : FreeMonoidalCategory S.Obj) : BraidedCoupon S

/-- The tensor signature obtained from `S` by adjoining formal braiding and inverse braiding
generators for every pair of tensor words. -/
abbrev braidedSignature (S : TensorSignature.{u, v}) : TensorSignature.{u, max u v} where
  Obj := S.Obj
  Coupon := BraidedCoupon S
  src
    | .coupon g => S.src g
    | .β_hom X Y => X.tensor Y
    | .β_inv X Y => Y.tensor X
  tgt
    | .coupon g => S.tgt g
    | .β_hom X Y => Y.tensor X
    | .β_inv X Y => X.tensor Y

/-- The defining equations of a braided monoidal category on `S.braidedSignature.FreeMonoidal`:
the inverse laws, left and right naturality, and the forward and reverse hexagon identities. -/
inductive BraidedRel (S : TensorSignature.{u, v}) : HomRel S.braidedSignature.FreeMonoidal
  | β_hom_inv (X Y : FreeMonoidalCategory S.Obj) :
      BraidedRel S
        (FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y) ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_inv X Y))
        (𝟙 (FreeMonoidal.mk (S := S.braidedSignature) (X.tensor Y)))
  | β_inv_hom (X Y : FreeMonoidalCategory S.Obj) :
      BraidedRel S
        (FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_inv X Y) ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y))
        (𝟙 (FreeMonoidal.mk (S := S.braidedSignature) (Y.tensor X)))
  | braiding_naturality_right (X : FreeMonoidalCategory S.Obj)
      {Y₁ Y₂ : FreeMonoidalCategory S.Obj}
      (f : FreeMonoidal.mk (S := S.braidedSignature) Y₁ ⟶
        FreeMonoidal.mk (S := S.braidedSignature) Y₂) :
      BraidedRel S
        (FreeMonoidal.mk (S := S.braidedSignature) X ◁ f ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y₂))
        (FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y₁) ≫
          f ▷ FreeMonoidal.mk (S := S.braidedSignature) X)
  | braiding_naturality_left {X₁ X₂ : FreeMonoidalCategory S.Obj}
      (f : FreeMonoidal.mk (S := S.braidedSignature) X₁ ⟶
        FreeMonoidal.mk (S := S.braidedSignature) X₂)
      (Y : FreeMonoidalCategory S.Obj) :
      BraidedRel S
        (f ▷ FreeMonoidal.mk (S := S.braidedSignature) Y ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X₂ Y))
        (FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X₁ Y) ≫
          FreeMonoidal.mk (S := S.braidedSignature) Y ◁ f)
  | hexagon_forward (X Y Z : FreeMonoidalCategory S.Obj) :
      BraidedRel S
        ((α_ (FreeMonoidal.mk (S := S.braidedSignature) X)
            (FreeMonoidal.mk (S := S.braidedSignature) Y)
            (FreeMonoidal.mk (S := S.braidedSignature) Z)).hom ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X (Y.tensor Z)) ≫
          (α_ (FreeMonoidal.mk (S := S.braidedSignature) Y)
            (FreeMonoidal.mk (S := S.braidedSignature) Z)
            (FreeMonoidal.mk (S := S.braidedSignature) X)).hom)
        (FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y) ▷
            FreeMonoidal.mk (S := S.braidedSignature) Z ≫
          (α_ (FreeMonoidal.mk (S := S.braidedSignature) Y)
            (FreeMonoidal.mk (S := S.braidedSignature) X)
            (FreeMonoidal.mk (S := S.braidedSignature) Z)).hom ≫
          FreeMonoidal.mk (S := S.braidedSignature) Y ◁
            FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Z))
  | hexagon_reverse (X Y Z : FreeMonoidalCategory S.Obj) :
      BraidedRel S
        ((α_ (FreeMonoidal.mk (S := S.braidedSignature) X)
            (FreeMonoidal.mk (S := S.braidedSignature) Y)
            (FreeMonoidal.mk (S := S.braidedSignature) Z)).inv ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom (X.tensor Y) Z) ≫
          (α_ (FreeMonoidal.mk (S := S.braidedSignature) Z)
            (FreeMonoidal.mk (S := S.braidedSignature) X)
            (FreeMonoidal.mk (S := S.braidedSignature) Y)).inv)
        (FreeMonoidal.mk (S := S.braidedSignature) X ◁
            FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom Y Z) ≫
          (α_ (FreeMonoidal.mk (S := S.braidedSignature) X)
            (FreeMonoidal.mk (S := S.braidedSignature) Z)
            (FreeMonoidal.mk (S := S.braidedSignature) Y)).inv ≫
          FreeMonoidal.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Z) ▷
            FreeMonoidal.mk (S := S.braidedSignature) Y)

/-- The free braided monoidal category on a tensor signature `S`. Its objects are formal tensor
words in `S.Obj`, and its morphisms are generated by identities, associators, unitors, braidings,
inverse braidings, and the coupons of `S`, modulo exactly the axioms of a braided monoidal
category. -/
abbrev FreeBraided (S : TensorSignature.{u, v}) : Type u :=
  S.braidedSignature.Presented (BraidedRel S)

namespace FreeBraided

variable {S : TensorSignature.{u, v}}

/-- The object of `S.FreeBraided` corresponding to a formal tensor word in `S.Obj`. -/
@[expose] def ofWord (X : FreeMonoidalCategory S.Obj) : S.FreeBraided :=
  (Presented.quotientFunctor (BraidedRel S)).obj ⟨X⟩

/-- The object of `S.FreeBraided` given by a single generating object. -/
@[expose] def of (a : S.Obj) : S.FreeBraided :=
  ofWord (.of a)

/-- The underlying formal tensor word of an object of `S.FreeBraided`. -/
@[expose] def word (X : S.FreeBraided) : FreeMonoidalCategory S.Obj :=
  X.as.as

@[simp]
theorem ofWord_of (a : S.Obj) : ofWord (.of a) = of a := rfl

@[simp]
theorem ofWord_tensorUnit : ofWord (𝟙_ (FreeMonoidalCategory S.Obj)) = 𝟙_ S.FreeBraided := rfl

@[simp]
theorem ofWord_tensor (X Y : FreeMonoidalCategory S.Obj) :
    ofWord (X ⊗ Y) = ofWord X ⊗ ofWord Y := rfl

@[simp]
theorem word_ofWord (X : FreeMonoidalCategory S.Obj) : (ofWord X).word = X := rfl

@[simp]
theorem ofWord_word (X : S.FreeBraided) : ofWord X.word = X := rfl

@[simp]
theorem word_of (a : S.Obj) : (of a).word = .of a := rfl

@[simp]
theorem word_tensorUnit : (𝟙_ S.FreeBraided).word = .unit := rfl

@[simp]
theorem word_tensor (X Y : S.FreeBraided) : (X ⊗ Y).word = X.word.tensor Y.word := rfl

/-- Raw braided morphism expressions between formal tensor words in `S.Obj`: formal composites,
tensor products, and whiskerings of identities, associators, unitors, braidings, inverse braidings,
and coupons of `S`. -/
abbrev RawHom (X Y : FreeMonoidalCategory S.Obj) : Type (max u v) :=
  FreeMonoidal.Hom (S := S.braidedSignature) X Y

/-- The raw morphism expression for a coupon of `S`. -/
@[expose] def RawHom.ofCoupon (g : S.Coupon) : RawHom (S := S) (S.src g) (S.tgt g) :=
  FreeMonoidal.Hom.coupon (S := S.braidedSignature) (BraidedCoupon.coupon g)

/-- The raw morphism expression for a formal braiding. -/
@[expose] def RawHom.braidingHom (X Y : FreeMonoidalCategory S.Obj) :
    RawHom (S := S) (X.tensor Y) (Y.tensor X) :=
  FreeMonoidal.Hom.coupon (S := S.braidedSignature) (BraidedCoupon.β_hom X Y)

/-- The raw morphism expression for a formal inverse braiding. -/
@[expose] def RawHom.braidingInv (X Y : FreeMonoidalCategory S.Obj) :
    RawHom (S := S) (Y.tensor X) (X.tensor Y) :=
  FreeMonoidal.Hom.coupon (S := S.braidedSignature) (BraidedCoupon.β_inv X Y)

/-- The morphism of `S.FreeBraided` represented by a raw braided morphism expression. -/
@[expose] def homMk {X Y : S.FreeBraided} (f : RawHom X.word Y.word) : X ⟶ Y :=
  (Presented.quotientFunctor (BraidedRel S)).map (FreeMonoidal.homMk f)

/-- The generating morphism of `S.FreeBraided` given by a coupon of `S`. -/
@[expose] def coupon (g : S.Coupon) : ofWord (S.src g) ⟶ ofWord (S.tgt g) :=
  homMk (.ofCoupon g)

instance : BraidedCategory S.FreeBraided where
  braiding X Y :=
    { hom := homMk (.braidingHom X.word Y.word)
      inv := homMk (.braidingInv X.word Y.word)
      hom_inv_id := Presented.sound (.β_hom_inv X.word Y.word)
      inv_hom_id := Presented.sound (.β_inv_hom X.word Y.word) }
  braiding_naturality_right X Y Z f := by
    obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
    exact Presented.sound (.braiding_naturality_right X.word f)
  braiding_naturality_left f Z := by
    obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
    exact Presented.sound (.braiding_naturality_left f Z.word)
  hexagon_forward X Y Z := Presented.sound (.hexagon_forward X.word Y.word Z.word)
  hexagon_reverse X Y Z := Presented.sound (.hexagon_reverse X.word Y.word Z.word)

@[simp]
theorem homMk_id (X : S.FreeBraided) :
    homMk (FreeMonoidal.Hom.id (S := S.braidedSignature) X.word) = 𝟙 X := rfl

@[simp]
theorem homMk_comp {X Y Z : S.FreeBraided} (f : RawHom X.word Y.word) (g : RawHom Y.word Z.word) :
    homMk (Y := Z) (f.comp g) = homMk f ≫ homMk g := rfl

@[simp]
theorem homMk_tensor {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : RawHom X₁.word Y₁.word)
    (g : RawHom X₂.word Y₂.word) :
    homMk (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (f.tensor g) = homMk f ⊗ₘ homMk g :=
  (CategoryTheory.Quotient.map_tensorHom_map (FreeMonoidal.homMk f) (FreeMonoidal.homMk g)).symm

@[simp]
theorem homMk_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided}
    (f : RawHom Y₁.word Y₂.word) :
    homMk (X := X ⊗ Y₁) (Y := X ⊗ Y₂)
      (FreeMonoidal.Hom.whiskerLeft (S := S.braidedSignature) X.word f) = X ◁ homMk f := rfl

@[simp]
theorem homMk_whiskerRight {X₁ X₂ : S.FreeBraided} (f : RawHom X₁.word X₂.word)
    (Y : S.FreeBraided) :
    homMk (X := X₁ ⊗ Y) (Y := X₂ ⊗ Y)
      (FreeMonoidal.Hom.whiskerRight (S := S.braidedSignature) f Y.word) = homMk f ▷ Y := rfl

@[simp]
theorem homMk_α_hom (X Y Z : S.FreeBraided) :
    homMk (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z))
      (FreeMonoidal.Hom.α_hom (S := S.braidedSignature) X.word Y.word Z.word) =
        (α_ X Y Z).hom := rfl

@[simp]
theorem homMk_α_inv (X Y Z : S.FreeBraided) :
    homMk (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z)
      (FreeMonoidal.Hom.α_inv (S := S.braidedSignature) X.word Y.word Z.word) =
        (α_ X Y Z).inv := rfl

@[simp]
theorem homMk_l_hom (X : S.FreeBraided) :
    homMk (X := 𝟙_ _ ⊗ X) (FreeMonoidal.Hom.l_hom (S := S.braidedSignature) X.word) =
      (λ_ X).hom := rfl

@[simp]
theorem homMk_l_inv (X : S.FreeBraided) :
    homMk (Y := 𝟙_ _ ⊗ X) (FreeMonoidal.Hom.l_inv (S := S.braidedSignature) X.word) =
      (λ_ X).inv := rfl

@[simp]
theorem homMk_ρ_hom (X : S.FreeBraided) :
    homMk (X := X ⊗ 𝟙_ _) (FreeMonoidal.Hom.ρ_hom (S := S.braidedSignature) X.word) =
      (ρ_ X).hom := rfl

@[simp]
theorem homMk_ρ_inv (X : S.FreeBraided) :
    homMk (Y := X ⊗ 𝟙_ _) (FreeMonoidal.Hom.ρ_inv (S := S.braidedSignature) X.word) =
      (ρ_ X).inv := rfl

@[simp]
theorem homMk_braidingHom (X Y : S.FreeBraided) :
    homMk (X := X ⊗ Y) (Y := Y ⊗ X) (RawHom.braidingHom X.word Y.word) = (β_ X Y).hom := rfl

@[simp]
theorem homMk_braidingInv (X Y : S.FreeBraided) :
    homMk (X := Y ⊗ X) (Y := X ⊗ Y) (RawHom.braidingInv X.word Y.word) = (β_ X Y).inv := rfl

@[simp]
theorem homMk_ofCoupon (g : S.Coupon) :
    homMk (X := ofWord (S.src g)) (Y := ofWord (S.tgt g)) (RawHom.ofCoupon g) = coupon g := rfl

/-- Induction principle for morphisms of `S.FreeBraided`: a property holding for identities,
associators, unitors, braidings, inverse braidings, and coupons, and closed under composition and
whiskering on both sides, holds for every morphism. -/
theorem hom_inductionOn {motive : {X Y : S.FreeBraided} → (X ⟶ Y) → Prop} {X Y : S.FreeBraided}
    (t : X ⟶ Y)
    (id : (X : S.FreeBraided) → motive (𝟙 X))
    (α_hom : (X Y Z : S.FreeBraided) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : S.FreeBraided) → motive (α_ X Y Z).inv)
    (l_hom : (X : S.FreeBraided) → motive (λ_ X).hom)
    (l_inv : (X : S.FreeBraided) → motive (λ_ X).inv)
    (ρ_hom : (X : S.FreeBraided) → motive (ρ_ X).hom)
    (ρ_inv : (X : S.FreeBraided) → motive (ρ_ X).inv)
    (β_hom : (X Y : S.FreeBraided) → motive (β_ X Y).hom)
    (β_inv : (X Y : S.FreeBraided) → motive (β_ X Y).inv)
    (coupon : (g : S.Coupon) → motive (FreeBraided.coupon g))
    (comp : {X Y Z : S.FreeBraided} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g →
      motive (f ≫ g))
    (whiskerLeft : (X : S.FreeBraided) → {Y Z : S.FreeBraided} → (f : Y ⟶ Z) → motive f →
      motive (X ◁ f))
    (whiskerRight : {X Y : S.FreeBraided} → (f : X ⟶ Y) → (Z : S.FreeBraided) → motive f →
      motive (f ▷ Z)) :
    motive t := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective t
  induction f using FreeMonoidal.Hom.inductionOn with
  | id X => exact id ((Presented.quotientFunctor (BraidedRel S)).obj X)
  | α_hom X Y Z =>
      exact α_hom ((Presented.quotientFunctor (BraidedRel S)).obj X)
        ((Presented.quotientFunctor (BraidedRel S)).obj Y)
        ((Presented.quotientFunctor (BraidedRel S)).obj Z)
  | α_inv X Y Z =>
      exact α_inv ((Presented.quotientFunctor (BraidedRel S)).obj X)
        ((Presented.quotientFunctor (BraidedRel S)).obj Y)
        ((Presented.quotientFunctor (BraidedRel S)).obj Z)
  | l_hom X => exact l_hom ((Presented.quotientFunctor (BraidedRel S)).obj X)
  | l_inv X => exact l_inv ((Presented.quotientFunctor (BraidedRel S)).obj X)
  | ρ_hom X => exact ρ_hom ((Presented.quotientFunctor (BraidedRel S)).obj X)
  | ρ_inv X => exact ρ_inv ((Presented.quotientFunctor (BraidedRel S)).obj X)
  | coupon g =>
      cases g with
      | coupon g => exact coupon g
      | β_hom X Y => exact β_hom (ofWord X) (ofWord Y)
      | β_inv X Y => exact β_inv (ofWord X) (ofWord Y)
  | comp f g hf hg => exact comp _ _ hf hg
  | whiskerLeft X f hf => exact whiskerLeft ((Presented.quotientFunctor (BraidedRel S)).obj X) _ hf
  | whiskerRight f X hf =>
      exact whiskerRight _ ((Presented.quotientFunctor (BraidedRel S)).obj X) hf

/-! ### Universal property: braided lifts -/

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))

/-- The strong braided functor out of `S.FreeBraided` determined by images `fo` of the generating
objects and `fc` of the coupons in an arbitrary (not necessarily strict) braided monoidal category
`D`. Its tensorator and unit comparison are identities. -/
-- Exposed so that object expressions `(lift fo fc).obj X` reduce to tensor products in `D`,
-- matching `FreeMonoidal.lift` and `Presented.lift`.
@[expose] def lift : S.FreeBraided ⥤ D :=
  Presented.lift (S := S.braidedSignature) fo
    (fun
      | .coupon g => fc g
      | .β_hom X Y => (β_ (projectObj fo X) (projectObj fo Y)).hom
      | .β_inv X Y => (β_ (projectObj fo X) (projectObj fo Y)).inv)
    (fun _ _ _ _ h ↦ by
      cases h with
      | β_hom_inv X Y =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, Functor.map_id]
          exact (β_ (projectObj fo X) (projectObj fo Y)).hom_inv_id
      | β_inv_hom X Y =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, Functor.map_id]
          exact (β_ (projectObj fo X) (projectObj fo Y)).inv_hom_id
      | braiding_naturality_right X f =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
            FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon]
          exact BraidedCategory.braiding_naturality_right (projectObj fo X) _
      | braiding_naturality_left f Y =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
            FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_coupon]
          exact BraidedCategory.braiding_naturality_left _ (projectObj fo Y)
      | hexagon_forward X Y Z =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_associator_hom,
            FreeMonoidal.lift_map_coupon, FreeMonoidal.lift_map_whiskerRight,
            FreeMonoidal.lift_map_whiskerLeft]
          exact BraidedCategory.hexagon_forward (projectObj fo X) (projectObj fo Y)
            (projectObj fo Z)
      | hexagon_reverse X Y Z =>
          simp only [Functor.map_comp, FreeMonoidal.lift_map_associator_inv,
            FreeMonoidal.lift_map_coupon, FreeMonoidal.lift_map_whiskerRight,
            FreeMonoidal.lift_map_whiskerLeft]
          exact BraidedCategory.hexagon_reverse (projectObj fo X) (projectObj fo Y)
            (projectObj fo Z))

instance : (lift fo fc).Monoidal := by
  dsimp only [lift]
  infer_instance

@[simp]
theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := rfl

@[simp]
theorem lift_obj_ofWord (X : FreeMonoidalCategory S.Obj) :
    (lift fo fc).obj (ofWord X) = projectObj fo X := rfl

@[simp]
theorem lift_obj_tensor (X Y : S.FreeBraided) :
    (lift fo fc).obj (X ⊗ Y) = (lift fo fc).obj X ⊗ (lift fo fc).obj Y := rfl

@[simp]
theorem lift_obj_tensorUnit : (lift fo fc).obj (𝟙_ S.FreeBraided) = 𝟙_ D := rfl

@[simp]
theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g :=
  FreeMonoidal.lift_map_coupon (S := S.braidedSignature) fo _ (BraidedCoupon.coupon g)

@[simp]
theorem lift_map_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Y₁ ⟶ Y₂) :
    (lift fo fc).map (X ◁ f) = (lift fo fc).obj X ◁ (lift fo fc).map f := by
  obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
  exact FreeMonoidal.lift_map_whiskerLeft (S := S.braidedSignature) fo _ X.as f

@[simp]
theorem lift_map_whiskerRight {X₁ X₂ : S.FreeBraided} (f : X₁ ⟶ X₂) (Y : S.FreeBraided) :
    (lift fo fc).map (f ▷ Y) = (lift fo fc).map f ▷ (lift fo fc).obj Y := by
  obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
  exact FreeMonoidal.lift_map_whiskerRight (S := S.braidedSignature) fo _ f Y.as

@[simp]
theorem lift_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (lift fo fc).map (f ⊗ₘ g) = (lift fo fc).map f ⊗ₘ (lift fo fc).map g := by
  obtain ⟨f, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
  obtain ⟨g, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective g
  rw [CategoryTheory.Quotient.map_tensorHom_map]
  exact FreeMonoidal.lift_map_tensorHom (S := S.braidedSignature) fo _ f g

@[simp]
theorem lift_map_associator_hom (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).hom =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom :=
  FreeMonoidal.lift_map_associator_hom (S := S.braidedSignature) fo _ X.as Y.as Z.as

@[simp]
theorem lift_map_associator_inv (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).inv =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).inv :=
  FreeMonoidal.lift_map_associator_inv (S := S.braidedSignature) fo _ X.as Y.as Z.as

/- The unitor and braiding equations are not `@[simp]`: Mathlib's `left_unitality`,
`right_unitality`, and `Functor.map_braiding` rewrite them in the opposite direction or already
simplify their left-hand sides. -/

theorem lift_map_leftUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).hom = (λ_ ((lift fo fc).obj X)).hom :=
  FreeMonoidal.lift_map_leftUnitor_hom (S := S.braidedSignature) fo _ X.as

theorem lift_map_leftUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).inv = (λ_ ((lift fo fc).obj X)).inv :=
  FreeMonoidal.lift_map_leftUnitor_inv (S := S.braidedSignature) fo _ X.as

theorem lift_map_rightUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).hom = (ρ_ ((lift fo fc).obj X)).hom :=
  FreeMonoidal.lift_map_rightUnitor_hom (S := S.braidedSignature) fo _ X.as

theorem lift_map_rightUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).inv = (ρ_ ((lift fo fc).obj X)).inv :=
  FreeMonoidal.lift_map_rightUnitor_inv (S := S.braidedSignature) fo _ X.as

theorem lift_map_braiding_hom (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).hom = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).hom :=
  FreeMonoidal.lift_map_coupon (S := S.braidedSignature) fo _ (BraidedCoupon.β_hom X.word Y.word)

theorem lift_map_braiding_inv (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).inv = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).inv :=
  FreeMonoidal.lift_map_coupon (S := S.braidedSignature) fo _ (BraidedCoupon.β_inv X.word Y.word)

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := by
  dsimp only [lift]
  exact Presented.lift_ε (S := S.braidedSignature) fo _ _

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := by
  dsimp only [lift]
  exact Presented.lift_η (S := S.braidedSignature) fo _ _

@[simp]
theorem lift_μ (X Y : S.FreeBraided) : Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := by
  dsimp only [lift]
  exact Presented.lift_μ (S := S.braidedSignature) fo _ _ X Y

@[simp]
theorem lift_δ (X Y : S.FreeBraided) : Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := by
  dsimp only [lift]
  exact Presented.lift_δ (S := S.braidedSignature) fo _ _ X Y

instance : (lift fo fc).Braided where
  braided X Y := by
    rw [lift_μ, lift_μ, lift_map_braiding_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end Lift

/-! ### Uniqueness up to unique monoidal natural isomorphism -/

section Uniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.FreeBraided` to a
lax monoidal functor is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.FreeBraided ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : ∀ a, α.app (of a) = β.app (of a)) : α = β :=
  Presented.natTrans_ext h

section WordIso

variable (F G : S.FreeBraided ⥤ D) [F.Monoidal] [G.Monoidal]
  (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a tensor word under two strong monoidal functors out of
`S.FreeBraided`, induced by isomorphisms `e` at the generating objects together with the
tensorators and unit comparisons of the two functors. -/
def wordIso : ∀ X : FreeMonoidalCategory S.Obj, F.obj (ofWord X) ≅ G.obj (ofWord X)
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
      (Functor.Monoidal.μIso F (ofWord X) (ofWord Y)).symm ≪≫
        (wordIso X ⊗ᵢ wordIso Y) ≪≫
        Functor.Monoidal.μIso G (ofWord X) (ofWord Y)

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (.of a) = e a := by rfl

@[simp]
theorem wordIso_tensorUnit_hom :
    (wordIso F G e (𝟙_ (FreeMonoidalCategory S.Obj))).hom = η F ≫ ε G := by rfl

@[simp]
theorem wordIso_tensor_hom (X Y : FreeMonoidalCategory S.Obj) :
    (wordIso F G e (X ⊗ Y)).hom =
      δ F (ofWord X) (ofWord Y) ≫
        ((wordIso F G e X).hom ⊗ₘ (wordIso F G e Y).hom) ≫
        μ G (ofWord X) (ofWord Y) := by rfl

private theorem wordIso_hom_eq_freeMonoidal (X : FreeMonoidalCategory S.Obj) :
    (wordIso F G e X).hom =
      (FreeMonoidal.wordIso (Presented.quotientFunctor (BraidedRel S) ⋙ F)
        (Presented.quotientFunctor (BraidedRel S) ⋙ G) e X).hom := by
  induction X with
  | of a =>
      exact (congrArg Iso.hom (FreeMonoidal.wordIso_of (S := S.braidedSignature)
        (Presented.quotientFunctor (BraidedRel S) ⋙ F)
        (Presented.quotientFunctor (BraidedRel S) ⋙ G) e a)).symm
  | unit =>
      rw [FreeMonoidalCategory.unit_eq_unit, wordIso_tensorUnit_hom]
      have h := FreeMonoidal.wordIso_tensorUnit_hom (S := S.braidedSignature)
        (Presented.quotientFunctor (BraidedRel S) ⋙ F)
        (Presented.quotientFunctor (BraidedRel S) ⋙ G) e
      simp only [Functor.OplaxMonoidal.comp_η, Functor.LaxMonoidal.comp_ε,
        CategoryTheory.Quotient.functor_η, CategoryTheory.Quotient.functor_ε, Functor.map_id,
        Category.comp_id] at h
      exact (congrArg (· ≫ ε G) (Category.id_comp (η F))).symm.trans h.symm
  | tensor X Y hX hY =>
      rw [FreeMonoidalCategory.tensor_eq_tensor, wordIso_tensor_hom, hX, hY]
      have h := FreeMonoidal.wordIso_tensor_hom (S := S.braidedSignature)
        (Presented.quotientFunctor (BraidedRel S) ⋙ F)
        (Presented.quotientFunctor (BraidedRel S) ⋙ G) e ⟨X⟩ ⟨Y⟩
      simp only [Functor.OplaxMonoidal.comp_δ, Functor.LaxMonoidal.comp_μ,
        CategoryTheory.Quotient.functor_δ, CategoryTheory.Quotient.functor_μ, Functor.map_id,
        Category.comp_id] at h
      exact (congrArg (· ≫ _) (Category.id_comp (δ F (ofWord X) (ofWord Y)))).symm.trans h.symm

end WordIso

section BraidedUniqueness

variable [BraidedCategory D] {F G : S.FreeBraided ⥤ D} [F.Braided] [G.Braided]
  {e : ∀ a, F.obj (of a) ≅ G.obj (of a)}

private theorem braiding_naturality_wordIso (X Y : FreeMonoidalCategory S.Obj) :
    F.map (β_ (ofWord X) (ofWord Y)).hom ≫ (wordIso F G e (Y.tensor X)).hom =
      (wordIso F G e (X.tensor Y)).hom ≫ G.map (β_ (ofWord X) (ofWord Y)).hom := by
  have h :
      F.map (β_ (ofWord X) (ofWord Y)).hom ≫
          (δ F (ofWord Y) (ofWord X) ≫
            ((wordIso F G e Y).hom ⊗ₘ (wordIso F G e X).hom) ≫
            μ G (ofWord Y) (ofWord X)) =
        (δ F (ofWord X) (ofWord Y) ≫
            ((wordIso F G e X).hom ⊗ₘ (wordIso F G e Y).hom) ≫
            μ G (ofWord X) (ofWord Y)) ≫
          G.map (β_ (ofWord X) (ofWord Y)).hom := by
    simp only [Category.assoc]
    rw [← Functor.δ_braiding_assoc, ← braiding_naturality_assoc, ← Functor.LaxBraided.braided]
  exact h

private theorem braiding_inv_naturality_wordIso (X Y : FreeMonoidalCategory S.Obj) :
    F.map (β_ (ofWord X) (ofWord Y)).inv ≫ (wordIso F G e (X.tensor Y)).hom =
      (wordIso F G e (Y.tensor X)).hom ≫ G.map (β_ (ofWord X) (ofWord Y)).inv := by
  let α : F.obj (ofWord X ⊗ ofWord Y) ⟶ G.obj (ofWord X ⊗ ofWord Y) :=
    (wordIso F G e (X.tensor Y)).hom
  let β : F.obj (ofWord Y ⊗ ofWord X) ⟶ G.obj (ofWord Y ⊗ ofWord X) :=
    (wordIso F G e (Y.tensor X)).hom
  have hb : F.map (β_ (ofWord X) (ofWord Y)).hom ≫ β =
      α ≫ G.map (β_ (ofWord X) (ofWord Y)).hom := braiding_naturality_wordIso X Y
  have h : F.map (β_ (ofWord X) (ofWord Y)).inv ≫ α =
      β ≫ G.map (β_ (ofWord X) (ofWord Y)).inv := by
    rw [← cancel_epi (F.map (β_ (ofWord X) (ofWord Y)).hom),
      ← cancel_mono (G.map (β_ (ofWord X) (ofWord Y)).hom)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
      Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
    exact hb.symm
  exact h

private theorem braidedCoupon_naturality
    (he : ∀ g : S.Coupon, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    (g : BraidedCoupon S) :
    F.map ((Presented.quotientFunctor (BraidedRel S)).map
        (FreeMonoidal.coupon (S := S.braidedSignature) g)) ≫
        (FreeMonoidal.wordIso (Presented.quotientFunctor (BraidedRel S) ⋙ F)
          (Presented.quotientFunctor (BraidedRel S) ⋙ G) e (S.braidedSignature.tgt g)).hom =
      (FreeMonoidal.wordIso (Presented.quotientFunctor (BraidedRel S) ⋙ F)
        (Presented.quotientFunctor (BraidedRel S) ⋙ G) e (S.braidedSignature.src g)).hom ≫
        G.map ((Presented.quotientFunctor (BraidedRel S)).map
          (FreeMonoidal.coupon (S := S.braidedSignature) g)) := by
  simp only [← wordIso_hom_eq_freeMonoidal]
  cases g with
  | coupon g => exact he g
  | β_hom X Y => exact braiding_naturality_wordIso X Y
  | β_inv X Y => exact braiding_inv_naturality_wordIso X Y

variable (F G e)

/-- Two strong braided functors out of `S.FreeBraided` that agree up to isomorphisms `e` on the
generating objects, compatibly with every coupon, are isomorphic by a monoidal natural isomorphism
extending `e`. -/
def monoidalNatIso
    (he : ∀ g : S.Coupon, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  Presented.monoidalNatIso F G e (braidedCoupon_naturality he)

variable {F G e}
  (he : ∀ g : S.Coupon, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
    (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeBraided) :
    (monoidalNatIso F G e he).hom.app X = (wordIso F G e X.word).hom :=
  (Presented.monoidalNatIso_hom_app (braidedCoupon_naturality he) X.as).trans
    (wordIso_hom_eq_freeMonoidal F G e X.word).symm

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app (of a) = (e a).hom :=
  (monoidalNatIso_hom_app he (of a)).trans (congrArg Iso.hom (wordIso_of F G e a))

include he in
/-- The word isomorphisms `wordIso F G e` are natural with respect to every morphism of
`S.FreeBraided` as soon as they are natural with respect to every coupon of `S`. -/
theorem map_comp_wordIso_hom {X Y : S.FreeBraided} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.word).hom = (wordIso F G e X.word).hom ≫ G.map f := by
  have h := (monoidalNatIso F G e he).hom.naturality f
  rw [monoidalNatIso_hom_app, monoidalNatIso_hom_app] at h
  exact h

instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom where
  unit := by
    have h : (monoidalNatIso F G e he).hom.app (𝟙_ S.FreeBraided) = η F ≫ ε G :=
      (monoidalNatIso_hom_app he (𝟙_ S.FreeBraided)).trans (wordIso_tensorUnit_hom F G e)
    rw [h, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    have hXY : (monoidalNatIso F G e he).hom.app (X ⊗ Y) =
        δ F X Y ≫
          ((monoidalNatIso F G e he).hom.app X ⊗ₘ (monoidalNatIso F G e he).hom.app Y) ≫
          μ G X Y := by
      have h1 := monoidalNatIso_hom_app he (X ⊗ Y)
      have h2 : (wordIso F G e (X ⊗ Y).word).hom =
          δ F X Y ≫ ((wordIso F G e X.word).hom ⊗ₘ (wordIso F G e Y.word).hom) ≫ μ G X Y :=
        wordIso_tensor_hom F G e X.word Y.word
      have hX : (monoidalNatIso F G e he).hom.app X = (wordIso F G e X.word).hom :=
        monoidalNatIso_hom_app he X
      have hY : (monoidalNatIso F G e he).hom.app Y = (wordIso F G e Y.word).hom :=
        monoidalNatIso_hom_app he Y
      exact h1.trans (h2.trans (congrArg (δ F X Y ≫ · ≫ μ G X Y)
        (congrArg₂ (· ⊗ₘ ·) hX.symm hY.symm)))
    rw [hXY, Functor.Monoidal.μ_δ_assoc]

end BraidedUniqueness

end Uniqueness

/-! ### Crossing-weight invariant and non-symmetry -/

section CrossingWeight

/-- The number of generating object letters in a formal tensor word. -/
private def rawWordLength {α : Type u} : FreeMonoidalCategory α → ℕ
  | .of _ => 1
  | .unit => 0
  | .tensor X Y => rawWordLength X + rawWordLength Y

/-- The number of generating object letters (strands) in an object of `S.FreeBraided`. -/
def wordLength (X : S.FreeBraided) : ℕ :=
  rawWordLength X.word

@[simp]
theorem wordLength_of (a : S.Obj) : (of a).wordLength = 1 := by rfl

@[simp]
theorem wordLength_tensorUnit : (𝟙_ S.FreeBraided).wordLength = 0 := by rfl

@[simp]
theorem wordLength_tensor (X Y : S.FreeBraided) :
    (X ⊗ Y).wordLength = X.wordLength + Y.wordLength := by rfl

/-- Auxiliary braided monoidal category on `ℕ` whose morphisms from `m` to `n` are elements of
`WithZero (Multiplicative ℤ)` that vanish whenever `m ≠ n`, with braiding weight
`WithZero.exp (m * n : ℤ)`. Used to define `FreeBraided.crossingWeight`. -/
private structure CrossingWeightObj where
  val : ℕ

@[ext]
private structure CrossingWeightHom (m n : CrossingWeightObj) where
  val : WithZero (Multiplicative ℤ)
  eq_zero : m.val ≠ n.val → val = 0

private noncomputable instance : Category.{0} CrossingWeightObj where
  Hom := CrossingWeightHom
  id _ := ⟨1, fun h ↦ absurd rfl h⟩
  comp {m n p} f g := ⟨f.val * g.val, fun h ↦ by
    by_cases hmn : m.val = n.val
    · rw [g.eq_zero (hmn ▸ h), mul_zero]
    · rw [f.eq_zero hmn, zero_mul]⟩
  id_comp f := CrossingWeightHom.ext (one_mul f.val)
  comp_id f := CrossingWeightHom.ext (mul_one f.val)
  assoc f g h := CrossingWeightHom.ext (mul_assoc f.val g.val h.val)

private noncomputable instance : MonoidalCategory CrossingWeightObj where
  tensorObj m n := ⟨m.val + n.val⟩
  whiskerLeft m _ _ f := ⟨f.val, fun h ↦ f.eq_zero fun h' ↦ h (congrArg (m.val + ·) h')⟩
  whiskerRight f n := ⟨f.val, fun h ↦ f.eq_zero fun h' ↦ h (congrArg (· + n.val) h')⟩
  tensorHom {m₁ n₁ m₂ n₂} f g := ⟨f.val * g.val, fun h ↦ by
    by_cases h₁ : m₁.val = n₁.val
    · rw [g.eq_zero fun h₂ ↦ h (congrArg₂ (· + ·) h₁ h₂), mul_zero]
    · rw [f.eq_zero h₁, zero_mul]⟩
  tensorHom_def _ _ := CrossingWeightHom.ext rfl
  id_tensorHom_id _ _ := CrossingWeightHom.ext (one_mul 1)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    CrossingWeightHom.ext (mul_mul_mul_comm f₁.val f₂.val g₁.val g₂.val)
  whiskerLeft_id _ _ := CrossingWeightHom.ext rfl
  id_whiskerRight _ _ := CrossingWeightHom.ext rfl
  tensorUnit := ⟨0⟩
  associator _ _ _ :=
    ⟨⟨1, fun h ↦ absurd (Nat.add_assoc _ _ _) h⟩,
      ⟨1, fun h ↦ absurd (Nat.add_assoc _ _ _).symm h⟩,
      CrossingWeightHom.ext (mul_one 1), CrossingWeightHom.ext (mul_one 1)⟩
  leftUnitor _ :=
    ⟨⟨1, fun h ↦ absurd (Nat.zero_add _) h⟩,
      ⟨1, fun h ↦ absurd (Nat.zero_add _).symm h⟩,
      CrossingWeightHom.ext (mul_one 1), CrossingWeightHom.ext (mul_one 1)⟩
  rightUnitor _ :=
    ⟨⟨1, fun h ↦ absurd (Nat.add_zero _) h⟩,
      ⟨1, fun h ↦ absurd (Nat.add_zero _).symm h⟩,
      CrossingWeightHom.ext (mul_one 1), CrossingWeightHom.ext (mul_one 1)⟩
  associator_naturality f₁ f₂ f₃ := CrossingWeightHom.ext (by
    simp only [CategoryStruct.comp, mul_one, one_mul, mul_assoc])
  leftUnitor_naturality f := CrossingWeightHom.ext (mul_one f.val |>.trans (one_mul f.val).symm)
  rightUnitor_naturality f := CrossingWeightHom.ext (mul_one f.val |>.trans (one_mul f.val).symm)
  pentagon _ _ _ _ := CrossingWeightHom.ext (by
    simp only [CategoryStruct.comp, mul_one])
  triangle _ _ := CrossingWeightHom.ext (mul_one (1 : WithZero (Multiplicative ℤ)))

private noncomputable instance : BraidedCategory CrossingWeightObj where
  braiding m n :=
    ⟨⟨WithZero.exp ((m.val : ℤ) * (n.val : ℤ)), fun h ↦ absurd (Nat.add_comm _ _) h⟩,
      ⟨WithZero.exp (-((m.val : ℤ) * (n.val : ℤ))), fun h ↦ absurd (Nat.add_comm _ _) h⟩,
      CrossingWeightHom.ext (by
        simp only [CategoryStruct.comp, CategoryStruct.id, ← WithZero.exp_add, add_neg_cancel,
          WithZero.exp_zero]),
      CrossingWeightHom.ext (by
        simp only [CategoryStruct.comp, CategoryStruct.id, ← WithZero.exp_add, neg_add_cancel,
          WithZero.exp_zero])⟩
  braiding_naturality_right m {n₁ n₂} f := CrossingWeightHom.ext (by
    by_cases h : n₁.val = n₂.val
    · simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight, h]
      exact mul_comm _ _
    · simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight, f.eq_zero h, zero_mul, mul_zero])
  braiding_naturality_left {m₁ m₂} f n := CrossingWeightHom.ext (by
    by_cases h : m₁.val = m₂.val
    · simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight, h]
      exact mul_comm _ _
    · simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight, f.eq_zero h, zero_mul, mul_zero])
  hexagon_forward m n p := CrossingWeightHom.ext (by
    simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
      MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.associator,
      MonoidalCategoryStruct.tensorObj, one_mul, mul_one, ← WithZero.exp_add]
    congr 1
    push_cast
    exact mul_add (m.val : ℤ) n.val p.val)
  hexagon_reverse m n p := CrossingWeightHom.ext (by
    simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
      MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.associator,
      MonoidalCategoryStruct.tensorObj, one_mul, mul_one, ← WithZero.exp_add]
    congr 1
    push_cast
    rw [add_mul, add_comm])

private noncomputable def crossingWeightFunctor (S : TensorSignature.{u, v}) :
    S.FreeBraided ⥤ CrossingWeightObj :=
  FreeBraided.lift (fun _ ↦ ⟨1⟩) (fun _ ↦ ⟨0, fun _ ↦ rfl⟩)

private theorem crossingWeightFunctor_obj (X : S.FreeBraided) :
    ((crossingWeightFunctor S).obj X).val = X.wordLength := by
  obtain ⟨⟨W⟩⟩ := X
  induction W with
  | of a => rfl
  | unit => rfl
  | tensor W₁ W₂ h₁ h₂ => exact congrArg₂ (· + ·) h₁ h₂

/-- The multiplicative crossing-weight invariant of a morphism in `S.FreeBraided`, valued in
`WithZero (Multiplicative ℤ)`. Identities, associators, and unitors have weight `1`; a braiding
`β_ X Y` has weight `WithZero.exp ((X.wordLength : ℤ) * (Y.wordLength : ℤ))`, its inverse has the
negated exponent, coupons have weight `0`, and composition and tensor product multiply weights. -/
noncomputable def crossingWeight {X Y : S.FreeBraided} (f : X ⟶ Y) :
    WithZero (Multiplicative ℤ) :=
  ((crossingWeightFunctor S).map f).val

@[simp]
theorem crossingWeight_id (X : S.FreeBraided) : crossingWeight (𝟙 X) = 1 := by
  rw [crossingWeight, Functor.map_id]
  rfl

@[simp]
theorem crossingWeight_comp {X Y Z : S.FreeBraided} (f : X ⟶ Y) (g : Y ⟶ Z) :
    crossingWeight (f ≫ g) = crossingWeight f * crossingWeight g := by
  rw [crossingWeight, Functor.map_comp]
  rfl

@[simp]
theorem crossingWeight_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    crossingWeight (f ⊗ₘ g) = crossingWeight f * crossingWeight g := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_tensorHom]
  rfl

@[simp]
theorem crossingWeight_whiskerLeft (X : S.FreeBraided) {Y Z : S.FreeBraided} (f : Y ⟶ Z) :
    crossingWeight (X ◁ f) = crossingWeight f := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_whiskerLeft]
  rfl

@[simp]
theorem crossingWeight_whiskerRight {X Y : S.FreeBraided} (f : X ⟶ Y) (Z : S.FreeBraided) :
    crossingWeight (f ▷ Z) = crossingWeight f := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_whiskerRight]
  rfl

@[simp]
theorem crossingWeight_associator_hom (X Y Z : S.FreeBraided) :
    crossingWeight (α_ X Y Z).hom = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_associator_hom]
  rfl

@[simp]
theorem crossingWeight_associator_inv (X Y Z : S.FreeBraided) :
    crossingWeight (α_ X Y Z).inv = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_associator_inv]
  rfl

@[simp]
theorem crossingWeight_leftUnitor_hom (X : S.FreeBraided) :
    crossingWeight (λ_ X).hom = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_leftUnitor_hom]
  rfl

@[simp]
theorem crossingWeight_leftUnitor_inv (X : S.FreeBraided) :
    crossingWeight (λ_ X).inv = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_leftUnitor_inv]
  rfl

@[simp]
theorem crossingWeight_rightUnitor_hom (X : S.FreeBraided) :
    crossingWeight (ρ_ X).hom = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_rightUnitor_hom]
  rfl

@[simp]
theorem crossingWeight_rightUnitor_inv (X : S.FreeBraided) :
    crossingWeight (ρ_ X).inv = 1 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_rightUnitor_inv]
  rfl

@[simp]
theorem crossingWeight_coupon (g : S.Coupon) : crossingWeight (coupon g) = 0 := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_coupon]

@[simp]
theorem crossingWeight_braiding_hom (X Y : S.FreeBraided) :
    crossingWeight (β_ X Y).hom = WithZero.exp ((X.wordLength : ℤ) * (Y.wordLength : ℤ)) := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_braiding_hom]
  exact congrArg WithZero.exp (congrArg₂ (· * ·)
    (congrArg (Nat.cast (R := ℤ)) (crossingWeightFunctor_obj X))
    (congrArg (Nat.cast (R := ℤ)) (crossingWeightFunctor_obj Y)))

@[simp]
theorem crossingWeight_braiding_inv (X Y : S.FreeBraided) :
    crossingWeight (β_ X Y).inv = WithZero.exp (-((X.wordLength : ℤ) * (Y.wordLength : ℤ))) := by
  rw [crossingWeight, crossingWeightFunctor, lift_map_braiding_inv]
  exact congrArg (fun z ↦ WithZero.exp (-z)) (congrArg₂ (· * ·)
    (congrArg (Nat.cast (R := ℤ)) (crossingWeightFunctor_obj X))
    (congrArg (Nat.cast (R := ℤ)) (crossingWeightFunctor_obj Y)))

/-- The double braiding of two generating objects has crossing weight `WithZero.exp (2 : ℤ)`. -/
theorem crossingWeight_doubleBraiding (a b : S.Obj) :
    crossingWeight ((β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom) = WithZero.exp (2 : ℤ) := by
  rw [crossingWeight_comp, crossingWeight_braiding_hom, crossingWeight_braiding_hom,
    wordLength_of, wordLength_of, Nat.cast_one, mul_one, ← WithZero.exp_add]
  rfl

private noncomputable def crossingWeightAutHom (X : S.FreeBraided) :
    Aut X →* (WithZero (Multiplicative ℤ))ˣ where
  toFun e :=
    { val := crossingWeight e.asIso.hom
      inv := crossingWeight e.asIso.inv
      val_inv := by rw [← crossingWeight_comp, e.asIso.hom_inv_id, crossingWeight_id]
      inv_val := by rw [← crossingWeight_comp, e.asIso.inv_hom_id, crossingWeight_id] }
  map_one' := Units.ext (crossingWeight_id X)
  map_mul' e₁ e₂ := Units.ext (by
    simp only [Aut.mul_asIso, Iso.trans_hom, crossingWeight_comp, Units.val_mul]
    exact mul_comm _ _)

/-- The crossing weight of an integer power of an automorphism is the corresponding power of its
crossing weight. -/
theorem crossingWeight_aut_zpow {X : S.FreeBraided} (e : Aut X) (k : ℤ) :
    crossingWeight (e ^ k).asIso.hom = (crossingWeight e.asIso.hom) ^ k := by
  have h := congrArg Units.val (map_zpow (crossingWeightAutHom X) e k)
  simpa [crossingWeightAutHom] using h

/-- The integer powers of the double braiding on any two generating objects are pairwise
distinct. -/
theorem doubleBraiding_zpow_injective (a b : S.Obj) :
    Function.Injective fun k : ℤ ↦
      (Aut.of (β_ (of a) (of b) ≪≫ β_ (of b) (of a))) ^ k := by
  intro k₁ k₂ h
  have hw := congrArg (fun e : Aut (of a ⊗ of b) ↦ crossingWeight e.asIso.hom) h
  simp only [crossingWeight_aut_zpow, Iso.trans_hom, crossingWeight_doubleBraiding,
    ← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul] at hw
  omega

/-- The double braiding of two generating objects in `S.FreeBraided` is never the identity. -/
theorem doubleBraiding_ne_id (a b : S.Obj) :
    (β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b) := by
  intro h
  have hw := congrArg crossingWeight h
  rw [crossingWeight_doubleBraiding, crossingWeight_id] at hw
  exact absurd (WithZero.exp_eq_one.mp hw) (by decide)

/-- Whenever `S` has at least one generating object, no `SymmetricCategory` structure on
`S.FreeBraided` extends its canonical `BraidedCategory` instance. -/
theorem not_symmetricCategory [Nonempty S.Obj] (h : SymmetricCategory S.FreeBraided) :
    h.toBraidedCategory ≠ (inferInstance : BraidedCategory S.FreeBraided) := by
  intro heq
  obtain ⟨a⟩ := ‹Nonempty S.Obj›
  have hsym := h.symmetry (of a) (of a)
  rw [heq] at hsym
  exact doubleBraiding_ne_id a a hsym

end CrossingWeight

end FreeBraided

end TauCeti.TensorSignature
