/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic

/-!
# Substitution of braided tensor expressions for coupons

A `TensorSignature.BraidedSubstitution S T` replaces object generators of `S` by formal tensor
words in `T.FreeBraided` and coupons of `S` by raw braided morphism expressions in `T` with the
substituted source and target boundaries. Object generators may be sent to the unit or to composite
tensor words, and nullary coupons retain their unit boundaries.

`FreeBraided.Hom.subst` performs this replacement on raw expressions before quotienting by the
braided monoidal axioms; `FreeBraided.HomEquiv.subst` shows that it preserves the braided
congruence. On equivalence classes, `BraidedSubstitution.toFunctor` is the strong braided functor
given by `FreeBraided.lift`, and `BraidedSubstitution.toFunctor_map_homMk` identifies its action on
representatives with raw substitution.

Braided substitutions form a compositional calculus via `BraidedSubstitution.id` and
`BraidedSubstitution.comp`, satisfying the two-sided unit laws (`id_comp`, `comp_id`),
associativity (`comp_assoc`), raw substitution laws (`id_subst_heq`, `comp_subst_heq`), and
functoriality of `toFunctor` (`id_toFunctor`, `comp_toFunctor`).

## Main definitions and results

* `TauCeti.TensorSignature.BraidedSubstitution S T`: typed raw braided substitutions between tensor
  signatures across independent universes.
* `FreeBraided.Hom.subst` and `FreeBraided.HomEquiv.subst`: raw braided substitution and its
  soundness with respect to the braided monoidal axioms.
* `BraidedSubstitution.toFunctor` and `BraidedSubstitution.toFunctor_map_homMk`: the induced strong
  braided functor `S.FreeBraided ⥤ T.FreeBraided` and its agreement with `FreeBraided.Hom.subst` on
  representatives.
* `BraidedSubstitution.id` and `BraidedSubstitution.comp`: identity and diagrammatic composition of
  braided substitutions, with unit and associativity laws (`id_comp`, `comp_id`, `comp_assoc`), raw
  substitution laws (`id_subst_heq`, `comp_subst_heq`), and functoriality (`id_toFunctor`,
  `comp_toFunctor`).

The design parallels the unbraided `TauCeti.TensorSignature.Substitution` in
`TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §3.3.
-/

public section

universe u v u' v' u'' v'' u''' v'''

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures. Generating objects are replaced by
objects of `T.FreeBraided`, and coupons by raw braided morphism expressions with the substituted
source and target words. The object and coupon universes of `S` and `T` are independent. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The tensor word in `T.FreeBraided` replacing each generating object of `S`. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided morphism expression replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon,
    FreeBraided.Hom (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}} {V : TensorSignature.{u''', v'''}}

namespace FreeBraided

/-- Substitute formal tensor words for generating objects and raw braided expressions for coupons.
Endpoints are interpreted by `FreeMonoidalCategory.projectObj`. -/
def Hom.subst (σ : BraidedSubstitution S T) :
    ∀ {X Y : FreeMonoidalCategory S.Obj},
      Hom X Y → Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => MonoidalCore.Hom.id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z =>
    MonoidalCore.Hom.α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z =>
    MonoidalCore.Hom.α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .l_hom X => MonoidalCore.Hom.l_hom (projectObj σ.obj X).as
  | _, _, .l_inv X => MonoidalCore.Hom.l_inv (projectObj σ.obj X).as
  | _, _, .ρ_hom X => MonoidalCore.Hom.ρ_hom (projectObj σ.obj X).as
  | _, _, .ρ_inv X => MonoidalCore.Hom.ρ_inv (projectObj σ.obj X).as
  | _, _, .gen g =>
    match g with
    | .β_hom X Y => .βHom (projectObj σ.obj X).as (projectObj σ.obj Y).as
    | .β_inv X Y => .βInv (projectObj σ.obj X).as (projectObj σ.obj Y).as
    | .coupon g => σ.coupon g
  | _, _, .comp f g => (Hom.subst σ f).comp (Hom.subst σ g)
  | _, _, .whiskerLeft X f => (Hom.subst σ f).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (Hom.subst σ f).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (Hom.subst σ f).tensor (Hom.subst σ g)

/-- Raw braided substitution sends a formal identity to the formal identity at the substituted
word. -/
@[simp]
theorem Hom.subst_id (σ : BraidedSubstitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.id X) =
      (MonoidalCore.Hom.id (projectObj σ.obj X).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution replaces a coupon `g` by `σ.coupon g`. -/
@[simp]
theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    Hom.subst σ (Hom.coupon g) = σ.coupon g := (rfl)

/-- Raw braided substitution commutes with formal composition. -/
@[simp]
theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    Hom.subst σ (f.comp g) = (Hom.subst σ f).comp (Hom.subst σ g) := (rfl)

/-- Raw braided substitution commutes with formal tensor product of morphisms. -/
@[simp]
theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    Hom.subst σ (f.tensor g) = (Hom.subst σ f).tensor (Hom.subst σ g) := (rfl)

/-- Raw braided substitution commutes with formal left whiskering. -/
@[simp]
theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    Hom.subst σ (f.whiskerLeft X) =
      (Hom.subst σ f).whiskerLeft (projectObj σ.obj X).as := (rfl)

/-- Raw braided substitution commutes with formal right whiskering. -/
@[simp]
theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    Hom.subst σ (f.whiskerRight X) =
      (Hom.subst σ f).whiskerRight (projectObj σ.obj X).as := (rfl)

/-- Raw braided substitution sends `Hom.α_hom` to `Hom.α_hom` at the substituted words. -/
@[simp]
theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    Hom.subst σ (MonoidalCore.Hom.α_hom X Y Z) =
      (MonoidalCore.Hom.α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
        (projectObj σ.obj Z).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.α_inv` to `Hom.α_inv` at the substituted words. -/
@[simp]
theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    Hom.subst σ (MonoidalCore.Hom.α_inv X Y Z) =
      (MonoidalCore.Hom.α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
        (projectObj σ.obj Z).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.l_hom` to `Hom.l_hom` at the substituted word. -/
@[simp]
theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.l_hom X) =
      (MonoidalCore.Hom.l_hom (projectObj σ.obj X).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.l_inv` to `Hom.l_inv` at the substituted word. -/
@[simp]
theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.l_inv X) =
      (MonoidalCore.Hom.l_inv (projectObj σ.obj X).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.ρ_hom` to `Hom.ρ_hom` at the substituted word. -/
@[simp]
theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.ρ_hom X) =
      (MonoidalCore.Hom.ρ_hom (projectObj σ.obj X).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.ρ_inv` to `Hom.ρ_inv` at the substituted word. -/
@[simp]
theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.ρ_inv X) =
      (MonoidalCore.Hom.ρ_inv (projectObj σ.obj X).as : Hom (S := T) _ _) := (rfl)

/-- Raw braided substitution sends `Hom.βHom` to `Hom.βHom` at the substituted words. -/
@[simp]
theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    Hom.subst σ (Hom.βHom X Y) = .βHom (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)

/-- Raw braided substitution sends `Hom.βInv` to `Hom.βInv` at the substituted words. -/
@[simp]
theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    Hom.subst σ (Hom.βInv X Y) = .βInv (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)

/-- Raw braided substitution respects heterogeneous equality of raw morphisms with equal
endpoints. -/
theorem Hom.subst_congr_heq (σ : BraidedSubstitution S T)
    {X₁ X₂ Y₁ Y₂ : FreeMonoidalCategory S.Obj}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂)
    {f₁ : Hom X₁ Y₁} {f₂ : Hom X₂ Y₂} (hf : HEq f₁ f₂) :
    HEq (Hom.subst σ f₁) (Hom.subst σ f₂) := by
  subst hX; subst hY
  cases eq_of_heq hf
  rfl

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

variable (σ : BraidedSubstitution S T)

-- Exposed so that `σ.toFunctor.obj ⟨X⟩` reduces to `projectObj σ.obj X`, matching the dependent
-- endpoint types of `FreeBraided.homMk (f.subst σ)` in `toFunctor_map_homMk`.
/-- The strong braided functor induced by a raw braided substitution: the universal lift of `σ.obj`
and the equivalence classes of `σ.coupon`. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

/-- `σ.toFunctor` is strong monoidal, with identity unit comparison and tensorator. -/
instance : σ.toFunctor.Monoidal :=
  inferInstanceAs (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal

/-- `σ.toFunctor` is a strong braided functor. -/
instance : σ.toFunctor.Braided :=
  inferInstanceAs (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

/-- The unit morphism of `σ.toFunctor` is the identity. -/
@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_ε _ _

/-- The counit morphism of `σ.toFunctor` is the identity. -/
@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_η _ _

/-- The tensorator of `σ.toFunctor` is the identity. -/
@[simp]
theorem toFunctor_μ (X Y : S.FreeBraided) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y

/-- The inverse tensorator of `σ.toFunctor` is the identity. -/
@[simp]
theorem toFunctor_δ (X Y : S.FreeBraided) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y

/-- On objects, `σ.toFunctor` interprets the underlying tensor word via `projectObj σ.obj`. -/
theorem toFunctor_obj (X : S.FreeBraided) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := (rfl)

/-- `σ.toFunctor` sends each generating object `of a` to `σ.obj a`. -/
@[simp]
theorem toFunctor_obj_of (a : S.Obj) :
    σ.toFunctor.obj (of a) = σ.obj a := rfl

/-- `σ.toFunctor` preserves tensor products of objects strictly. -/
@[simp]
theorem toFunctor_obj_tensor (X Y : S.FreeBraided) :
    σ.toFunctor.obj (X ⊗ Y) = σ.toFunctor.obj X ⊗ σ.toFunctor.obj Y := rfl

/-- `σ.toFunctor` preserves the tensor unit strictly. -/
@[simp]
theorem toFunctor_obj_tensorUnit :
    σ.toFunctor.obj (𝟙_ S.FreeBraided) = 𝟙_ T.FreeBraided := rfl

/-- `σ.toFunctor` sends each coupon `g` to the equivalence class of `σ.coupon g`. -/
@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

/-- `σ.toFunctor` preserves left whiskering strictly. -/
@[simp]
theorem toFunctor_map_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Y₁ ⟶ Y₂) :
    σ.toFunctor.map (X ◁ f) = σ.toFunctor.obj X ◁ σ.toFunctor.map f :=
  FreeBraided.lift_map_whiskerLeft _ _ X f

/-- `σ.toFunctor` preserves right whiskering strictly. -/
@[simp]
theorem toFunctor_map_whiskerRight {X₁ X₂ : S.FreeBraided} (f : X₁ ⟶ X₂) (Y : S.FreeBraided) :
    σ.toFunctor.map (f ▷ Y) = σ.toFunctor.map f ▷ σ.toFunctor.obj Y :=
  FreeBraided.lift_map_whiskerRight _ _ f Y

/-- `σ.toFunctor` preserves tensor products of morphisms strictly. -/
@[simp]
theorem toFunctor_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    σ.toFunctor.map (f ⊗ₘ g) = σ.toFunctor.map f ⊗ₘ σ.toFunctor.map g :=
  FreeBraided.lift_map_tensorHom _ _ f g

/-- `σ.toFunctor` sends the forward associator to the forward associator of `T.FreeBraided`. -/
@[simp]
theorem toFunctor_map_associator_hom (X Y Z : S.FreeBraided) :
    σ.toFunctor.map (α_ X Y Z).hom =
      (α_ (σ.toFunctor.obj X) (σ.toFunctor.obj Y) (σ.toFunctor.obj Z)).hom :=
  FreeBraided.lift_map_associator_hom _ _ X Y Z

/-- `σ.toFunctor` sends the inverse associator to the inverse associator of `T.FreeBraided`. -/
@[simp]
theorem toFunctor_map_associator_inv (X Y Z : S.FreeBraided) :
    σ.toFunctor.map (α_ X Y Z).inv =
      (α_ (σ.toFunctor.obj X) (σ.toFunctor.obj Y) (σ.toFunctor.obj Z)).inv :=
  FreeBraided.lift_map_associator_inv _ _ X Y Z

/-- `σ.toFunctor` sends the forward left unitor to the forward left unitor of `T.FreeBraided`. -/
theorem toFunctor_map_leftUnitor_hom (X : S.FreeBraided) :
    σ.toFunctor.map (λ_ X).hom = (λ_ (σ.toFunctor.obj X)).hom :=
  FreeBraided.lift_map_leftUnitor_hom _ _ X

/-- `σ.toFunctor` sends the inverse left unitor to the inverse left unitor of `T.FreeBraided`. -/
theorem toFunctor_map_leftUnitor_inv (X : S.FreeBraided) :
    σ.toFunctor.map (λ_ X).inv = (λ_ (σ.toFunctor.obj X)).inv :=
  FreeBraided.lift_map_leftUnitor_inv _ _ X

/-- `σ.toFunctor` sends the forward right unitor to the forward right unitor of `T.FreeBraided`. -/
theorem toFunctor_map_rightUnitor_hom (X : S.FreeBraided) :
    σ.toFunctor.map (ρ_ X).hom = (ρ_ (σ.toFunctor.obj X)).hom :=
  FreeBraided.lift_map_rightUnitor_hom _ _ X

/-- `σ.toFunctor` sends the inverse right unitor to the inverse right unitor of `T.FreeBraided`. -/
theorem toFunctor_map_rightUnitor_inv (X : S.FreeBraided) :
    σ.toFunctor.map (ρ_ X).inv = (ρ_ (σ.toFunctor.obj X)).inv :=
  FreeBraided.lift_map_rightUnitor_inv _ _ X

/-- `σ.toFunctor` sends the forward braiding to the forward braiding of `T.FreeBraided`. -/
theorem toFunctor_map_braiding_hom (X Y : S.FreeBraided) :
    σ.toFunctor.map (β_ X Y).hom = (β_ (σ.toFunctor.obj X) (σ.toFunctor.obj Y)).hom :=
  FreeBraided.lift_map_braiding_hom _ _ X Y

/-- `σ.toFunctor` sends the inverse braiding to the inverse braiding of `T.FreeBraided`. -/
@[simp]
theorem toFunctor_map_braiding_inv (X Y : S.FreeBraided) :
    σ.toFunctor.map (β_ X Y).inv = (β_ (σ.toFunctor.obj X) (σ.toFunctor.obj Y)).inv :=
  FreeBraided.lift_map_braiding_inv _ _ X Y

/-- Applying `σ.toFunctor` to the equivalence class of a raw braided expression gives the
equivalence class of its raw substitution `f.subst σ`. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (Hom.subst σ f) := by
  induction f with
  | id X => exact (lift σ.obj _).map_id ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | gen g =>
    cases g with
    | β_hom X Y => exact lift_map_braiding_hom _ _ ⟨X⟩ ⟨Y⟩
    | β_inv X Y => exact lift_map_braiding_inv _ _ ⟨X⟩ ⟨Y⟩
    | coupon g =>
      exact (congrArg σ.toFunctor.map (homMk_coupon g)).trans (lift_map_coupon σ.obj _ g)
  | comp f g hf hg =>
    exact ((lift σ.obj _).map_comp (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans
      (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end BraidedSubstitution

namespace FreeBraided

/-- Raw braided substitution preserves the congruence generated by the braided monoidal axioms,
without requiring any equation among the replacing coupons. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (Hom.subst σ f) (Hom.subst σ g) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

private theorem projectObj_of (X : FreeMonoidalCategory S.Obj) :
    projectObj (D := S.FreeBraided) of X = ⟨X⟩ := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
    dsimp only [projectObj]
    rw [hX, hY]
    rfl

private theorem projectObj_comp {D : Type u''} [Category.{v''} D] [MonoidalCategory D]
    (f : S.Obj → T.FreeBraided) (g : T.Obj → D) (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ projectObj g (f a).as) X = projectObj g (projectObj f X).as := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
    dsimp only [projectObj]
    rw [hX, hY]
    rfl

/-- The identity braided substitution on a tensor signature `S`, sending each generating object to
itself and each coupon to itself across the endpoint equality for `projectObj`. -/
def id (S : TensorSignature.{u, v}) : BraidedSubstitution S S where
  obj := FreeBraided.of
  coupon g :=
    cast (congrArg₂ FreeBraided.Hom
      (congrArg FreeBraided.as (projectObj_of (S.src g))).symm
      (congrArg FreeBraided.as (projectObj_of (S.tgt g))).symm)
      (FreeBraided.Hom.coupon g)

/-- The identity braided substitution sends each generating object `a` to `FreeBraided.of a`. -/
@[simp]
theorem id_obj (a : S.Obj) : (id S).obj a = FreeBraided.of a := (rfl)

/-- The identity braided substitution sends each coupon `g` to `FreeBraided.Hom.coupon g`, up to
heterogeneous equality across the endpoint equality for `projectObj`. -/
theorem id_coupon_heq (g : S.Coupon) :
    HEq ((id S).coupon g) (FreeBraided.Hom.coupon g) :=
  cast_heq _ _

/-- Composition of braided substitutions in diagrammatic order: `σ.comp τ` first applies `σ` and
then substitutes along `τ`. -/
def comp (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) :
    BraidedSubstitution S U where
  obj a := τ.toFunctor.obj (σ.obj a)
  coupon g :=
    cast (congrArg₂ FreeBraided.Hom
      (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj (S.src g))).symm
      (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj (S.tgt g))).symm)
      (Hom.subst τ (σ.coupon g))

/-- On generating objects, `σ.comp τ` applies `τ.toFunctor` to the object word `σ.obj a`. -/
@[simp]
theorem comp_obj (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = τ.toFunctor.obj (σ.obj a) := (rfl)

/-- On coupons, `σ.comp τ` substitutes `τ` into `σ.coupon g`, up to heterogeneous equality
across iterated `projectObj`. -/
theorem comp_coupon_heq (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    (g : S.Coupon) :
    HEq ((σ.comp τ).coupon g) (Hom.subst τ (σ.coupon g)) :=
  cast_heq _ _

private theorem hom_comp_heq {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : FreeMonoidalCategory S.Obj}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    {f₁ : FreeBraided.Hom X₁ Y₁} {f₂ : FreeBraided.Hom X₂ Y₂}
    {g₁ : FreeBraided.Hom Y₁ Z₁} {g₂ : FreeBraided.Hom Y₂ Z₂}
    (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) :
    HEq (f₁.comp g₁) (f₂.comp g₂) := by
  subst hX; subst hY; subst hZ
  cases eq_of_heq hf; cases eq_of_heq hg
  rfl

private theorem hom_whiskerLeft_heq {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : FreeMonoidalCategory S.Obj}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    {f₁ : FreeBraided.Hom Y₁ Z₁} {f₂ : FreeBraided.Hom Y₂ Z₂} (hf : HEq f₁ f₂) :
    HEq (f₁.whiskerLeft X₁) (f₂.whiskerLeft X₂) := by
  subst hX; subst hY; subst hZ
  cases eq_of_heq hf
  rfl

private theorem hom_whiskerRight_heq {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : FreeMonoidalCategory S.Obj}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    {f₁ : FreeBraided.Hom X₁ Y₁} {f₂ : FreeBraided.Hom X₂ Y₂} (hf : HEq f₁ f₂) :
    HEq (f₁.whiskerRight Z₁) (f₂.whiskerRight Z₂) := by
  subst hX; subst hY; subst hZ
  cases eq_of_heq hf
  rfl

private theorem hom_tensor_heq
    {W₁ W₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : FreeMonoidalCategory S.Obj}
    (hW : W₁ = W₂) (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    {f₁ : FreeBraided.Hom W₁ Y₁} {f₂ : FreeBraided.Hom W₂ Y₂}
    {g₁ : FreeBraided.Hom X₁ Z₁} {g₂ : FreeBraided.Hom X₂ Z₂}
    (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) :
    HEq (f₁.tensor g₁) (f₂.tensor g₂) := by
  subst hW; subst hX; subst hY; subst hZ
  cases eq_of_heq hf; cases eq_of_heq hg
  rfl

private theorem homMk_heq_of_heq {X₁ X₂ Y₁ Y₂ : S.FreeBraided}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂)
    {f₁ : FreeBraided.Hom X₁.as Y₁.as} {f₂ : FreeBraided.Hom X₂.as Y₂.as}
    (hf : HEq f₁ f₂) :
    HEq (homMk f₁) (homMk f₂) := by
  subst hX; subst hY
  cases eq_of_heq hf
  rfl

private theorem subst_heq_of {σ : BraidedSubstitution S U}
    (φ : FreeMonoidalCategory S.Obj → FreeMonoidalCategory U.Obj)
    (has : ∀ Z, (projectObj σ.obj Z).as = φ Z)
    (F : ∀ {X Y}, FreeBraided.Hom X Y → FreeBraided.Hom (φ X) (φ Y))
    (h_coupon : ∀ g, HEq (σ.coupon g) (F (.coupon g)))
    {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y)
    (h_id : ∀ X, HEq (MonoidalCore.Hom.id (φ X) : FreeBraided.Hom (S := U) _ _)
      (F (.id X)) := by intros; rfl)
    (h_α_hom : ∀ X Y Z,
      HEq (MonoidalCore.Hom.α_hom (φ X) (φ Y) (φ Z) : FreeBraided.Hom (S := U) _ _)
        (F (.α_hom X Y Z)) := by intros; rfl)
    (h_α_inv : ∀ X Y Z,
      HEq (MonoidalCore.Hom.α_inv (φ X) (φ Y) (φ Z) : FreeBraided.Hom (S := U) _ _)
        (F (.α_inv X Y Z)) := by intros; rfl)
    (h_l_hom : ∀ X, HEq (MonoidalCore.Hom.l_hom (φ X) : FreeBraided.Hom (S := U) _ _)
      (F (.l_hom X)) := by intros; rfl)
    (h_l_inv : ∀ X, HEq (MonoidalCore.Hom.l_inv (φ X) : FreeBraided.Hom (S := U) _ _)
      (F (.l_inv X)) := by intros; rfl)
    (h_ρ_hom : ∀ X, HEq (MonoidalCore.Hom.ρ_hom (φ X) : FreeBraided.Hom (S := U) _ _)
      (F (.ρ_hom X)) := by intros; rfl)
    (h_ρ_inv : ∀ X, HEq (MonoidalCore.Hom.ρ_inv (φ X) : FreeBraided.Hom (S := U) _ _)
      (F (.ρ_inv X)) := by intros; rfl)
    (h_β_hom : ∀ X Y, HEq (FreeBraided.Hom.βHom (φ X) (φ Y)) (F (.βHom X Y)) := by intros; rfl)
    (h_β_inv : ∀ X Y, HEq (FreeBraided.Hom.βInv (φ X) (φ Y)) (F (.βInv X Y)) := by intros; rfl)
    (h_comp : ∀ {X Y Z} (f : FreeBraided.Hom X Y) (g : FreeBraided.Hom Y Z),
      HEq ((F f).comp (F g)) (F (f.comp g)) := by intros; rfl)
    (h_whiskerLeft : ∀ X {Y Z} (f : FreeBraided.Hom Y Z),
      HEq ((F f).whiskerLeft (φ X)) (F (f.whiskerLeft X)) := by intros; rfl)
    (h_whiskerRight : ∀ {X Y} (f : FreeBraided.Hom X Y) Z,
      HEq ((F f).whiskerRight (φ Z)) (F (f.whiskerRight Z)) := by intros; rfl)
    (h_tensor : ∀ {W X Y Z} (f : FreeBraided.Hom W Y) (g : FreeBraided.Hom X Z),
      HEq ((F f).tensor (F g)) (F (f.tensor g)) := by intros; rfl) :
    HEq (Hom.subst σ f) (F f) := by
  induction f with
  | id X =>
    rw [Hom.subst_id]
    exact (congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.id Z : FreeBraided.Hom (S := U) _ _))
      (has X)).trans (h_id X)
  | α_hom X Y Z =>
    rw [Hom.subst_α_hom]
    exact (congr_arg_heq
      (fun p : _ × _ × _ ↦ (MonoidalCore.Hom.α_hom p.1 p.2.1 p.2.2 :
        FreeBraided.Hom (S := U) _ _))
      (congrArg₂ Prod.mk (has X) (congrArg₂ Prod.mk (has Y) (has Z)))).trans (h_α_hom X Y Z)
  | α_inv X Y Z =>
    rw [Hom.subst_α_inv]
    exact (congr_arg_heq
      (fun p : _ × _ × _ ↦ (MonoidalCore.Hom.α_inv p.1 p.2.1 p.2.2 :
        FreeBraided.Hom (S := U) _ _))
      (congrArg₂ Prod.mk (has X) (congrArg₂ Prod.mk (has Y) (has Z)))).trans (h_α_inv X Y Z)
  | l_hom X =>
    rw [Hom.subst_l_hom]
    exact (congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_hom Z : FreeBraided.Hom (S := U) _ _))
      (has X)).trans (h_l_hom X)
  | l_inv X =>
    rw [Hom.subst_l_inv]
    exact (congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_inv Z : FreeBraided.Hom (S := U) _ _))
      (has X)).trans (h_l_inv X)
  | ρ_hom X =>
    rw [Hom.subst_ρ_hom]
    exact (congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_hom Z : FreeBraided.Hom (S := U) _ _))
      (has X)).trans (h_ρ_hom X)
  | ρ_inv X =>
    rw [Hom.subst_ρ_inv]
    exact (congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_inv Z : FreeBraided.Hom (S := U) _ _))
      (has X)).trans (h_ρ_inv X)
  | gen g =>
    cases g with
    | β_hom X Y =>
      rw [Hom.subst_β_hom]
      exact (congr_arg_heq (fun p : _ × _ ↦ FreeBraided.Hom.βHom p.1 p.2)
        (congrArg₂ Prod.mk (has X) (has Y))).trans (h_β_hom X Y)
    | β_inv X Y =>
      rw [Hom.subst_β_inv]
      exact (congr_arg_heq (fun p : _ × _ ↦ FreeBraided.Hom.βInv p.1 p.2)
        (congrArg₂ Prod.mk (has X) (has Y))).trans (h_β_inv X Y)
    | coupon g =>
      rw [Hom.subst_coupon]
      exact h_coupon g
  | comp f g hf hg =>
    rw [Hom.subst_comp]
    exact (hom_comp_heq (has _) (has _) (has _) hf hg).trans (h_comp f g)
  | whiskerLeft X f hf =>
    rw [Hom.subst_whiskerLeft]
    exact (hom_whiskerLeft_heq (has X) (has _) (has _) hf).trans (h_whiskerLeft X f)
  | whiskerRight f X hf =>
    rw [Hom.subst_whiskerRight]
    exact (hom_whiskerRight_heq (has _) (has _) (has X) hf).trans (h_whiskerRight f X)
  | tensor f g hf hg =>
    rw [Hom.subst_tensor]
    exact (hom_tensor_heq (has _) (has _) (has _) (has _) hf hg).trans (h_tensor f g)

/-- Substituting along the identity braided substitution leaves every raw braided expression
heterogeneously unchanged. -/
theorem id_subst_heq {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    HEq (Hom.subst (id S) f) f :=
  subst_heq_of _root_.id
    (fun Z ↦ congrArg FreeBraided.as (projectObj_of Z))
    (fun {_ _} f ↦ f) id_coupon_heq f

/-- Substituting along a composite braided substitution `σ.comp τ` agrees heterogeneously with
substituting along `σ` followed by `τ`. -/
theorem comp_subst_heq (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    HEq (Hom.subst (σ.comp τ) f) (Hom.subst τ (Hom.subst σ f)) :=
  subst_heq_of (fun Z ↦ (projectObj τ.obj (projectObj σ.obj Z).as).as)
    (fun Z ↦ by
      rw [show (σ.comp τ).obj = fun a ↦ projectObj τ.obj (σ.obj a).as from
        funext fun a ↦ (comp_obj σ τ a).trans (τ.toFunctor_obj (σ.obj a))]
      exact congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj Z))
    (fun {_ _} f ↦ Hom.subst τ (Hom.subst σ f)) (comp_coupon_heq σ τ) f

/-- The strong braided functor induced by the identity braided substitution is the identity functor
on `S.FreeBraided`. -/
@[simp]
theorem id_toFunctor (S : TensorSignature.{u, v}) :
    (id S).toFunctor = 𝟭 S.FreeBraided := by
  refine Functor.hext (fun X ↦ projectObj_of X.as) fun X Y f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  exact (heq_of_eq ((id S).toFunctor_map_homMk f)).trans
    (homMk_heq_of_heq (projectObj_of X.as) (projectObj_of Y.as) (id_subst_heq f))

/-- The strong braided functor induced by a composite braided substitution is the composite of the
induced strong braided functors. -/
@[simp]
theorem comp_toFunctor (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) :
    (σ.comp τ).toFunctor = σ.toFunctor ⋙ τ.toFunctor := by
  refine Functor.hext (fun X ↦ projectObj_comp σ.obj τ.obj X.as) fun X Y f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  refine (heq_of_eq ((σ.comp τ).toFunctor_map_homMk f)).trans ?_
  refine (homMk_heq_of_heq (projectObj_comp σ.obj τ.obj X.as)
    (projectObj_comp σ.obj τ.obj Y.as) (comp_subst_heq σ τ f)).trans ?_
  exact heq_of_eq ((τ.toFunctor_map_homMk (Hom.subst σ f)).symm.trans
    (congrArg τ.toFunctor.map (σ.toFunctor_map_homMk f).symm))

/-- Precomposing with the identity braided substitution leaves a substitution unchanged. -/
@[simp]
theorem id_comp (σ : BraidedSubstitution S T) : (id S).comp σ = σ := by
  refine BraidedSubstitution.ext (funext fun a ↦ by simp)
    (Function.hfunext rfl fun g _ hg ↦ ?_)
  cases eq_of_heq hg
  refine (comp_coupon_heq (id S) σ g).trans ?_
  exact (FreeBraided.Hom.subst_congr_heq σ (congrArg FreeBraided.as (projectObj_of (S.src g)))
    (congrArg FreeBraided.as (projectObj_of (S.tgt g))) (id_coupon_heq g)).trans
    (heq_of_eq (FreeBraided.Hom.subst_coupon σ g))

/-- Postcomposing with the identity braided substitution leaves a substitution unchanged. -/
@[simp]
theorem comp_id (σ : BraidedSubstitution S T) : σ.comp (id T) = σ := by
  refine BraidedSubstitution.ext (funext fun a ↦ by simp)
    (Function.hfunext rfl fun g _ hg ↦ ?_)
  cases eq_of_heq hg
  exact (comp_coupon_heq σ (id T) g).trans (id_subst_heq (σ.coupon g))

/-- Composition of braided substitutions is associative. -/
@[simp]
theorem comp_assoc (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    (υ : BraidedSubstitution U V) :
    (σ.comp τ).comp υ = σ.comp (τ.comp υ) := by
  refine BraidedSubstitution.ext (funext fun a ↦ by simp)
    (Function.hfunext rfl fun g _ hg ↦ ?_)
  cases eq_of_heq hg
  refine (comp_coupon_heq (σ.comp τ) υ g).trans ?_
  refine (FreeBraided.Hom.subst_congr_heq υ
    (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj (S.src g)))
    (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj (S.tgt g)))
    (comp_coupon_heq σ τ g)).trans ?_
  exact (comp_subst_heq τ υ (σ.coupon g)).symm.trans (comp_coupon_heq σ (τ.comp υ) g).symm

end BraidedSubstitution

end TauCeti.TensorSignature
