/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic

/-!
# Substitution for free braided monoidal categories

A `TauCeti.TensorSignature.FreeBraided.Substitution S T` replaces generating objects of `S` by
formal tensor words in `T.FreeBraided` and coupons of `S` by raw braided morphism expressions in
`T` with the resulting substituted boundaries.

`Substitution.subst` performs this substitution directly on raw braided expressions before
quotienting by the braided monoidal axioms, commuting with identities, associators, unitors,
braidings, inverse braidings, composition, tensor products, and whiskering.
`Substitution.toFunctor` is the induced strong braided functor `S.FreeBraided ⥤ T.FreeBraided`,
and `Substitution.toFunctor_map_homMk` identifies its action with raw substitution, giving
soundness for braided monoidal equivalence (`Substitution.homMk_subst_eq_of_eq`).

Substitutions carry an identity `Substitution.id` and associative composition `Substitution.comp`
with two-sided unit laws (`Substitution.id_comp`, `Substitution.comp_id`,
`Substitution.comp_assoc`), and `Substitution.toFunctor` is strictly functorial with respect to
both (`Substitution.toFunctor_id`, `Substitution.toFunctor_comp`).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. 102 (1993), 20–78.
* P. Selinger, *A survey of graphical languages for monoidal categories*, Lecture Notes in Physics
  813 (2011), §3.3.
-/

public section

universe u v u' v' u'' v'' u₃ v₃

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature.FreeBraided

section ProjectObj

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}}

/-- Interpreting a tensor word along the object generators of `S.FreeBraided` recovers that word
as an object of `S.FreeBraided`. -/
theorem projectObj_of (X : FreeMonoidalCategory S.Obj) :
    projectObj (FreeBraided.of (S := S)) X = ofWord X := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
      simp only [projectObj, hX, hY]
      rfl

/-- Word-level form of `projectObj_of`. -/
theorem projectObj_of_word (X : FreeMonoidalCategory S.Obj) :
    (projectObj (FreeBraided.of (S := S)) X).word = X :=
  congrArg FreeBraided.word (projectObj_of X)

/-- Iterated `projectObj` along two object assignments agrees with `projectObj` along their
composite assignment. -/
theorem projectObj_projectObj (f : S.Obj → T.FreeBraided) (g : T.Obj → U.FreeBraided)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ projectObj g (f a).word) X = projectObj g (projectObj f X).word := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
      simp only [projectObj, word_tensor, hX, hY]

/-- Word-level form of `projectObj_projectObj`. -/
theorem projectObj_projectObj_word (f : S.Obj → T.FreeBraided) (g : T.Obj → U.FreeBraided)
    (X : FreeMonoidalCategory S.Obj) :
    (projectObj (fun a ↦ projectObj g (f a).word) X).word =
      (projectObj g (projectObj f X).word).word :=
  congrArg FreeBraided.word (projectObj_projectObj f g X)

end ProjectObj

/-- A typed braided substitution between tensor signatures: generating objects of `S` are replaced
by objects of `T.FreeBraided` (formal tensor words in `T.Obj`), and coupons of `S` are replaced
by raw braided morphism expressions in `T` with the substituted source and target words. -/
@[ext]
structure Substitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The tensor word in `T.FreeBraided` replacing each object generator of `S`. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided morphism expression in `T` replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon,
    RawHom (projectObj obj (S.src g)).word (projectObj obj (S.tgt g)).word

namespace Substitution

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}} {W : TensorSignature.{u₃, v₃}}

/-- Heterogeneous extensionality for braided substitutions whose object maps agree pointwise. -/
theorem ext_heq {σ τ : Substitution S T}
    (hobj : ∀ a, σ.obj a = τ.obj a)
    (hcoupon : ∀ g, HEq (σ.coupon g) (τ.coupon g)) : σ = τ := by
  cases σ with | mk o₁ c₁ =>
  cases τ with | mk o₂ c₂ =>
  have ho : o₁ = o₂ := funext hobj
  subst ho
  congr
  funext g
  exact eq_of_heq (hcoupon g)

/-- Substitute formal tensor words for object generators and raw braided expressions for coupons
in a raw braided morphism expression, preserving identities, associators, unitors, braidings,
inverse braidings, composition, tensor products, and whiskering. -/
def subst (σ : Substitution S T) : ∀ {X Y}, RawHom X Y →
    RawHom (projectObj σ.obj X).word (projectObj σ.obj Y).word
  | _, _, .id X => FreeMonoidal.Hom.id (S := T.braidedSignature) (projectObj σ.obj X).word
  | _, _, .α_hom X Y Z => FreeMonoidal.Hom.α_hom (S := T.braidedSignature)
      (projectObj σ.obj X).word (projectObj σ.obj Y).word (projectObj σ.obj Z).word
  | _, _, .α_inv X Y Z => FreeMonoidal.Hom.α_inv (S := T.braidedSignature)
      (projectObj σ.obj X).word (projectObj σ.obj Y).word (projectObj σ.obj Z).word
  | _, _, .l_hom X => FreeMonoidal.Hom.l_hom (S := T.braidedSignature) (projectObj σ.obj X).word
  | _, _, .l_inv X => FreeMonoidal.Hom.l_inv (S := T.braidedSignature) (projectObj σ.obj X).word
  | _, _, .ρ_hom X => FreeMonoidal.Hom.ρ_hom (S := T.braidedSignature) (projectObj σ.obj X).word
  | _, _, .ρ_inv X => FreeMonoidal.Hom.ρ_inv (S := T.braidedSignature) (projectObj σ.obj X).word
  | _, _, .coupon (BraidedCoupon.coupon g) => σ.coupon g
  | _, _, .coupon (BraidedCoupon.β_hom X Y) =>
      RawHom.braidingHom (projectObj σ.obj X).word (projectObj σ.obj Y).word
  | _, _, .coupon (BraidedCoupon.β_inv X Y) =>
      RawHom.braidingInv (projectObj σ.obj X).word (projectObj σ.obj Y).word
  | _, _, .comp f g => (σ.subst f).comp (σ.subst g)
  | _, _, .whiskerLeft X f =>
      FreeMonoidal.Hom.whiskerLeft (S := T.braidedSignature) (projectObj σ.obj X).word (σ.subst f)
  | _, _, .whiskerRight f X =>
      FreeMonoidal.Hom.whiskerRight (S := T.braidedSignature) (σ.subst f) (projectObj σ.obj X).word
  | _, _, .tensor f g => (σ.subst f).tensor (σ.subst g)

@[simp]
theorem subst_id (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.id (S := S.braidedSignature) X) =
      FreeMonoidal.Hom.id (S := T.braidedSignature) (projectObj σ.obj X).word := by rfl

@[simp]
theorem subst_ofCoupon (σ : Substitution S T) (g : S.Coupon) :
    σ.subst (RawHom.ofCoupon g) = σ.coupon g := by rfl

@[simp]
theorem subst_braidingHom (σ : Substitution S T) (X Y : FreeMonoidalCategory S.Obj) :
    σ.subst (RawHom.braidingHom X Y) =
      RawHom.braidingHom (projectObj σ.obj X).word (projectObj σ.obj Y).word := by rfl

@[simp]
theorem subst_braidingInv (σ : Substitution S T) (X Y : FreeMonoidalCategory S.Obj) :
    σ.subst (RawHom.braidingInv X Y) =
      RawHom.braidingInv (projectObj σ.obj X).word (projectObj σ.obj Y).word := by rfl

@[simp]
theorem subst_comp (σ : Substitution S T) {X Y Z : FreeMonoidalCategory S.Obj}
    (f : RawHom X Y) (g : RawHom Y Z) :
    σ.subst (f.comp g) = (σ.subst f).comp (σ.subst g) := by rfl

@[simp]
theorem subst_tensor (σ : Substitution S T) {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory S.Obj}
    (f : RawHom X₁ Y₁) (g : RawHom X₂ Y₂) :
    σ.subst (f.tensor g) = (σ.subst f).tensor (σ.subst g) := by rfl

@[simp]
theorem subst_whiskerLeft (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj)
    {Y Z : FreeMonoidalCategory S.Obj} (f : RawHom Y Z) :
    σ.subst (FreeMonoidal.Hom.whiskerLeft (S := S.braidedSignature) X f) =
      FreeMonoidal.Hom.whiskerLeft (S := T.braidedSignature)
        (projectObj σ.obj X).word (σ.subst f) := by rfl

@[simp]
theorem subst_whiskerRight (σ : Substitution S T) {Y Z : FreeMonoidalCategory S.Obj}
    (f : RawHom Y Z) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.whiskerRight (S := S.braidedSignature) f X) =
      FreeMonoidal.Hom.whiskerRight (S := T.braidedSignature)
        (σ.subst f) (projectObj σ.obj X).word := by rfl

@[simp]
theorem subst_α_hom (σ : Substitution S T) (X Y Z : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.α_hom (S := S.braidedSignature) X Y Z) =
      FreeMonoidal.Hom.α_hom (S := T.braidedSignature) (projectObj σ.obj X).word
        (projectObj σ.obj Y).word (projectObj σ.obj Z).word := by rfl

@[simp]
theorem subst_α_inv (σ : Substitution S T) (X Y Z : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.α_inv (S := S.braidedSignature) X Y Z) =
      FreeMonoidal.Hom.α_inv (S := T.braidedSignature) (projectObj σ.obj X).word
        (projectObj σ.obj Y).word (projectObj σ.obj Z).word := by rfl

@[simp]
theorem subst_l_hom (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.l_hom (S := S.braidedSignature) X) =
      FreeMonoidal.Hom.l_hom (S := T.braidedSignature) (projectObj σ.obj X).word := by rfl

@[simp]
theorem subst_l_inv (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.l_inv (S := S.braidedSignature) X) =
      FreeMonoidal.Hom.l_inv (S := T.braidedSignature) (projectObj σ.obj X).word := by rfl

@[simp]
theorem subst_ρ_hom (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.ρ_hom (S := S.braidedSignature) X) =
      FreeMonoidal.Hom.ρ_hom (S := T.braidedSignature) (projectObj σ.obj X).word := by rfl

@[simp]
theorem subst_ρ_inv (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    σ.subst (FreeMonoidal.Hom.ρ_inv (S := S.braidedSignature) X) =
      FreeMonoidal.Hom.ρ_inv (S := T.braidedSignature) (projectObj σ.obj X).word := by rfl

variable (σ : Substitution S T)

/-- The strong braided functor induced by a braided substitution, obtained via the universal
property `FreeBraided.lift`. -/
-- Exposed so that object expressions `σ.toFunctor.obj X` reduce to `projectObj σ.obj X.word`.
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := by
  dsimp only [toFunctor]
  infer_instance

instance : σ.toFunctor.Braided := by
  dsimp only [toFunctor]
  infer_instance

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeBraided) : Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeBraided) : Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeBraided) : σ.toFunctor.obj X = projectObj σ.obj X.word := rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

private theorem toFunctor_map_homMk_tensor {W X Y Z : FreeMonoidalCategory S.Obj}
    (f : RawHom W Y) (g : RawHom X Z)
    (hf : σ.toFunctor.map (homMk (S := S) (X := ofWord W) (Y := ofWord Y) f) =
      homMk (S := T) (X := projectObj σ.obj W) (Y := projectObj σ.obj Y) (σ.subst f))
    (hg : σ.toFunctor.map (homMk (S := S) (X := ofWord X) (Y := ofWord Z) g) =
      homMk (S := T) (X := projectObj σ.obj X) (Y := projectObj σ.obj Z) (σ.subst g)) :
    σ.toFunctor.map (homMk (S := S) (X := ofWord (W.tensor X)) (Y := ofWord (Y.tensor Z))
        (f.tensor g)) =
      homMk (S := T) (X := projectObj σ.obj (W.tensor X)) (Y := projectObj σ.obj (Y.tensor Z))
        ((σ.subst f).tensor (σ.subst g)) := by
  have hl := homMk_tensor (S := S) (X₁ := ofWord W) (Y₁ := ofWord Y)
    (X₂ := ofWord X) (Y₂ := ofWord Z) f g
  have hr := homMk_tensor (S := T) (X₁ := projectObj σ.obj W) (Y₁ := projectObj σ.obj Y)
    (X₂ := projectObj σ.obj X) (Y₂ := projectObj σ.obj Z) (σ.subst f) (σ.subst g)
  exact (congrArg σ.toFunctor.map hl).trans
    ((FreeBraided.lift_map_tensorHom σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))
      (homMk (S := S) (X := ofWord W) (Y := ofWord Y) f)
      (homMk (S := S) (X := ofWord X) (Y := ofWord Z) g)).trans
      ((congrArg₂ (· ⊗ₘ ·) hf hg).trans hr.symm))

/-- Applying the induced braided functor to the equivalence class of a raw braided expression
yields the equivalence class of the substituted raw expression. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : RawHom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (S := S) (X := ofWord X) (Y := ofWord Y) f) =
      FreeBraided.homMk (S := T) (X := projectObj σ.obj X) (Y := projectObj σ.obj Y)
        (σ.subst f) := by
  let fc := fun g ↦ FreeBraided.homMk (σ.coupon g)
  match f with
  | .id X => exact σ.toFunctor.map_id (ofWord X)
  | .α_hom X Y Z => exact lift_map_associator_hom σ.obj fc (ofWord X) (ofWord Y) (ofWord Z)
  | .α_inv X Y Z => exact lift_map_associator_inv σ.obj fc (ofWord X) (ofWord Y) (ofWord Z)
  | .l_hom X => exact lift_map_leftUnitor_hom σ.obj fc (ofWord X)
  | .l_inv X => exact lift_map_leftUnitor_inv σ.obj fc (ofWord X)
  | .ρ_hom X => exact lift_map_rightUnitor_hom σ.obj fc (ofWord X)
  | .ρ_inv X => exact lift_map_rightUnitor_inv σ.obj fc (ofWord X)
  | .coupon (BraidedCoupon.coupon g) => exact lift_map_coupon σ.obj fc g
  | .coupon (BraidedCoupon.β_hom X Y) => exact lift_map_braiding_hom σ.obj fc (ofWord X) (ofWord Y)
  | .coupon (BraidedCoupon.β_inv X Y) => exact lift_map_braiding_inv σ.obj fc (ofWord X) (ofWord Y)
  | .comp f g =>
      exact (σ.toFunctor.map_comp (homMk (S := S) (X := ofWord _) (Y := ofWord _) f)
        (homMk (S := S) (X := ofWord _) (Y := ofWord _) g)).trans
        (congrArg₂ (· ≫ ·) (toFunctor_map_homMk f) (toFunctor_map_homMk g))
  | .whiskerLeft X f =>
      exact (lift_map_whiskerLeft σ.obj fc (ofWord X)
        (homMk (S := S) (X := ofWord _) (Y := ofWord _) f)).trans
        (congrArg (projectObj σ.obj X ◁ ·) (toFunctor_map_homMk f))
  | .whiskerRight f X =>
      exact (lift_map_whiskerRight σ.obj fc
        (homMk (S := S) (X := ofWord _) (Y := ofWord _) f) (ofWord X)).trans
        (congrArg (· ▷ projectObj σ.obj X) (toFunctor_map_homMk f))
  | @FreeMonoidal.Hom.tensor S.braidedSignature _ _ _ _ f g =>
      exact toFunctor_map_homMk_tensor σ f g (toFunctor_map_homMk f) (toFunctor_map_homMk g)

/-- Raw braided substitution respects equality in `S.FreeBraided` without requiring any equations
between the replacing coupons. -/
theorem homMk_subst_eq_of_eq {X Y : FreeMonoidalCategory S.Obj} {f g : RawHom X Y}
    (h : homMk (X := ofWord X) (Y := ofWord Y) f = homMk (X := ofWord X) (Y := ofWord Y) g) :
    homMk (X := projectObj σ.obj X) (Y := projectObj σ.obj Y) (σ.subst f) =
      homMk (X := projectObj σ.obj X) (Y := projectObj σ.obj Y) (σ.subst g) :=
  (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg σ.toFunctor.map h).trans (σ.toFunctor_map_homMk g))

/-! ### Identity and composition of braided substitutions -/

private def castRawHom {X Y X' Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (f : RawHom X Y) : RawHom X' Y' :=
  hX ▸ hY ▸ f

private theorem castRawHom_heq {X Y X' Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (f : RawHom X Y) :
    HEq (castRawHom hX hY f) f := by
  subst hX; subst hY; rfl

private theorem subst_castRawHom_heq
    {X Y X' Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y') (f : RawHom X Y) :
    HEq (σ.subst (castRawHom hX hY f)) (σ.subst f) := by
  subst hX; subst hY; rfl

private theorem rawHom_unary_heq {p q : FreeMonoidalCategory T.Obj → FreeMonoidalCategory T.Obj}
    (F : ∀ X, RawHom (p X) (q X)) {X X' : FreeMonoidalCategory T.Obj} (hX : X = X') :
    HEq (F X) (F X') := by
  subst hX; rfl

private theorem rawHom_binary_heq
    {p q : FreeMonoidalCategory T.Obj → FreeMonoidalCategory T.Obj → FreeMonoidalCategory T.Obj}
    (F : ∀ X Y, RawHom (p X Y) (q X Y))
    {X X' Y Y' : FreeMonoidalCategory T.Obj} (hX : X = X') (hY : Y = Y') :
    HEq (F X Y) (F X' Y') := by
  subst hX; subst hY; rfl

private theorem rawHom_ternary_heq
    {p q : FreeMonoidalCategory T.Obj → FreeMonoidalCategory T.Obj →
      FreeMonoidalCategory T.Obj → FreeMonoidalCategory T.Obj}
    (F : ∀ X Y Z, RawHom (p X Y Z) (q X Y Z))
    {X X' Y Y' Z Z' : FreeMonoidalCategory T.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    HEq (F X Y Z) (F X' Y' Z') := by
  subst hX; subst hY; subst hZ; rfl

private theorem rawHom_comp_heq {A B C A' B' C' : FreeMonoidalCategory T.Obj}
    (hA : A = A') (hB : B = B') (hC : C = C')
    {f : RawHom A B} {g : RawHom B C} {f' : RawHom A' B'} {g' : RawHom B' C'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (f.comp g) (f'.comp g') := by
  subst hA; subst hB; subst hC; cases hf; cases hg; rfl

private theorem rawHom_tensor_heq {A₁ B₁ A₂ B₂ A₁' B₁' A₂' B₂' : FreeMonoidalCategory T.Obj}
    (hA₁ : A₁ = A₁') (hB₁ : B₁ = B₁') (hA₂ : A₂ = A₂') (hB₂ : B₂ = B₂')
    {f : RawHom A₁ B₁} {g : RawHom A₂ B₂} {f' : RawHom A₁' B₁'} {g' : RawHom A₂' B₂'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (f.tensor g) (f'.tensor g') := by
  subst hA₁; subst hB₁; subst hA₂; subst hB₂; cases hf; cases hg; rfl

private theorem rawHom_whiskerLeft_heq {X Y Z X' Y' Z' : FreeMonoidalCategory T.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : RawHom Y Z} {f' : RawHom Y' Z'} (hf : HEq f f') :
    HEq (FreeMonoidal.Hom.whiskerLeft (S := T.braidedSignature) X f)
      (FreeMonoidal.Hom.whiskerLeft (S := T.braidedSignature) X' f') := by
  subst hX; subst hY; subst hZ; cases hf; rfl

private theorem rawHom_whiskerRight_heq {X Y Z X' Y' Z' : FreeMonoidalCategory T.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : RawHom X Y} {f' : RawHom X' Y'} (hf : HEq f f') :
    HEq (FreeMonoidal.Hom.whiskerRight (S := T.braidedSignature) f Z)
      (FreeMonoidal.Hom.whiskerRight (S := T.braidedSignature) f' Z') := by
  subst hX; subst hY; subst hZ; cases hf; rfl

/-- The identity braided substitution on `S`, sending each generating object and coupon to
itself. -/
def id (S : TensorSignature.{u, v}) : Substitution S S where
  obj := FreeBraided.of
  coupon g :=
    castRawHom (projectObj_of_word (S.src g)).symm (projectObj_of_word (S.tgt g)).symm
      (RawHom.ofCoupon g)

@[simp]
theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) :
    (Substitution.id S).obj a = FreeBraided.of a := by rfl

/-- Composition of braided substitutions: `σ.comp τ` first applies `σ` and then substitutes `τ`
into the resulting object words and raw coupon expressions. -/
def comp (τ : Substitution T U) : Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).word
  coupon g :=
    castRawHom (projectObj_projectObj_word σ.obj τ.obj (S.src g)).symm
      (projectObj_projectObj_word σ.obj τ.obj (S.tgt g)).symm
      (τ.subst (σ.coupon g))

@[simp]
theorem comp_obj (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).word := by rfl

/-- Substituting the identity substitution into any raw braided expression returns that expression
(heterogeneously, along the endpoint identification `projectObj_of_word`). -/
theorem subst_id_heq {X Y : FreeMonoidalCategory S.Obj} (f : RawHom X Y) :
    HEq ((Substitution.id S).subst f) f := by
  let h := projectObj_of_word (S := S)
  match f with
  | .id X => exact rawHom_unary_heq (T := S) (FreeMonoidal.Hom.id (S := S.braidedSignature)) (h X)
  | .α_hom X Y Z =>
      exact rawHom_ternary_heq (T := S) (FreeMonoidal.Hom.α_hom (S := S.braidedSignature))
        (h X) (h Y) (h Z)
  | .α_inv X Y Z =>
      exact rawHom_ternary_heq (T := S) (FreeMonoidal.Hom.α_inv (S := S.braidedSignature))
        (h X) (h Y) (h Z)
  | .l_hom X =>
      exact rawHom_unary_heq (T := S) (FreeMonoidal.Hom.l_hom (S := S.braidedSignature)) (h X)
  | .l_inv X =>
      exact rawHom_unary_heq (T := S) (FreeMonoidal.Hom.l_inv (S := S.braidedSignature)) (h X)
  | .ρ_hom X =>
      dsimp only [subst, id]
      exact rawHom_unary_heq (T := S) (FreeMonoidal.Hom.ρ_hom (S := S.braidedSignature)) (h X)
  | .ρ_inv X =>
      dsimp only [subst, id]
      exact rawHom_unary_heq (T := S) (FreeMonoidal.Hom.ρ_inv (S := S.braidedSignature)) (h X)
  | .coupon (BraidedCoupon.coupon _) => exact castRawHom_heq _ _ _
  | .coupon (BraidedCoupon.β_hom X Y) =>
      exact rawHom_binary_heq (T := S) (RawHom.braidingHom (S := S)) (h X) (h Y)
  | .coupon (BraidedCoupon.β_inv X Y) =>
      exact rawHom_binary_heq (T := S) (RawHom.braidingInv (S := S)) (h X) (h Y)
  | .comp f g =>
      exact rawHom_comp_heq (T := S) (h _) (h _) (h _) (subst_id_heq f) (subst_id_heq g)
  | .whiskerLeft X f =>
      dsimp only [subst, id]
      exact rawHom_whiskerLeft_heq (T := S) (h X) (h _) (h _) (subst_id_heq f)
  | .whiskerRight f X =>
      dsimp only [subst, id]
      exact rawHom_whiskerRight_heq (T := S) (h _) (h _) (h X) (subst_id_heq f)
  | .tensor f g =>
      exact rawHom_tensor_heq (T := S) (h _) (h _) (h _) (h _) (subst_id_heq f) (subst_id_heq g)

/-- Substituting a composite braided substitution `σ.comp τ` into a raw braided expression agrees
with substituting `σ` and then `τ` (heterogeneously, along `projectObj_projectObj_word`). -/
theorem subst_comp_heq (τ : Substitution T U) {X Y : FreeMonoidalCategory S.Obj} (f : RawHom X Y) :
    HEq ((σ.comp τ).subst f) (τ.subst (σ.subst f)) := by
  let h := projectObj_projectObj_word σ.obj τ.obj
  match f with
  | .id X => exact rawHom_unary_heq (T := U) (FreeMonoidal.Hom.id (S := U.braidedSignature)) (h X)
  | .α_hom X Y Z =>
      exact rawHom_ternary_heq (T := U) (FreeMonoidal.Hom.α_hom (S := U.braidedSignature))
        (h X) (h Y) (h Z)
  | .α_inv X Y Z =>
      exact rawHom_ternary_heq (T := U) (FreeMonoidal.Hom.α_inv (S := U.braidedSignature))
        (h X) (h Y) (h Z)
  | .l_hom X =>
      exact rawHom_unary_heq (T := U) (FreeMonoidal.Hom.l_hom (S := U.braidedSignature)) (h X)
  | .l_inv X =>
      exact rawHom_unary_heq (T := U) (FreeMonoidal.Hom.l_inv (S := U.braidedSignature)) (h X)
  | .ρ_hom X =>
      exact rawHom_unary_heq (T := U) (FreeMonoidal.Hom.ρ_hom (S := U.braidedSignature)) (h X)
  | .ρ_inv X =>
      exact rawHom_unary_heq (T := U) (FreeMonoidal.Hom.ρ_inv (S := U.braidedSignature)) (h X)
  | .coupon (BraidedCoupon.coupon _) => exact castRawHom_heq _ _ _
  | .coupon (BraidedCoupon.β_hom X Y) =>
      exact rawHom_binary_heq (T := U) (RawHom.braidingHom (S := U)) (h X) (h Y)
  | .coupon (BraidedCoupon.β_inv X Y) =>
      exact rawHom_binary_heq (T := U) (RawHom.braidingInv (S := U)) (h X) (h Y)
  | .comp f g =>
      exact rawHom_comp_heq (T := U) (h _) (h _) (h _) (subst_comp_heq τ f) (subst_comp_heq τ g)
  | .whiskerLeft X f =>
      exact rawHom_whiskerLeft_heq (T := U) (h X) (h _) (h _) (subst_comp_heq τ f)
  | .whiskerRight f X =>
      exact rawHom_whiskerRight_heq (T := U) (h _) (h _) (h X) (subst_comp_heq τ f)
  | .tensor f g =>
      exact rawHom_tensor_heq (T := U) (h _) (h _) (h _) (h _)
        (subst_comp_heq τ f) (subst_comp_heq τ g)

/-- Left unit law for braided substitution composition. -/
@[simp]
theorem id_comp : (Substitution.id S).comp σ = σ :=
  ext_heq (fun _ ↦ rfl) fun g ↦
    (castRawHom_heq _ _ _).trans
      ((subst_castRawHom_heq σ _ _ (RawHom.ofCoupon g)).trans
        (heq_of_eq (subst_ofCoupon σ g)))

/-- Right unit law for braided substitution composition. -/
@[simp]
theorem comp_id : σ.comp (Substitution.id T) = σ :=
  ext_heq (fun a ↦ projectObj_of (σ.obj a).word) fun g ↦
    (castRawHom_heq _ _ _).trans (subst_id_heq (σ.coupon g))

/-- Associativity of braided substitution composition. -/
theorem comp_assoc (τ : Substitution T U) (υ : Substitution U W) :
    (σ.comp τ).comp υ = σ.comp (τ.comp υ) :=
  ext_heq (fun a ↦ (projectObj_projectObj τ.obj υ.obj (σ.obj a).word).symm) fun g ↦
    (castRawHom_heq _ _ _).trans
      ((subst_castRawHom_heq υ _ _ _).trans
        ((subst_comp_heq τ υ (σ.coupon g)).symm.trans (castRawHom_heq _ _ _).symm))

private theorem homMk_eq_of_heq {X Y X' Y' : S.FreeBraided} (hX : X = X') (hY : Y = Y')
    {f : RawHom X.word Y.word} {g : RawHom X'.word Y'.word} (hfg : HEq f g) :
    homMk (S := S) f = eqToHom hX ≫ homMk (S := S) g ≫ eqToHom hY.symm := by
  subst hX; subst hY; cases hfg; simp

/-- The strong braided functor induced by the identity substitution is the identity functor. -/
@[simp]
theorem toFunctor_id (S : TensorSignature.{u, v}) :
    (Substitution.id S).toFunctor = 𝟭 S.FreeBraided := by
  refine CategoryTheory.Functor.ext (fun X ↦ projectObj_of X.word) fun X Y f ↦ ?_
  obtain ⟨⟨X⟩⟩ := X
  obtain ⟨⟨Y⟩⟩ := Y
  obtain ⟨r, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
  obtain ⟨r, rfl⟩ := Quotient.exists_rep r
  let r' : RawHom (S := S) X Y := r
  have hX : projectObj (Substitution.id S).obj X = ofWord (S := S) X := by
    dsimp only [id]; exact projectObj_of (S := S) X
  have hY : projectObj (Substitution.id S).obj Y = ofWord (S := S) Y := by
    dsimp only [id]; exact projectObj_of (S := S) Y
  dsimp only [Functor.id_obj, Functor.id_map]
  exact (toFunctor_map_homMk (Substitution.id S) r').trans
    (homMk_eq_of_heq (S := S) hX hY (subst_id_heq r'))

/-- The strong braided functor induced by a composite substitution is the composite of the
induced functors. -/
@[simp]
theorem toFunctor_comp (τ : Substitution T U) :
    (σ.comp τ).toFunctor = σ.toFunctor ⋙ τ.toFunctor := by
  refine CategoryTheory.Functor.ext (fun X ↦ projectObj_projectObj σ.obj τ.obj X.word)
    fun X Y f ↦ ?_
  obtain ⟨⟨X⟩⟩ := X
  obtain ⟨⟨Y⟩⟩ := Y
  obtain ⟨r, rfl⟩ := (Presented.quotientFunctor (BraidedRel S)).map_surjective f
  obtain ⟨r, rfl⟩ := Quotient.exists_rep r
  let r' : RawHom (S := S) X Y := r
  have hl := toFunctor_map_homMk (σ.comp τ) r'
  have hr : (σ.toFunctor ⋙ τ.toFunctor).map
        (homMk (S := S) (X := ofWord X) (Y := ofWord Y) r') =
      homMk (S := U) (X := projectObj τ.obj (projectObj σ.obj X).word)
        (Y := projectObj τ.obj (projectObj σ.obj Y).word) (τ.subst (σ.subst r')) := by
    dsimp only [Functor.comp_map]
    rw [toFunctor_map_homMk σ r']
    exact toFunctor_map_homMk τ (σ.subst r')
  exact hl.trans ((homMk_eq_of_heq (S := U) (projectObj_projectObj σ.obj τ.obj X)
    (projectObj_projectObj σ.obj τ.obj Y) (subst_comp_heq σ τ r')).trans
    (congrArg (fun m ↦ eqToHom _ ≫ m ≫ eqToHom _) hr.symm))

end Substitution

end TauCeti.TensorSignature.FreeBraided
