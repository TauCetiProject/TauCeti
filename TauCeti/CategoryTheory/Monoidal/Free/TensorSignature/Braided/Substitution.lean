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
words in `T` and coupons of `S` by raw braided morphism expressions in `T` with the resulting
boundaries. In particular, an object generator may be replaced by the tensor unit or by a
multi-letter tensor word, while each coupon retains its full ordered source and target words.

`FreeBraided.Hom.subst` performs this replacement on raw syntax before quotienting by the braided
monoidal axioms, and `FreeBraided.HomEquiv.subst` shows that it respects those axioms. The strong
braided functor `BraidedSubstitution.toFunctor` is the universal lift of the substitution, and
`BraidedSubstitution.toFunctor_map_homMk` identifies its action on classes with raw substitution.

Substitutions form a strict algebra under `BraidedSubstitution.id` and `BraidedSubstitution.comp`,
satisfying two-sided unit laws (`id_comp`, `comp_id`) and associativity (`comp_assoc`), and
`toFunctor` preserves identities and composition strictly (`toFunctor_id`, `toFunctor_comp`).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
-/

public section

universe u v u' v' u'' v'' u₃ v₃

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures. Object generators are replaced by
formal tensor expressions, and coupons by raw braided expressions with the substituted source and
target. The object and coupon types of the two signatures need not have the same universes. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The tensor expression replacing each object generator. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided expression replacing each coupon. -/
  coupon : ∀ g : S.Coupon, FreeBraided.Hom
    (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}} {V : TensorSignature.{u₃, v₃}}

namespace FreeBraided

/-- Interpreting a tensor word by the generating objects `FreeBraided.of` recovers the word. -/
@[simp]
theorem projectObj_of (X : S.FreeBraided) :
    projectObj (of (S := S)) X.as = X := by
  rcases X with ⟨X⟩
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ (· ⊗ ·) hX hY

/-- Iterated `projectObj` along an object substitution into `FreeBraided` agrees with interpreting
each generating object by the composite map. -/
@[simp]
theorem projectObj_comp {D : Type u''} [Category.{v''} D] [MonoidalCategory D]
    (f : S.Obj → T.FreeBraided) (g : T.Obj → D) (X : S.FreeBraided) :
    projectObj g (projectObj f X.as).as = projectObj (fun a ↦ projectObj g (f a).as) X.as := by
  rcases X with ⟨X⟩
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ (· ⊗ ·) hX hY

/-- Transport a raw braided morphism along endpoint equalities of formal tensor words. -/
def Hom.cast {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory S.Obj}
    (f : Hom X₁ Y₁) (hX : X₁ = X₂) (hY : Y₁ = Y₂) : Hom X₂ Y₂ :=
  hX ▸ hY ▸ f

@[simp]
theorem Hom.cast_rfl {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.cast rfl rfl = f := by rfl

@[simp]
theorem Hom.cast_cast {X₁ Y₁ X₂ Y₂ X₃ Y₃ : FreeMonoidalCategory S.Obj}
    (f : Hom X₁ Y₁) (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hX' : X₂ = X₃) (hY' : Y₂ = Y₃) :
    (f.cast hX hY).cast hX' hY' = f.cast (hX.trans hX') (hY.trans hY') := by
  cases hX; cases hY; cases hX'; cases hY'; rfl

theorem Hom.cast_heq {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory S.Obj}
    (f : Hom X₁ Y₁) (hX : X₁ = X₂) (hY : Y₁ = Y₂) :
    HEq (f.cast hX hY) f := by
  cases hX; cases hY; rfl

/-- Substitute tensor expressions for object generators and raw braided expressions for coupons.
The endpoints are interpreted by the native tensor-word interpreter `projectObj`. -/
def Hom.subst (σ : BraidedSubstitution S T) : ∀ {X Y}, Hom X Y →
    Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => .id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .l_hom X => .l_hom (projectObj σ.obj X).as
  | _, _, .l_inv X => .l_inv (projectObj σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (projectObj σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (projectObj σ.obj X).as
  | _, _, .β_hom X Y => .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .β_inv X Y => .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp]
theorem Hom.subst_id (σ : BraidedSubstitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_hom X Y).subst σ =
      .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

@[simp]
theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_inv X Y).subst σ =
      .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

@[simp]
theorem Hom.subst_cast (σ : BraidedSubstitution S T) {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory S.Obj}
    (f : Hom X₁ Y₁) (hX : X₁ = X₂) (hY : Y₁ = Y₂) :
    (f.cast hX hY).subst σ =
      (f.subst σ).cast (congrArg (fun W ↦ (projectObj σ.obj W).as) hX)
        (congrArg (fun W ↦ (projectObj σ.obj W).as) hY) := by
  cases hX; cases hY; rfl

theorem Hom.subst_cast_heq (σ : BraidedSubstitution S T) {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory S.Obj}
    (f : Hom X₁ Y₁) (hX : X₁ = X₂) (hY : Y₁ = Y₂) :
    HEq ((f.cast hX hY).subst σ) (f.subst σ) := by
  cases hX; cases hY; rfl

private theorem Hom.heq_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FreeMonoidalCategory S.Obj}
    {f₁ : Hom X₁ Y₁} {g₁ : Hom Y₁ Z₁} {f₂ : Hom X₂ Y₂} {g₂ : Hom Y₂ Z₂}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂) (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) :
    HEq (f₁.comp g₁) (f₂.comp g₂) := by
  cases hX; cases hY; cases hZ; cases hf; cases hg; rfl

private theorem Hom.heq_whiskerLeft {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FreeMonoidalCategory S.Obj}
    {f₁ : Hom Y₁ Z₁} {f₂ : Hom Y₂ Z₂}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂) (hf : HEq f₁ f₂) :
    HEq (f₁.whiskerLeft X₁) (f₂.whiskerLeft X₂) := by
  cases hX; cases hY; cases hZ; cases hf; rfl

private theorem Hom.heq_whiskerRight {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FreeMonoidalCategory S.Obj}
    {f₁ : Hom X₁ Y₁} {f₂ : Hom X₂ Y₂}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂) (hf : HEq f₁ f₂) :
    HEq (f₁.whiskerRight Z₁) (f₂.whiskerRight Z₂) := by
  cases hX; cases hY; cases hZ; cases hf; rfl

private theorem Hom.heq_tensor {W₁ X₁ Y₁ Z₁ W₂ X₂ Y₂ Z₂ : FreeMonoidalCategory S.Obj}
    {f₁ : Hom W₁ Y₁} {g₁ : Hom X₁ Z₁} {f₂ : Hom W₂ Y₂} {g₂ : Hom X₂ Z₂}
    (hW : W₁ = W₂) (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) :
    HEq (f₁.tensor g₁) (f₂.tensor g₂) := by
  cases hW; cases hX; cases hY; cases hZ; cases hf; cases hg; rfl

private theorem homMk_heq {X₁ Y₁ X₂ Y₂ : S.FreeBraided}
    {f₁ : Hom X₁.as Y₁.as} {f₂ : Hom X₂.as Y₂.as}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hf : HEq f₁ f₂) :
    HEq (homMk (X := X₁) (Y := Y₁) f₁) (homMk (X := X₂) (Y := Y₂) f₂) := by
  cases hX; cases hY; cases hf; rfl

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

/-- The identity braided substitution on a tensor signature `S`. Exposed so that `(id S).obj`
reduces in the dependent type of `(id S).coupon`. -/
@[expose] def id (S : TensorSignature.{u, v}) : BraidedSubstitution S S where
  obj := FreeBraided.of
  coupon g :=
    (Hom.coupon g).cast
      (congrArg FreeBraided.as (projectObj_of ⟨S.src g⟩)).symm
      (congrArg FreeBraided.as (projectObj_of ⟨S.tgt g⟩)).symm

@[simp]
theorem id_obj (a : S.Obj) : (id S).obj a = FreeBraided.of a := rfl

theorem id_coupon (g : S.Coupon) :
    (id S).coupon g =
      (Hom.coupon g).cast
        (congrArg FreeBraided.as (projectObj_of ⟨S.src g⟩)).symm
        (congrArg FreeBraided.as (projectObj_of ⟨S.tgt g⟩)).symm := rfl

/-- Composition of braided substitutions: apply `σ` and then substitute `τ` into the resulting
object words and raw braided expressions. Exposed so that `(σ.comp τ).obj` reduces in the
dependent type of `(σ.comp τ).coupon`. -/
@[expose] def comp (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) :
    BraidedSubstitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g :=
    ((σ.coupon g).subst τ).cast
      (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨S.src g⟩))
      (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨S.tgt g⟩))

@[simp]
theorem comp_obj (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as := rfl

theorem comp_coupon (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g =
      ((σ.coupon g).subst τ).cast
        (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨S.src g⟩))
        (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨S.tgt g⟩)) := rfl

variable (σ : BraidedSubstitution S T)

/-- The strong braided functor induced by a raw braided substitution. It is the universal lift of
the specified object expressions and the equivalence classes of the replacing coupons. Its object
action is exposed so that raw substituted expressions have the required endpoint types in the
representative computation rules. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal

instance : σ.toFunctor.Braided := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeBraided) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeBraided) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeBraided) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := by rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

/-- Interpreting a raw braided expression by the induced functor is the equivalence class of its
substitution. This is also the representative computation rule for the descended operation. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | β_hom X Y => exact lift_map_braiding_hom _ _ ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact lift_map_braiding_inv _ _ ⟨X⟩ ⟨Y⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg =>
    exact (liftMap_comp _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
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

/-- Applying the identity substitution to a raw braided morphism returns a heterogeneously equal
morphism. -/
theorem Hom.subst_id_heq {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    HEq (f.subst (BraidedSubstitution.id S)) f := by
  let h := fun W : FreeMonoidalCategory S.Obj ↦ congrArg FreeBraided.as (projectObj_of ⟨W⟩)
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z =>
    exact congr_arg_heq (fun p : (_ × _) × _ ↦ Hom.α_hom p.1.1 p.1.2 p.2)
      (congrArg₂ Prod.mk (congrArg₂ Prod.mk (h X) (h Y)) (h Z))
  | α_inv X Y Z =>
    exact congr_arg_heq (fun p : (_ × _) × _ ↦ Hom.α_inv p.1.1 p.1.2 p.2)
      (congrArg₂ Prod.mk (congrArg₂ Prod.mk (h X) (h Y)) (h Z))
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | β_hom X Y =>
    exact congr_arg_heq (fun p : _ × _ ↦ Hom.β_hom p.1 p.2) (congrArg₂ Prod.mk (h X) (h Y))
  | β_inv X Y =>
    exact congr_arg_heq (fun p : _ × _ ↦ Hom.β_inv p.1 p.2) (congrArg₂ Prod.mk (h X) (h Y))
  | coupon g => exact Hom.cast_heq _ _ _
  | @comp X Y Z _ _ hf hg => exact Hom.heq_comp (h X) (h Y) (h Z) hf hg
  | @whiskerLeft X Y₁ Y₂ _ hf => exact Hom.heq_whiskerLeft (h X) (h Y₁) (h Y₂) hf
  | @whiskerRight X₁ X₂ _ Y hf => exact Hom.heq_whiskerRight (h X₁) (h X₂) (h Y) hf
  | @tensor W X Y Z _ _ hf hg => exact Hom.heq_tensor (h W) (h X) (h Y) (h Z) hf hg

/-- Applying the identity substitution to a raw braided morphism equals transporting the morphism
along the word identity `projectObj_of`. -/
theorem Hom.subst_id_eq_cast {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.subst (BraidedSubstitution.id S) =
      f.cast (congrArg FreeBraided.as (projectObj_of ⟨X⟩)).symm
        (congrArg FreeBraided.as (projectObj_of ⟨Y⟩)).symm :=
  eq_of_heq ((Hom.subst_id_heq f).trans (Hom.cast_heq f _ _).symm)

/-- Substituting along `σ.comp τ` agrees heterogeneously with substituting along `σ` and then
along `τ`. -/
theorem Hom.subst_comp_heq (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    HEq (f.subst (σ.comp τ)) ((f.subst σ).subst τ) := by
  let h := fun W : FreeMonoidalCategory S.Obj ↦
    (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨W⟩)).symm
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z =>
    exact congr_arg_heq (fun p : (_ × _) × _ ↦ Hom.α_hom p.1.1 p.1.2 p.2)
      (congrArg₂ Prod.mk (congrArg₂ Prod.mk (h X) (h Y)) (h Z))
  | α_inv X Y Z =>
    exact congr_arg_heq (fun p : (_ × _) × _ ↦ Hom.α_inv p.1.1 p.1.2 p.2)
      (congrArg₂ Prod.mk (congrArg₂ Prod.mk (h X) (h Y)) (h Z))
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | β_hom X Y =>
    exact congr_arg_heq (fun p : _ × _ ↦ Hom.β_hom p.1 p.2) (congrArg₂ Prod.mk (h X) (h Y))
  | β_inv X Y =>
    exact congr_arg_heq (fun p : _ × _ ↦ Hom.β_inv p.1 p.2) (congrArg₂ Prod.mk (h X) (h Y))
  | coupon g => exact Hom.cast_heq _ _ _
  | @comp X Y Z _ _ hf hg => exact Hom.heq_comp (h X) (h Y) (h Z) hf hg
  | @whiskerLeft X Y₁ Y₂ _ hf => exact Hom.heq_whiskerLeft (h X) (h Y₁) (h Y₂) hf
  | @whiskerRight X₁ X₂ _ Y hf => exact Hom.heq_whiskerRight (h X₁) (h X₂) (h Y) hf
  | @tensor W X Y Z _ _ hf hg => exact Hom.heq_tensor (h W) (h X) (h Y) (h Z) hf hg

/-- Substituting along `σ.comp τ` equals transporting iterated substitution along
`projectObj_comp`. -/
theorem Hom.subst_comp_eq_cast (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.subst (σ.comp τ) =
      ((f.subst σ).subst τ).cast
        (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨X⟩))
        (congrArg FreeBraided.as (projectObj_comp σ.obj τ.obj ⟨Y⟩)) :=
  eq_of_heq ((Hom.subst_comp_heq σ τ f).trans (Hom.cast_heq _ _ _).symm)

/-- Braided substitution preserves the relation generated by the braided monoidal axioms. No
equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

@[simp]
theorem id_comp (σ : BraidedSubstitution S T) : (id S).comp σ = σ := by
  ext a
  · rfl
  · refine Function.hfunext rfl fun g₁ g₂ hg ↦ ?_
    cases hg
    exact (Hom.cast_heq _ _ _).trans (Hom.subst_cast_heq σ (Hom.coupon g₁) _ _)

@[simp]
theorem comp_id (σ : BraidedSubstitution S T) : σ.comp (id T) = σ := by
  ext a
  · exact projectObj_of (σ.obj a)
  · refine Function.hfunext rfl fun g₁ g₂ hg ↦ ?_
    cases hg
    exact (Hom.cast_heq _ _ _).trans (Hom.subst_id_heq (σ.coupon g₁))

theorem comp_assoc (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U)
    (υ : BraidedSubstitution U V) :
    (σ.comp τ).comp υ = σ.comp (τ.comp υ) := by
  ext a
  · exact projectObj_comp τ.obj υ.obj (σ.obj a)
  · refine Function.hfunext rfl fun g₁ g₂ hg ↦ ?_
    cases hg
    have h₁ : HEq (((σ.comp τ).comp υ).coupon g₁) (((σ.coupon g₁).subst τ).subst υ) :=
      (Hom.cast_heq _ _ _).trans (Hom.subst_cast_heq υ ((σ.coupon g₁).subst τ) _ _)
    have h₂ : HEq ((σ.comp (τ.comp υ)).coupon g₁) (((σ.coupon g₁).subst τ).subst υ) :=
      (Hom.cast_heq _ _ _).trans (Hom.subst_comp_heq τ υ (σ.coupon g₁))
    exact h₁.trans h₂.symm

/-- The functor induced by the identity substitution is the identity functor. -/
theorem toFunctor_id (S : TensorSignature.{u, v}) :
    (id S).toFunctor = 𝟭 S.FreeBraided := by
  refine Functor.hext (fun X ↦ projectObj_of X) fun X Y f ↦ ?_
  induction f using Quotient.inductionOn with | _ p
  exact (heq_of_eq ((id S).toFunctor_map_homMk p)).trans
    (homMk_heq (projectObj_of X) (projectObj_of Y) (Hom.subst_id_heq p))

/-- The functor induced by a composite substitution is the composite of the induced functors. -/
theorem toFunctor_comp (σ : BraidedSubstitution S T) (τ : BraidedSubstitution T U) :
    (σ.comp τ).toFunctor = σ.toFunctor ⋙ τ.toFunctor := by
  refine Functor.hext (fun X ↦ (projectObj_comp σ.obj τ.obj X).symm) fun X Y f ↦ ?_
  induction f using Quotient.inductionOn with | _ p
  have h₁ : (σ.comp τ).toFunctor.map (homMk p) = homMk (p.subst (σ.comp τ)) :=
    (σ.comp τ).toFunctor_map_homMk p
  have h₂ : (σ.toFunctor ⋙ τ.toFunctor).map (homMk p) = homMk ((p.subst σ).subst τ) :=
    (congrArg τ.toFunctor.map (σ.toFunctor_map_homMk p)).trans (τ.toFunctor_map_homMk _)
  exact (heq_of_eq h₁).trans
    ((homMk_heq (projectObj_comp σ.obj τ.obj X).symm (projectObj_comp σ.obj τ.obj Y).symm
      (Hom.subst_comp_heq σ τ p)).trans (heq_of_eq h₂).symm)

end BraidedSubstitution

end TauCeti.TensorSignature
