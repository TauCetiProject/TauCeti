/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic

/-!
# Morphisms of tensor signatures and coupon invariants

A morphism `TauCeti.TensorSignature.Hom S T` between tensor signatures sends generating objects of
`S` to generating objects of `T` and coupons of `S` to coupons of `T` compatibly with their source
and target tensor words (including empty words and arbitrary parenthesizations). Signature
morphisms compose strictly across arbitrary universes and make `TauCeti.TensorSignature.{u, v}` into
a category whose isomorphisms are characterized by bijectivity on generating objects and coupons.

We also record the coupon-multiset permutation invariant `FreeMonoidal.HomEquiv.coupons_perm` and
additive coupon count `FreeMonoidal.couponCount` on `S.FreeMonoidal`. Because the monoidal-category
axioms only permute coupons via the interchange law and never create or cancel them, no coupon
equals a structural transport `eqToHom` and distinct parallel coupons remain distinct in
`S.FreeMonoidal`.

## Main definitions and results

* `TauCeti.TensorSignature.FreeMonoidal.Hom.coupons` and
  `TauCeti.TensorSignature.FreeMonoidal.HomEquiv.coupons_perm`: the list of coupons occurring in a
  formal morphism is invariant up to list permutation under the monoidal axioms.
* `TauCeti.TensorSignature.FreeMonoidal.couponCount`: the number of coupons in a morphism of
  `S.FreeMonoidal`, additive under composition and tensor product and vanishing on identities and
  structural transports.
* `TauCeti.TensorSignature.FreeMonoidal.coupon_ne_eqToHom` and
  `TauCeti.TensorSignature.FreeMonoidal.coupon_eq_iff`: coupons never collapse to structural
  transports and parallel coupons are distinct whenever their labels are distinct.
* `TauCeti.TensorSignature.Hom`: structure-preserving maps between tensor signatures across
  independent universes, with `Hom.id`, `Hom.comp`, `Category TensorSignature.{u, v}`,
  `Hom.invOfEquiv`, and `Hom.isIso_iff`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
-/

public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

namespace FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

@[ext]
theorem ext {X Y : S.FreeMonoidal} (h : X.as = Y.as) : X = Y := by
  cases X
  cases Y
  congr

@[simp]
theorem mk_as (X : S.FreeMonoidal) : (⟨X.as⟩ : S.FreeMonoidal) = X :=
  rfl

theorem of_as (a : S.Obj) : (of a : S.FreeMonoidal).as = .of a :=
  rfl

theorem tensorUnit_as : (𝟙_ S.FreeMonoidal).as = 𝟙_ (FreeMonoidalCategory S.Obj) :=
  rfl

theorem tensorObj_as (X Y : S.FreeMonoidal) : (X ⊗ Y).as = X.as ⊗ Y.as :=
  rfl

@[simp]
theorem projectObj_as_of {D : Type*} [Category* D] [MonoidalCategory D]
    (f : S.Obj → D) (a : S.Obj) :
    projectObj f (of a : S.FreeMonoidal).as = f a :=
  rfl

@[simp]
theorem projectObj_as_tensorUnit {D : Type*} [Category* D] [MonoidalCategory D]
    (f : S.Obj → D) :
    projectObj f (𝟙_ S.FreeMonoidal).as = 𝟙_ D :=
  rfl

@[simp]
theorem projectObj_as_tensorObj {D : Type*} [Category* D] [MonoidalCategory D]
    (f : S.Obj → D) (X Y : S.FreeMonoidal) :
    projectObj f (X ⊗ Y).as = projectObj f X.as ⊗ projectObj f Y.as :=
  rfl

/-- The inclusion of generating objects into `S.FreeMonoidal` is injective. -/
theorem of_injective : Function.Injective (of (S := S)) := fun _ _ h ↦
  FreeMonoidalCategory.of_injective (congrArg FreeMonoidal.as h)

/-- Unwrapping a formal tensor word evaluated in `T.FreeMonoidal` evaluates the unwrapped
generator words in `FreeMonoidalCategory T.Obj`. -/
theorem projectObj_as {A : Type*} (f : A → T.FreeMonoidal) (X : FreeMonoidalCategory A) :
    (projectObj f X).as = projectObj (fun a ↦ (f a).as) X := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ ihX ihY => exact congrArg₂ FreeMonoidalCategory.tensor ihX ihY

@[simp]
theorem projectObj_of_as (X : FreeMonoidalCategory S.Obj) :
    (projectObj (of (S := S)) X).as = X :=
  (projectObj_as of X).trans (projectObj_of_eq X)

@[simp]
theorem projectObj_of_self (X : S.FreeMonoidal) : projectObj (of (S := S)) X.as = X :=
  ext (projectObj_of_as X.as)

/-- Evaluating in an arbitrary monoidal category `D` after substituting tensor words in
`T.FreeMonoidal` agrees with evaluating directly along the composite generator assignment. -/
theorem projectObj_projectObj_as {A : Type*} {D : Type*} [Category* D] [MonoidalCategory D]
    (fo : T.Obj → D) (g : A → T.FreeMonoidal) (X : FreeMonoidalCategory A) :
    projectObj fo (projectObj g X).as = projectObj (fun a ↦ projectObj fo (g a).as) X := by
  rw [projectObj_as, projectObj_projectObj]

/-- Evaluating `FreeMonoidal.lift fo fc` on an object `X` evaluates its underlying formal tensor
word along `fo`. -/
theorem lift_obj {D : Type*} [Category* D] [MonoidalCategory D] (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))
    (X : S.FreeMonoidal) :
    (lift fo fc).obj X = projectObj fo X.as :=
  rfl

/-! ### Endpoint transport on raw formal morphisms -/

/-- Transport a raw morphism expression along equalities of its source and target tensor words. -/
@[expose] def Hom.cast {X X' Y Y' : FreeMonoidalCategory S.Obj} :
    X = X' → Y = Y' → Hom X Y → Hom X' Y'
  | rfl, rfl, f => f

@[simp]
theorem Hom.cast_rfl {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.cast rfl rfl = f :=
  rfl

theorem Hom.cast_heq {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    (f : Hom (S := S) X Y) : f.cast hX hY ≍ f := by
  subst hX hY
  rfl

@[simp]
theorem Hom.cast_cast {X X' X'' Y Y' Y'' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hX' : X' = X'') (hY : Y = Y') (hY' : Y' = Y'') (f : Hom X Y) :
    (f.cast hX hY).cast hX' hY' = f.cast (hX.trans hX') (hY.trans hY') := by
  subst hX hX' hY hY'
  rfl

@[simp]
theorem Hom.cast_inj {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    {f g : Hom X Y} : f.cast hX hY = g.cast hX hY ↔ f = g := by
  subst hX hY
  rfl

theorem Hom.cast_eq_iff {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    {f : Hom X Y} {g : Hom X' Y'} :
    f.cast hX hY = g ↔ f = g.cast hX.symm hY.symm := by
  subst hX hY
  rfl

theorem Hom.cast_id {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') (h₁ h₂ : X = X') :
    (Hom.id (S := S) X).cast h₁ h₂ = .id X' := by
  subst hX
  rfl

theorem Hom.cast_α_hom {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (h₁ : (X.tensor Y).tensor Z = (X'.tensor Y').tensor Z')
    (h₂ : X.tensor (Y.tensor Z) = X'.tensor (Y'.tensor Z')) :
    (Hom.α_hom (S := S) X Y Z).cast h₁ h₂ = .α_hom X' Y' Z' := by
  subst hX hY hZ
  rfl

theorem Hom.cast_α_inv {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (h₁ : X.tensor (Y.tensor Z) = X'.tensor (Y'.tensor Z'))
    (h₂ : (X.tensor Y).tensor Z = (X'.tensor Y').tensor Z') :
    (Hom.α_inv (S := S) X Y Z).cast h₁ h₂ = .α_inv X' Y' Z' := by
  subst hX hY hZ
  rfl

theorem Hom.cast_l_hom {X X' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (h₁ : unit.tensor X = unit.tensor X') (h₂ : X = X') :
    (Hom.l_hom (S := S) X).cast h₁ h₂ = .l_hom X' := by
  subst hX
  rfl

theorem Hom.cast_l_inv {X X' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (h₁ : X = X') (h₂ : unit.tensor X = unit.tensor X') :
    (Hom.l_inv (S := S) X).cast h₁ h₂ = .l_inv X' := by
  subst hX
  rfl

theorem Hom.cast_ρ_hom {X X' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (h₁ : X.tensor unit = X'.tensor unit) (h₂ : X = X') :
    (Hom.ρ_hom (S := S) X).cast h₁ h₂ = .ρ_hom X' := by
  subst hX
  rfl

theorem Hom.cast_ρ_inv {X X' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (h₁ : X = X') (h₂ : X.tensor unit = X'.tensor unit) :
    (Hom.ρ_inv (S := S) X).cast h₁ h₂ = .ρ_inv X' := by
  subst hX
  rfl

theorem Hom.cast_comp {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : Hom (S := S) X Y) (g : Hom Y Z) :
    (f.cast hX hY).comp (g.cast hY hZ) = (f.comp g).cast hX hZ := by
  subst hX hY hZ
  rfl

theorem Hom.cast_whiskerLeft {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : Hom (S := S) Y Z)
    (h₁ : X.tensor Y = X'.tensor Y') (h₂ : X.tensor Z = X'.tensor Z') :
    (f.cast hY hZ).whiskerLeft X' = (f.whiskerLeft X).cast h₁ h₂ := by
  subst hX hY hZ
  rfl

theorem Hom.cast_whiskerRight {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : Hom (S := S) X Y)
    (h₁ : X.tensor Z = X'.tensor Z') (h₂ : Y.tensor Z = Y'.tensor Z') :
    (f.cast hX hY).whiskerRight Z' = (f.whiskerRight Z).cast h₁ h₂ := by
  subst hX hY hZ
  rfl

theorem Hom.cast_tensor {W W' X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hW : W = W') (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : Hom (S := S) W Y) (g : Hom X Z)
    (h₁ : W.tensor X = W'.tensor X') (h₂ : Y.tensor Z = Y'.tensor Z') :
    (f.cast hW hY).tensor (g.cast hX hZ) = (f.tensor g).cast h₁ h₂ := by
  subst hW hX hY hZ
  rfl

@[simp]
theorem homMk_cast {X Y : FreeMonoidalCategory S.Obj} {X' Y' : S.FreeMonoidal}
    (hX : X = X'.as) (hY : Y = Y'.as) (f : Hom (S := S) X Y) :
    homMk (X := X') (Y := Y') (f.cast hX hY) =
      eqToHom (ext hX.symm) ≫
        homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f ≫ eqToHom (ext hY) := by
  rcases X' with ⟨X'⟩
  rcases Y' with ⟨Y'⟩
  dsimp at hX hY
  subst hX hY
  simp

theorem HomEquiv.cast {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    {f g : Hom (S := S) X Y} (h : HomEquiv f g) :
    HomEquiv (f.cast hX hY) (g.cast hX hY) := by
  subst hX hY
  exact h

/-! ### Coupon permutation invariant and non-collapse -/

/-- The list of coupons occurring in a raw morphism expression, read left-to-right across
compositions and tensor products. -/
def Hom.coupons : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → List S.Coupon
  | _, _, .id _ => []
  | _, _, .α_hom _ _ _ => []
  | _, _, .α_inv _ _ _ => []
  | _, _, .l_hom _ => []
  | _, _, .l_inv _ => []
  | _, _, .ρ_hom _ => []
  | _, _, .ρ_inv _ => []
  | _, _, .coupon g => [g]
  | _, _, .comp f g => f.coupons ++ g.coupons
  | _, _, .whiskerLeft _ f => f.coupons
  | _, _, .whiskerRight f _ => f.coupons
  | _, _, .tensor f g => f.coupons ++ g.coupons

@[simp] theorem Hom.coupons_id (X) : (Hom.id (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_α_hom (X Y Z) : (Hom.α_hom (S := S) X Y Z).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_α_inv (X Y Z) : (Hom.α_inv (S := S) X Y Z).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_l_hom (X) : (Hom.l_hom (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_l_inv (X) : (Hom.l_inv (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_ρ_hom (X) : (Hom.ρ_hom (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_ρ_inv (X) : (Hom.ρ_inv (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_coupon (g : S.Coupon) : (Hom.coupon g).coupons = [g] := (rfl)

@[simp]
theorem Hom.coupons_comp {X Y Z} (f : Hom (S := S) X Y) (g : Hom Y Z) :
    (f.comp g).coupons = f.coupons ++ g.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_whiskerLeft (X) {Y Z} (f : Hom (S := S) Y Z) :
    (f.whiskerLeft X).coupons = f.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_whiskerRight {X Y} (f : Hom (S := S) X Y) (Z) :
    (f.whiskerRight Z).coupons = f.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_tensor {W X Y Z} (f : Hom (S := S) W Y) (g : Hom X Z) :
    (f.tensor g).coupons = f.coupons ++ g.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_cast {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    (f : Hom (S := S) X Y) : (f.cast hX hY).coupons = f.coupons := by
  subst hX hY
  rfl

/-- Equivalent formal morphisms contain the same coupons up to list permutation: the interchange
law permutes coupon lists, and no monoidal axiom creates or erases coupons. -/
theorem HomEquiv.coupons_perm {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) : f.coupons.Perm g.coupons := by
  induction h with
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | whiskerLeft _ _ _ _ ih => exact ih
  | whiskerRight _ _ _ _ ih => exact ih
  | tensor _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | tensorHom_def => exact List.Perm.refl _
  | comp_id => simp
  | id_comp => simp
  | assoc => simp
  | id_tensorHom_id => simp
  | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ =>
    simp only [Hom.coupons_comp, Hom.coupons_tensor, List.append_assoc]
    exact List.Perm.append_left f₁.coupons (List.perm_append_comm_assoc f₂.coupons g₁.coupons _)
  | whiskerLeft_id => simp
  | id_whiskerRight => simp
  | α_hom_inv => simp
  | α_inv_hom => simp
  | associator_naturality => simp [List.append_assoc]
  | ρ_hom_inv => simp
  | ρ_inv_hom => simp
  | ρ_naturality => simp
  | l_hom_inv => simp
  | l_inv_hom => simp
  | l_naturality => simp
  | pentagon => simp
  | triangle => simp

/-- Two formal morphisms representing the same morphism in `S.FreeMonoidal` have permuted coupon
lists. -/
theorem homMk_eq_imp_coupons_perm {X Y : S.FreeMonoidal} {f g : Hom X.as Y.as}
    (h : homMk f = homMk g) : f.coupons.Perm g.coupons :=
  HomEquiv.coupons_perm (Quotient.exact (s := setoidHom X.as Y.as) h)

/-- The number of coupons occurring in a morphism of `S.FreeMonoidal`. -/
def couponCount {X Y : S.FreeMonoidal} (f : X ⟶ Y) : ℕ :=
  Quotient.lift (fun r ↦ r.coupons.length) (fun _ _ h ↦ (HomEquiv.coupons_perm h).length_eq) f

@[simp]
theorem couponCount_homMk {X Y : S.FreeMonoidal} (f : Hom X.as Y.as) :
    couponCount (homMk f) = f.coupons.length :=
  (rfl)

@[simp]
theorem couponCount_id (X : S.FreeMonoidal) : couponCount (𝟙 X) = 0 :=
  (rfl)

@[simp]
theorem couponCount_eqToHom {X Y : S.FreeMonoidal} (h : X = Y) : couponCount (eqToHom h) = 0 := by
  subst h
  rfl

@[simp]
theorem couponCount_coupon (g : S.Coupon) : couponCount (coupon g) = 1 :=
  (rfl)

@[simp]
theorem couponCount_comp {X Y Z : S.FreeMonoidal} (f : X ⟶ Y) (g : Y ⟶ Z) :
    couponCount (f ≫ g) = couponCount f + couponCount g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  exact List.length_append

@[simp]
theorem couponCount_whiskerLeft (X : S.FreeMonoidal) {Y Z : S.FreeMonoidal} (f : Y ⟶ Z) :
    couponCount (X ◁ f) = couponCount f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem couponCount_whiskerRight {X Y : S.FreeMonoidal} (f : X ⟶ Y) (Z : S.FreeMonoidal) :
    couponCount (f ▷ Z) = couponCount f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem couponCount_tensorHom {W X Y Z : S.FreeMonoidal} (f : W ⟶ Y) (g : X ⟶ Z) :
    couponCount (f ⊗ₘ g) = couponCount f + couponCount g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  exact List.length_append

/-- A coupon in `S.FreeMonoidal` is never equal to an object-equality transport `eqToHom`,
in particular an endomorphism coupon is never equal to the identity morphism. -/
theorem coupon_ne_eqToHom (g : S.Coupon) (h : (⟨S.src g⟩ : S.FreeMonoidal) = ⟨S.tgt g⟩) :
    coupon g ≠ eqToHom h := by
  intro hg
  have hc := congrArg couponCount hg
  simp at hc

/-- Two coupons with matching source and target words determine equal morphisms in `S.FreeMonoidal`
(up to the canonical endpoint transports) if and only if they are the same coupon. -/
theorem coupon_eq_iff {g₁ g₂ : S.Coupon} (hsrc : S.src g₁ = S.src g₂)
    (htgt : S.tgt g₁ = S.tgt g₂) :
    coupon g₁ = eqToHom (congrArg FreeMonoidal.mk hsrc) ≫ coupon g₂ ≫
        eqToHom (congrArg FreeMonoidal.mk htgt.symm) ↔ g₁ = g₂ := by
  constructor
  · intro h
    have hcast : homMk (X := ⟨S.src g₁⟩) (Y := ⟨S.tgt g₁⟩) (Hom.coupon g₁) =
        homMk (X := ⟨S.src g₁⟩) (Y := ⟨S.tgt g₁⟩) ((Hom.coupon g₂).cast hsrc.symm htgt.symm) := by
      rw [homMk_coupon, homMk_cast, homMk_coupon, h]
    have hperm := homMk_eq_imp_coupons_perm hcast
    simpa using hperm.mem_iff.mp (List.mem_singleton_self g₁)
  · rintro rfl
    simp

end FreeMonoidal

/-! ### Morphisms of tensor signatures -/

/-- A morphism of tensor signatures sends generating objects to generating objects and coupons to
coupons compatibly with their formal source and target tensor words. The two signatures may live in
independent universes. -/
@[ext]
structure Hom (S : TensorSignature.{u₁, v₁}) (T : TensorSignature.{u₂, v₂}) where
  /-- The map on generating objects. -/
  obj : S.Obj → T.Obj
  /-- The map on coupons. -/
  coupon : S.Coupon → T.Coupon
  /-- Compatibility with coupon source words. -/
  src_coupon : ∀ g : S.Coupon, T.src (coupon g) = projectObj (.of ∘ obj) (S.src g) := by
    cat_disch
  /-- Compatibility with coupon target words. -/
  tgt_coupon : ∀ g : S.Coupon, T.tgt (coupon g) = projectObj (.of ∘ obj) (S.tgt g) := by
    cat_disch

namespace Hom

/-- The identity morphism of a tensor signature. -/
@[expose] def id (S : TensorSignature.{u, v}) : Hom S S where
  obj := _root_.id
  coupon := _root_.id
  src_coupon g := (projectObj_of_eq (S.src g)).symm
  tgt_coupon g := (projectObj_of_eq (S.tgt g)).symm

@[simp] theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) : (id S).obj a = a := (rfl)
@[simp] theorem id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) : (id S).coupon g = g := (rfl)

/-- Diagrammatic composition of tensor-signature morphisms across arbitrary universes. -/
@[expose] def comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) : Hom S U where
  obj := ψ.obj ∘ φ.obj
  coupon := ψ.coupon ∘ φ.coupon
  src_coupon g := by
    rw [Function.comp_apply, ψ.src_coupon, φ.src_coupon, projectObj_map_of]
    rfl
  tgt_coupon g := by
    rw [Function.comp_apply, ψ.tgt_coupon, φ.tgt_coupon, projectObj_map_of]
    rfl

@[simp]
theorem comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (a : S.Obj) :
    (φ.comp ψ).obj a = ψ.obj (φ.obj a) :=
  (rfl)

@[simp]
theorem comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (g : S.Coupon) :
    (φ.comp ψ).coupon g = ψ.coupon (φ.coupon g) :=
  (rfl)

@[simp]
theorem id_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T) :
    (id S).comp φ = φ := by
  ext <;> rfl

@[simp]
theorem comp_id {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T) :
    φ.comp (id T) = φ := by
  ext <;> rfl

theorem comp_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u', v'}}
    (φ : Hom S T) (ψ : Hom T U) (θ : Hom U V) :
    (φ.comp ψ).comp θ = φ.comp (ψ.comp θ) := by
  ext <;> rfl

/-- Construct the inverse morphism of a tensor-signature morphism whose object and coupon maps are
given by equivalences. -/
def invOfEquiv {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T)
    (eo : S.Obj ≃ T.Obj) (ec : S.Coupon ≃ T.Coupon)
    (ho : ∀ a, eo a = φ.obj a) (hc : ∀ g, ec g = φ.coupon g) : Hom T S where
  obj := eo.symm
  coupon := ec.symm
  src_coupon h := by
    have hφ : φ.coupon (ec.symm h) = h := (hc (ec.symm h)).symm.trans (ec.apply_symm_apply h)
    calc S.src (ec.symm h)
        = projectObj FreeMonoidalCategory.of (S.src (ec.symm h)) := (projectObj_of_eq _).symm
      _ = projectObj ((.of ∘ eo.symm) ∘ φ.obj) (S.src (ec.symm h)) :=
          projectObj_congr (fun a ↦ congrArg FreeMonoidalCategory.of
            ((eo.symm_apply_apply a).symm.trans (congrArg eo.symm (ho a)))) _
      _ = projectObj (.of ∘ eo.symm) (T.src (φ.coupon (ec.symm h))) := by
          rw [φ.src_coupon, projectObj_map_of]
      _ = projectObj (.of ∘ eo.symm) (T.src h) := by rw [hφ]
  tgt_coupon h := by
    have hφ : φ.coupon (ec.symm h) = h := (hc (ec.symm h)).symm.trans (ec.apply_symm_apply h)
    calc S.tgt (ec.symm h)
        = projectObj FreeMonoidalCategory.of (S.tgt (ec.symm h)) := (projectObj_of_eq _).symm
      _ = projectObj ((.of ∘ eo.symm) ∘ φ.obj) (S.tgt (ec.symm h)) :=
          projectObj_congr (fun a ↦ congrArg FreeMonoidalCategory.of
            ((eo.symm_apply_apply a).symm.trans (congrArg eo.symm (ho a)))) _
      _ = projectObj (.of ∘ eo.symm) (T.tgt (φ.coupon (ec.symm h))) := by
          rw [φ.tgt_coupon, projectObj_map_of]
      _ = projectObj (.of ∘ eo.symm) (T.tgt h) := by rw [hφ]

@[simp]
theorem invOfEquiv_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T)
    (eo : S.Obj ≃ T.Obj) (ec : S.Coupon ≃ T.Coupon)
    (ho : ∀ a, eo a = φ.obj a) (hc : ∀ g, ec g = φ.coupon g) (b : T.Obj) :
    (φ.invOfEquiv eo ec ho hc).obj b = eo.symm b :=
  (rfl)

@[simp]
theorem invOfEquiv_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (eo : S.Obj ≃ T.Obj) (ec : S.Coupon ≃ T.Coupon)
    (ho : ∀ a, eo a = φ.obj a) (hc : ∀ g, ec g = φ.coupon g) (h : T.Coupon) :
    (φ.invOfEquiv eo ec ho hc).coupon h = ec.symm h :=
  (rfl)

@[simp]
theorem comp_invOfEquiv {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T)
    (eo : S.Obj ≃ T.Obj) (ec : S.Coupon ≃ T.Coupon)
    (ho : ∀ a, eo a = φ.obj a) (hc : ∀ g, ec g = φ.coupon g) :
    φ.comp (φ.invOfEquiv eo ec ho hc) = id S := by
  ext a
  · exact (congrArg eo.symm (ho a).symm).trans (eo.symm_apply_apply a)
  · exact (congrArg ec.symm (hc a).symm).trans (ec.symm_apply_apply a)

@[simp]
theorem invOfEquiv_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} (φ : Hom S T)
    (eo : S.Obj ≃ T.Obj) (ec : S.Coupon ≃ T.Coupon)
    (ho : ∀ a, eo a = φ.obj a) (hc : ∀ g, ec g = φ.coupon g) :
    (φ.invOfEquiv eo ec ho hc).comp φ = id T := by
  ext b
  · exact (ho (eo.symm b)).symm.trans (eo.apply_symm_apply b)
  · exact (hc (ec.symm b)).symm.trans (ec.apply_symm_apply b)

end Hom

instance : Category TensorSignature.{u, v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

namespace Hom

@[simp]
theorem category_id_obj (S : TensorSignature.{u, v}) (a : S.Obj) :
    (𝟙 S : S ⟶ S).obj a = a :=
  (rfl)

@[simp]
theorem category_id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    (𝟙 S : S ⟶ S).coupon g = g :=
  (rfl)

@[simp]
theorem category_comp_obj {S T U : TensorSignature.{u, v}} (φ : S ⟶ T) (ψ : T ⟶ U) (a : S.Obj) :
    (φ ≫ ψ).obj a = ψ.obj (φ.obj a) :=
  (rfl)

@[simp]
theorem category_comp_coupon {S T U : TensorSignature.{u, v}} (φ : S ⟶ T) (ψ : T ⟶ U)
    (g : S.Coupon) : (φ ≫ ψ).coupon g = ψ.coupon (φ.coupon g) :=
  (rfl)

/-- A morphism in `TensorSignature.{u, v}` is an isomorphism if and only if it is bijective on both
generating objects and coupons. -/
theorem isIso_iff {S T : TensorSignature.{u, v}} (φ : S ⟶ T) :
    IsIso φ ↔ Function.Bijective φ.obj ∧ Function.Bijective φ.coupon := by
  constructor
  · intro h
    refine ⟨⟨fun a₁ a₂ ha ↦ ?_, fun b ↦ ⟨(inv φ).obj b, ?_⟩⟩,
      ⟨fun g₁ g₂ hg ↦ ?_, fun c ↦ ⟨(inv φ).coupon c, ?_⟩⟩⟩
    · have h₁ := congrArg (fun θ : S ⟶ S ↦ θ.obj a₁) (IsIso.hom_inv_id φ)
      have h₂ := congrArg (fun θ : S ⟶ S ↦ θ.obj a₂) (IsIso.hom_inv_id φ)
      exact h₁.symm.trans ((congrArg (inv φ).obj ha).trans h₂)
    · exact congrArg (fun θ : T ⟶ T ↦ θ.obj b) (IsIso.inv_hom_id φ)
    · have h₁ := congrArg (fun θ : S ⟶ S ↦ θ.coupon g₁) (IsIso.hom_inv_id φ)
      have h₂ := congrArg (fun θ : S ⟶ S ↦ θ.coupon g₂) (IsIso.hom_inv_id φ)
      exact h₁.symm.trans ((congrArg (inv φ).coupon hg).trans h₂)
    · exact congrArg (fun θ : T ⟶ T ↦ θ.coupon c) (IsIso.inv_hom_id φ)
  · rintro ⟨ho, hc⟩
    let eo := Equiv.ofBijective φ.obj ho
    let ec := Equiv.ofBijective φ.coupon hc
    exact ⟨φ.invOfEquiv eo ec (fun _ ↦ rfl) (fun _ ↦ rfl),
      φ.comp_invOfEquiv eo ec (fun _ ↦ rfl) (fun _ ↦ rfl),
      φ.invOfEquiv_comp eo ec (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

end Hom

end TauCeti.TensorSignature
