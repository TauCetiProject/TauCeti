/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic

/-!
# Morphisms of tensor signatures

A morphism `TauCeti.TensorSignature.Hom S T` between tensor signatures sends generating objects of
`S` to generating objects of `T` and coupons of `S` to coupons of `T` compatibly with their source
and target tensor words (including empty words and arbitrary parenthesizations). Signature
morphisms compose strictly across arbitrary universes and make `TauCeti.TensorSignature.{u, v}` into
a category whose isomorphisms are characterized by bijectivity on generating objects and coupons.

## Main definitions and results

* `TauCeti.TensorSignature.Hom`: structure-preserving maps between tensor signatures across
  independent universes, with `Hom.id`, `Hom.comp`, `Hom.invOfEquiv`,
  `Category TensorSignature.{u, v}`, `TensorSignature.hom_ext`, and `Hom.isIso_iff`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
-/

public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

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
def id (S : TensorSignature.{u, v}) : Hom S S where
  obj := _root_.id
  coupon := _root_.id
  src_coupon g := (projectObj_of (S.src g)).symm
  tgt_coupon g := (projectObj_of (S.tgt g)).symm

@[simp] theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) : (id S).obj a = a := (rfl)
@[simp] theorem id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) : (id S).coupon g = g := (rfl)

/-- Diagrammatic composition of tensor-signature morphisms across arbitrary universes. -/
def comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) : Hom S U where
  obj := ψ.obj ∘ φ.obj
  coupon := ψ.coupon ∘ φ.coupon
  src_coupon g := by
    rw [Function.comp_apply, ψ.src_coupon, φ.src_coupon, projectObj_projectObj_of_comp]
    rfl
  tgt_coupon g := by
    rw [Function.comp_apply, ψ.tgt_coupon, φ.tgt_coupon, projectObj_projectObj_of_comp]
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
        = projectObj FreeMonoidalCategory.of (S.src (ec.symm h)) := (projectObj_of _).symm
      _ = projectObj ((.of ∘ eo.symm) ∘ φ.obj) (S.src (ec.symm h)) :=
          projectObj_congr (fun a ↦ congrArg FreeMonoidalCategory.of
            ((eo.symm_apply_apply a).symm.trans (congrArg eo.symm (ho a)))) _
      _ = projectObj (.of ∘ eo.symm) (T.src (φ.coupon (ec.symm h))) := by
          rw [φ.src_coupon, projectObj_projectObj_of_comp]
      _ = projectObj (.of ∘ eo.symm) (T.src h) := by rw [hφ]
  tgt_coupon h := by
    have hφ : φ.coupon (ec.symm h) = h := (hc (ec.symm h)).symm.trans (ec.apply_symm_apply h)
    calc S.tgt (ec.symm h)
        = projectObj FreeMonoidalCategory.of (S.tgt (ec.symm h)) := (projectObj_of _).symm
      _ = projectObj ((.of ∘ eo.symm) ∘ φ.obj) (S.tgt (ec.symm h)) :=
          projectObj_congr (fun a ↦ congrArg FreeMonoidalCategory.of
            ((eo.symm_apply_apply a).symm.trans (congrArg eo.symm (ho a)))) _
      _ = projectObj (.of ∘ eo.symm) (T.tgt (φ.coupon (ec.symm h))) := by
          rw [φ.tgt_coupon, projectObj_projectObj_of_comp]
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

/-- Extensionality for morphisms in `TensorSignature.{u, v}`: two morphisms are equal if they agree
on generating objects and coupons. -/
@[ext]
theorem hom_ext {S T : TensorSignature.{u, v}} {φ ψ : S ⟶ T}
    (hobj : ∀ a, φ.obj a = ψ.obj a) (hcoupon : ∀ g, φ.coupon g = ψ.coupon g) : φ = ψ :=
  Hom.ext (funext hobj) (funext hcoupon)

/-- The categorical identity on `S` is `Hom.id S`. -/
theorem id_eq (S : TensorSignature.{u, v}) : (𝟙 S : S ⟶ S) = Hom.id S :=
  (rfl)

/-- Categorical composition in `TensorSignature.{u, v}` is `Hom.comp`. -/
theorem comp_eq {S T U : TensorSignature.{u, v}} (φ : S ⟶ T) (ψ : T ⟶ U) :
    φ ≫ ψ = φ.comp ψ :=
  (rfl)

@[simp]
theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) : (𝟙 S : S ⟶ S).obj a = a :=
  Hom.id_obj S a

@[simp]
theorem id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) : (𝟙 S : S ⟶ S).coupon g = g :=
  Hom.id_coupon S g

@[simp]
theorem comp_obj {S T U : TensorSignature.{u, v}} (φ : S ⟶ T) (ψ : T ⟶ U) (a : S.Obj) :
    (φ ≫ ψ).obj a = ψ.obj (φ.obj a) :=
  Hom.comp_obj φ ψ a

@[simp]
theorem comp_coupon {S T U : TensorSignature.{u, v}} (φ : S ⟶ T) (ψ : T ⟶ U) (g : S.Coupon) :
    (φ ≫ ψ).coupon g = ψ.coupon (φ.coupon g) :=
  Hom.comp_coupon φ ψ g

namespace Hom

/-- A morphism in `TensorSignature.{u, v}` is an isomorphism if and only if it is bijective on both
generating objects and coupons. -/
theorem isIso_iff {S T : TensorSignature.{u, v}} (φ : S ⟶ T) :
    IsIso φ ↔ Function.Bijective φ.obj ∧ Function.Bijective φ.coupon := by
  constructor
  · intro h
    refine ⟨Function.bijective_iff_has_inverse.mpr ⟨(inv φ).obj,
        fun a ↦ congrArg (fun θ : S ⟶ S ↦ θ.obj a) (IsIso.hom_inv_id φ),
        fun b ↦ congrArg (fun θ : T ⟶ T ↦ θ.obj b) (IsIso.inv_hom_id φ)⟩,
      Function.bijective_iff_has_inverse.mpr ⟨(inv φ).coupon,
        fun g ↦ congrArg (fun θ : S ⟶ S ↦ θ.coupon g) (IsIso.hom_inv_id φ),
        fun c ↦ congrArg (fun θ : T ⟶ T ↦ θ.coupon c) (IsIso.inv_hom_id φ)⟩⟩
  · rintro ⟨ho, hc⟩
    let eo := Equiv.ofBijective φ.obj ho
    let ec := Equiv.ofBijective φ.coupon hc
    exact ⟨φ.invOfEquiv eo ec (fun _ ↦ rfl) (fun _ ↦ rfl),
      φ.comp_invOfEquiv eo ec (fun _ ↦ rfl) (fun _ ↦ rfl),
      φ.invOfEquiv_comp eo ec (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

end Hom

end TauCeti.TensorSignature
